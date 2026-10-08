from commit_owned_v1 import *
import re

post_fixed()
r=load(RUN/'delivery-receipt-v1.json')
assert r['verdict'] in ['accepted','accepted-with-explicit-delta'] and r['inputs_unchanged']
assert not r['required_blocking_repairs'] and r['report_sha256']==sha(RUN/'delivery-review-v1.md')
inputs=load(RUN/'delivery-review-inputs-v1.json')['rows']
assert r['fixed_input_count']==len(inputs) and all(sha(x['path'])==x['sha256'] for x in inputs)
changed=subprocess.check_output(['git','diff','HEAD','--name-only','-z']).decode('utf8').split('\0')
others=subprocess.check_output(['git','ls-files','--others','--exclude-standard','-z']).decode('utf8').split('\0')
assert all(p.startswith(RUN.relative_to(ROOT).as_posix()+'/') for p in changed+others if p)
stage_owned()
command=['git','-c','core.whitespace=blank-at-eol,blank-at-eof,space-before-tab,cr-at-eol','diff','--cached','--check','HEAD']
code=gate('delivery-evidence-full-diff-v1',*command,required=False);assert code in [0,2]
bad=set(re.findall(r'^([^\r\n]+?):\d+: (?:trailing whitespace|new blank line at EOF|space before tab)',
    (RUN/'delivery-evidence-full-diff-v1.log').read_text(encoding='utf8'),re.M))
bound={x['path']:x['sha256'] for x in inputs};exceptions=[]
for rel in sorted(bad):
    p=ROOT/rel
    assert rel.startswith(RUN.relative_to(ROOT).as_posix()+'/') and p.suffix=='.log'
    assert bound[p.as_posix()]==sha(p)
    exceptions.append(dict(path=rel,sha256=sha(p)))
if code:
    assert bad
    exceptions.append(dict(path=(RUN/'delivery-evidence-full-diff-v1.log').relative_to(ROOT).as_posix(),sha256=sha(RUN/'delivery-evidence-full-diff-v1.log')))
write(RUN/'delivery-evidence-raw-exceptions-v1.json',dict(exceptions=exceptions,
    full_unexcluded_actual_exit=code,source_or_executable_exceptions=0))
stage_owned();gate('delivery-evidence-scoped-diff-v1',*command,'--','.',*[':(exclude)'+x['path'] for x in exceptions])
receipt=commit_owned('Record reviewed bounded FTL draft delivery and official attachment evidence','final-evidence-commit-v1')
head=receipt['actual_head'];d=load(RUN/'actual-draft-delivery-v1.json');number=d['PR']

def remote(label,command):
    log=ROOT/'tmp'/('online-ftl-obstruction-'+label+'.log');assert not log.exists()
    tick=time.monotonic()
    with log.open('wb') as stream:
        child=subprocess.run(command,cwd=str(ROOT),stdout=stream,stderr=subprocess.STDOUT)
    write(log.with_suffix('.json'),dict(command=command,cwd=ROOT.as_posix(),actual_exit=child.returncode,
        seconds=time.monotonic()-tick,log_sha256=sha(log)))
    assert child.returncode==0
    return log

remote('final-push-v1',['git','-c','credential.helper=','-c','credential.helper=!gh auth git-credential','push','origin',BRANCH])
for n in range(3):
    p=remote('final-PR'+str(number)+'-v'+str(n+1),['gh','pr','view',str(number),'--json',
        'number,url,title,body,state,isDraft,headRefOid,headRefName,baseRefName,mergedAt,statusCheckRollup'])
    actual=load(p)
    if actual['headRefOid']==head:break
    time.sleep(2)
assert actual['headRefOid']==head and actual['headRefName']==BRANCH
assert actual['baseRefName']=='codex/research-online-c1-source-reconcile'
assert actual['state']=='OPEN' and actual['isDraft'] and actual['mergedAt'] is None
assert actual['title']==(RUN/'prospective-PR-title-v1.txt').read_text(encoding='utf8').strip()
assert actual['body'].replace('\r\n','\n').rstrip('\n')==(RUN/'prospective-PR-body-v1.md').read_text(encoding='utf8').rstrip('\n')
assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],encoding='utf8').strip()
write(ROOT/'tmp/online-ftl-obstruction-final-ready-v1.json',dict(actual_final_head=head,branch=BRANCH,
    PR=number,url=actual['url'],exact_stacked_base=BASE,basePR=201,state='OPEN',draft=True,
    merged=False,live=False,worktree_clean=True,official_attachment_committed=True,
    remote_checks_capture=actual['statusCheckRollup'],remote_all_required_passed=False,
    applicable_clean_local_site_source=load(RUN/'registry-v2.json')['source_commit'],
    current_public_canary_and_pins_unchanged=True,worktree_retained_for_next_required_obligation=ROOT.as_posix(),
    chapter_complete=False,goal_complete=False))
print('Actual final OPEN draft PR',number,'exact remote head:',head,'clean checkout; whole Goal ACTIVE.',flush=True)
