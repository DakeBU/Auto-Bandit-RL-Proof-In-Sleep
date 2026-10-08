from common_accepted_v3 import *
from commit_owned_v1 import stage_owned,commit_owned
import re

accepted_fixed()
delivery=load(RUN/'delivery-receipt-v3.json')
assert delivery['verdict'] in ['accepted','accepted-with-explicit-delta'] and delivery['inputs_unchanged']
assert not delivery['required_blocking_repairs']
assert delivery['report_sha256']==sha(RUN/'delivery-review-v3.md')
assert all(sha(r['path'])==r['sha256'] for r in load(RUN/'delivery-review-inputs-v3.json')['rows'])
changed=subprocess.check_output(['git','diff','HEAD','--name-only','-z']).decode('utf8').split('\0')
untracked=subprocess.check_output(['git','ls-files','--others','--exclude-standard','-z']).decode('utf8').split('\0')
assert all(p.startswith(RUN.relative_to(ROOT).as_posix()+'/') for p in changed+untracked if p)
stage_owned()
cmd=['git','-c','core.whitespace=blank-at-eol,blank-at-eof,space-before-tab,cr-at-eol','diff','--cached','--check','HEAD']
gate('delivery-evidence-full-diff-v4',*cmd,required=False)
code=load(RUN/'delivery-evidence-full-diff-v4-exit.json')['actual_exit'];assert code in [0,2]
bad=set(re.findall(r'^([^\r\n]+?):\d+: (?:trailing whitespace|new blank line at EOF|space before tab)',
    (RUN/'delivery-evidence-full-diff-v4.log').read_text(encoding='utf8'),re.M))
bound={r['sha256'] for r in load(RUN/'delivery-review-inputs-v3.json')['rows']}
exceptions=[]
for rel in sorted(bad):
    p=ROOT/rel;assert p.suffix=='.log' and sha(p) in bound and list(RUN.glob(p.stem+'*exit.json')),rel
    exceptions.append(dict(path=rel,sha256=sha(p),reason='Exact delivery-reviewed actual raw command output only'))
if code:
    assert bad
    exceptions.append(dict(path=(RUN/'delivery-evidence-full-diff-v4.log').relative_to(ROOT).as_posix(),
        sha256=sha(RUN/'delivery-evidence-full-diff-v4.log'),reason='Actual raw whitespace diagnostic'))
write(RUN/'delivery-evidence-raw-exceptions-v4.json',dict(exceptions=exceptions,
    full_unexcluded_actual_exit=code,full_unexcluded_passed=code==0,source_and_executable_exceptions=0))
stage_owned()
gate('delivery-evidence-scoped-diff-v4',*cmd,'--','.',*[':(exclude)'+r['path'] for r in exceptions])
assert all(sha(r['path'])==r['sha256'] for r in load(RUN/'delivery-review-inputs-v3.json')['rows'])
commit_owned('Record reviewed draft PR198 creation, official attachment and delivery evidence')
head=subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf8').strip()
# Final remote outputs are intentionally ignored task-local receipts, avoiding a false self-referential commit hash.
tmp=ROOT/'tmp';tmp.mkdir(exist_ok=True)
def remote(label,args):
    out=tmp/(label+'.log');receipt=tmp/(label+'-exit.json')
    assert not out.exists() and not receipt.exists()
    start=time.monotonic()
    with out.open('wb') as stream:r=subprocess.run(args,stdout=stream,stderr=subprocess.STDOUT)
    write(receipt,dict(command=args,cwd=ROOT.as_posix(),actual_exit=r.returncode,seconds=time.monotonic()-start,log_sha256=sha(out)))
    assert r.returncode==0,label
    return out
remote('online-ae-causal-final-push-v4',['git','-c','credential.helper=',
    '-c','credential.helper=!gh auth git-credential','push','origin',BRANCH])
p=remote('online-ae-causal-final-PR198-v4',['gh','pr','view','198','--json',
    'number,url,title,body,state,isDraft,headRefOid,baseRefName,headRefName,mergedAt,statusCheckRollup'])
r=load(p)
assert r['headRefOid']==head and r['headRefName']==BRANCH and r['baseRefName']=='codex/research-online-c1-core-audit'
assert r['state']=='OPEN' and r['isDraft'] and r['mergedAt'] is None
assert r['body'].replace('\r\n','\n').rstrip('\n')==(RUN/'prospective-PR-body-v2.md').read_text(encoding='utf8').replace('\r\n','\n').rstrip('\n')
assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],encoding='utf8').strip()
write(tmp/'online-ae-causal-final-ready-v4.json',dict(actual_final_head=head,branch=BRANCH,PR=198,url=r['url'],
    exact_stacked_base=BASE,basePR=197,state='OPEN',draft=True,merged=False,live=False,
    worktree_clean=True,official_attachment_committed=True,
    remote_checks_capture=r['statusCheckRollup'],remote_all_required_passed=False,
    note='Remote snapshot at final evidence push; running checks are not passed. Current three proof bodies/local gates unchanged.',
    worktree_retained_for_next_required_completion_bridge=ROOT.as_posix(),chapter_complete=False,goal_complete=False))
print('Actual final OPENdraft198 head',head,'clean worktree, whole Goal active; remote check snapshot saved without success claim.',flush=True)
