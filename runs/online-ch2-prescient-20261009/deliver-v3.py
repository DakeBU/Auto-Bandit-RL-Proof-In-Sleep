from publication_guard_v3 import *
import re

fixed()
post=RUN/'post-native-review-v1.json';r=load(post)
assert sha(post)=='72631c85b955d178eb3524ef2ac736573ba23ac5fcbff4cce2f638feded5744e'
assert r['native_verdict']==r['metadata_verdict']==r['prospective_publication_prose_verdict']=='accepted-with-explicit-delta'
assert r['FINAL_sha256']==sha(RUN/'FINAL-review-v1.json')
repair=load(RUN/'delivery-helper-review-v3.json')
assert repair['verdict']=='accepted-with-explicit-delta' and not repair['required_repairs']
for packet in ['post-native-inputs-v1.json','delivery-helper-inputs-v2.json','delivery-helper-inputs-v3.json']:
    for row in load(RUN/packet)['rows']:assert sha(row['path'])==row['sha256'],row['path']
plan=load(RUN/'PR-plan-v1.json');assert sha(plan['body_path'])==plan['body_sha256']
assert plan['base']=='codex/research-online-ch2-chapter-audit' and plan['head']==BRANCH and plan['parent_exact_head']==BASE
assert plan['draft'] and not plan['merge'] and not plan['deploy']
stage=load(RUN/'candidate-stage-plan-v1.json')['stage']
def scope():
    for line in subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],encoding='utf8').splitlines():
        rel=line[3:]
        assert rel in stage or any(rel.startswith(prefix+'/') for prefix in [RUN.relative_to(ROOT).as_posix(),CONTRACT.relative_to(ROOT).as_posix()]),rel
scope()
# Terminal observations go to ignored tmp to avoid commit/hash self-reference loops.
delivery=ROOT/'tmp'/'online-ch2-prescient-delivery-v3';assert not delivery.exists();delivery.mkdir()
def observe(label,args,required=True):
    start=time.monotonic();p=subprocess.run(list(map(str,args)),cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    write(delivery/(label+'.json'),dict(command=list(map(str,args)),actual_exit=p.returncode,cwd=ROOT.as_posix(),seconds=time.monotonic()-start,stdout_sha256=hashlib.sha256(p.stdout).hexdigest(),stdout_base64=base64.b64encode(p.stdout).decode('ascii')))
    print(label,'actual exit',p.returncode,flush=True)
    if required:assert p.returncode==0,(label,p.stdout.decode('utf8',errors='replace'))
    return p.stdout.decode('utf8',errors='replace')
capture('acceptance-stage-v3','git','add',*stage)
code,out=capture('acceptance-full-package-diff-v3','git','diff','--cached',BASE,'--check',required=False)
exceptions=load(RUN/'FINAL-review-v1.json')['whitespace']['exceptions']
expected={Path(x['path']).relative_to(ROOT).as_posix() for x in exceptions}
actual={line.split(':',1)[0] for line in out.splitlines() if ': new blank line at EOF.' in line}
assert code==2 and actual==expected and ': trailing whitespace.' not in out
for row in exceptions:assert sha(row['path'])==row['sha256']
capture('acceptance-scoped-package-diff-v3','git','diff','--cached',BASE,'--check','--','.',*[':(exclude)'+p for p in sorted(expected)])
rawrows=[]
for rel in subprocess.check_output(['git','diff','--cached','--name-only'],encoding='utf8').splitlines():
    p=ROOT/rel;raw=p.read_bytes();blob=subprocess.check_output(['git','show',':'+rel])
    if raw!=blob:
        assert raw.replace(b'\r\n',b'\n')==blob,rel
        rawrows.append(dict(path=rel,raw_sha256=sha(p),git_blob_sha256=hashlib.sha256(blob).hexdigest(),raw_base64=base64.b64encode(raw).decode('ascii'),only_CRLF_to_LF=True))
write(RUN/'exact-RAW-line-ending-snapshots-v3.json',dict(rows=rawrows,prior_snapshots=rows([RUN/'exact-RAW-line-ending-snapshots-v1.json',RUN/'exact-RAW-line-ending-snapshots-v2.json']),scope='Actual additional acceptance staged RAW/blob CRLF differences only; historical snapshots immutable.'))
observe('acceptance-final-stage',['git','add',*stage])
fixed();scope()
# No RUN writes from here onward. All actual terminal receipts are ignored tmp.
full=observe('final-package-diff-full',['git','diff','--cached',BASE,'--check'],required=False)
full_receipt=load(delivery/'final-package-diff-full.json')
actual_final={line.split(':',1)[0] for line in full.splitlines() if ': new blank line at EOF.' in line}
assert full_receipt['actual_exit']==2 and actual_final==expected and ': trailing whitespace.' not in full
observe('final-package-diff-scoped',['git','diff','--cached',BASE,'--check','--','.',*[':(exclude)'+p for p in sorted(expected)]])
staged=observe('final-staged-scope',['git','diff','--cached','--name-only']).splitlines()
for rel in staged:
    assert rel in stage or any(rel.startswith(prefix+'/') for prefix in [RUN.relative_to(ROOT).as_posix(),CONTRACT.relative_to(ROOT).as_posix()]),rel
assert staged
parent=json.loads(observe('parent-PR204',['gh','pr','view','204','--json','number,state,isDraft,headRefName,headRefOid,baseRefName,mergedAt,url']))
assert parent['state']=='OPEN' and parent['mergedAt'] is None and parent['headRefOid']==BASE and parent['headRefName']==plan['base']
observe('acceptance-commit',['git','commit','-m','Record accepted affine prescient verification and reader evidence'])
head=subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf8').strip()
assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],encoding='utf8').strip()
fixed()
for label,base in [('contributor-stack',BASE),('contributor-main','origin/main')]:
    out=observe(label,[sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base',base])
    assert 'Contributor contract: N/A' not in out and PUBLIC.relative_to(ROOT).as_posix() in out
observe('push',['git','-c','credential.helper=','-c','credential.helper=!gh auth git-credential','push','origin',BRANCH])
remote=observe('remote-head',['git','ls-remote','origin','refs/heads/'+BRANCH]);assert remote.split()[0]==head
prs=json.loads(observe('existing-PRs',['gh','pr','list','--head',BRANCH,'--state','open','--json','number,url,isDraft,headRefOid,baseRefName']))
assert len(prs)<=1
if prs:
    pr=prs[0];assert pr['isDraft'] and pr['headRefOid']==head and pr['baseRefName']==plan['base'];url=pr['url']
else:
    out=observe('create-PR',['gh','pr','create','--draft','--base',plan['base'],'--head',BRANCH,'--title',plan['title'],'--body-file',plan['body_path']])
    urls=re.findall(r'https://github\.com/[^\s]+/pull/\d+',out);assert len(urls)==1;url=urls[0]
pr=json.loads(observe('created-PR',['gh','pr','view',url,'--json','number,url,state,isDraft,headRefName,headRefOid,baseRefName,title,body,mergedAt']))
assert pr['state']=='OPEN' and pr['isDraft'] and pr['mergedAt'] is None and pr['headRefOid']==head and pr['headRefName']==BRANCH and pr['baseRefName']==plan['base']
def body_normalized(s):
    s=s.replace('\r\n','\n')
    return s[:-1] if s.endswith('\n') else s
assert pr['title']==plan['title'] and body_normalized(pr['body'])==body_normalized(Path(plan['body_path']).read_text(encoding='utf8'))
fixed();assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],encoding='utf8').strip()
write(delivery/'inspected.json',dict(actual_head=head,actual_remote_head=head,PR=pr,stacked_exact_base=BASE,actual_clean=True,body_comparison='CRLF to LF and at most one final LF; no other whitespace normalized',applicable_site_source_commit='5680bcca81c5f894b801c0599689f2a5870e8306',no_fresh_site_at_delivery_head_claim=True,official_attachment='pending',distinct_delivery_review='pending',chapter_complete=False,whole_Goal_status='ACTIVE'))
print('Actual clean scoped commit/push/draft PR verified. Official attachment and distinct delivery review remain pending:',url)
