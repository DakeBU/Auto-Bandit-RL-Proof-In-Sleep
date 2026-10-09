from publication_guard_v4 import *
fixed();review=load(RUN/'actual-delivery-review-v1.json')
assert review['verdict'] in ['accepted','accepted-with-explicit-delta'] and not review['required_repairs']
assert review['actual_delivery_verdict']=='accepted' and review['prospective_evidence_only_commit_verdict']=='accepted'
packet=load(RUN/'actual-delivery-review-inputs-v1.json')
assert subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf8').strip()==packet['delivered_head']
for row in packet['rows']:assert sha(row['path'])==row['sha256'],row['path']
tail=ROOT/'tmp/online-ch2-prescient-causal-delivery-final-v1';assert not tail.exists();tail.mkdir()
def obs(label,args,allowed=(0,)):
    start=time.monotonic();p=subprocess.run(list(map(str,args)),cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    write(tail/(label+'.json'),dict(command=list(map(str,args)),actual_exit=p.returncode,seconds=time.monotonic()-start,stdout_sha256=hashlib.sha256(p.stdout).hexdigest(),stdout_base64=base64.b64encode(p.stdout).decode('ascii')))
    print(label,'actual exit',p.returncode,flush=True)
    assert p.returncode in allowed,(label,p.stdout.decode('utf8',errors='replace'))
    return p.stdout.decode('utf8',errors='replace')
new=[]
for line in subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],encoding='utf8').splitlines():
    assert line[:2]=='??',line
    rel=line[3:];assert rel.startswith(RUN.relative_to(ROOT).as_posix()+'/'),rel;new.append(rel)
assert new
obs('stage-for-RAW-snapshot',['git','add',*new])
raw=[]
for rel in new:
    p=ROOT/rel;data=p.read_bytes();blob=subprocess.check_output(['git','show',':'+rel])
    if data!=blob:
        assert data.replace(b'\r\n',b'\n')==blob,rel
        raw.append(dict(path=rel,raw_sha256=sha(p),git_blob_sha256=hashlib.sha256(blob).hexdigest(),raw_base64=base64.b64encode(data).decode('ascii'),only_CRLF_to_LF=True))
snap=RUN/'exact-RAW-line-ending-snapshots-delivery-final-v1.json';write(snap,dict(rows=raw,scope='Create-only actual delivery evidence and distinct review RAW bytes; no preexisting input mutation.'))
obs('final-stage',['git','add',*new,snap.relative_to(ROOT).as_posix()])
staged=obs('staged-paths',['git','diff','--cached','--name-only']).splitlines();assert set(staged)==set(new+[snap.relative_to(ROOT).as_posix()])
for row in packet['rows']:assert sha(row['path'])==row['sha256'],row['path']
fixed()
obs('full-package-whitespace',['git','diff','--cached',BASE,'--check'])
obs('commit',['git','commit','-m','Bind actual prescient causal proof PR delivery and review evidence'])
head=subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf8').strip()
assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],encoding='utf8').strip();fixed()
for label,base in [('contributor-stack',BASE),('contributor-main','origin/main')]:
    out=obs(label,[sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base',base]);assert 'Contributor contract: N/A' not in out and PUBLIC.relative_to(ROOT).as_posix() in out
obs('push',['git','-c','credential.helper=','-c','credential.helper=!gh auth git-credential','push','origin',BRANCH])
assert obs('remote',['git','ls-remote','origin','refs/heads/'+BRANCH]).split()[0]==head
pr=json.loads(obs('new prescient causal PR',['gh','pr','view',str(packet['PR']),'--json','number,url,state,isDraft,headRefName,headRefOid,baseRefName,title,body,mergedAt']))
old=load(RUN/'actual-delivery-summary-v1.json')['actual']['PR']
assert all(pr[k]==old[k] for k in old if k!='headRefOid') and pr['headRefOid']==head
assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],encoding='utf8').strip()
write(tail/'inspected.json',dict(final_head=head,remote_head=head,clean=True,PR=pr,official_attachment_sha256=sha(RUN/'official-PR-attachment-v1.json'),distinct_review_sha256=sha(RUN/'actual-delivery-review-v1.json'),only_OWN_new_delivery_evidence=True,math_or_reader_change=False,site_fresh_at_final_head=False,chapter_complete=False,whole_Goal_status='ACTIVE',merge=False,deploy=False))
print('Evidence-only new prescient causal PR delivery complete at',head,'; whole Goal ACTIVE.')
