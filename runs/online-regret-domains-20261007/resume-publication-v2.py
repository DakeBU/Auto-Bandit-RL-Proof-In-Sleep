from common_v1 import *
fixed(integrated=True)
r=load(RUN/'publication-repair-receipt-v2.json');assert r['actor']['task']=='/root/source_reviewer' and r['verdict'] in ['accepted','accepted-with-explicit-delta'] and sha(r['report'])==r['report_sha256']
reviewed={x['path']:x['sha256'] for x in r['reviewed_files']}
for row in load(RUN/'publication-repair-inputs-v2.json')['rows']:assert reviewed[row['path']]==row['sha256']==sha(row['path'])
for p,h in reviewed.items():assert sha(p)==h,p
for key in ['required_repairs','required_mathematical_repairs','required_metadata_repairs']:assert not r.get(key,[])
f=load(RUN/'final-reader-receipt-v1.json');assert sha(f['report'])==f['report_sha256']
for row in load(RUN/'final-reader-inputs-v1.json')['rows']:assert sha(row['path'])==row['sha256'],row['path']
write(RUN/'publication-repair-accepted-v2.json',dict(status=r['verdict'],receipt_sha256=sha(RUN/'publication-repair-receipt-v2.json'),fixed_rows=len(load(RUN/'publication-repair-inputs-v2.json')['rows']),prior_FINAL401_unchanged=True,mathematical_target_unchanged=True,actual_retry_not_yet_passed=True,goal_complete=False))
native('publication-repair-accepted-event-v2','lifecycle-event','--session',TASK,'--event','accepted','--payload-json',json.dumps(dict(scope='Reviewed same-scope publication retry, success pending',record=(RUN/'publication-repair-accepted-v2.json').as_posix(),no_new_math=True,chapter_complete=False,goal_complete=False)))
gate('source-scope-publication-repair-v2',sys.executable,'-B','-X','utf8',RUN/'audit-scope-v1.py','publication-repair-v2')
subprocess.run([sys.executable,'-B','-X','utf8',str(RUN/'commit-owned-v2.py'),'Preserve transient GitHub push failure and reviewed same-scope retry'],check=True)
assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],encoding='utf-8').strip()
gate('push-creation-v2','git','-c','credential.helper=','-c','credential.helper=!gh auth git-credential','push','-u','origin',BRANCH)
gate('create-pr-v2',sys.executable,'-B','-X','utf8',RUN/'create-pr-v2.py')
fixed(integrated=True)
