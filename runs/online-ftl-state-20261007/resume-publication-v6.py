from common_v1 import *
fixed(proving=True,integrated=True)
r=load(RUN/'publication-repair-receipt-v2.json');assert r['actor']['task']=='/root/source_reviewer' and r['verdict'] in ['accepted','accepted-with-explicit-delta'] and sha(r['report'])==r['report_sha256']
for key in ['required_repairs','required_mathematical_repairs','required_metadata_repairs','required_blocking_reader_repairs']:assert not r.get(key,[]),key
reviewed={x['path']:x['sha256'] for x in r['reviewed_files']}
for x in load(RUN/'publication-repair-inputs-v2.json')['rows']:assert reviewed[x['path']]==x['sha256']==sha(x['path']),x['path']
for p,h in reviewed.items():assert sha(p)==h,p
for x in load(RUN/'final-reader-inputs-v1.json')['rows']:assert sha(x['path'])==x['sha256'],x['path']
for label in ['full-harness-final-v1','contributor-final-v1','scoped-diff-final-v2','source-scope-final-v2']:assert load(RUN/(label+'-exit.json'))['exit_code']==0
write(RUN/'publication-repair-accepted-v2.json',dict(status=r['verdict'],report_sha256=r['report_sha256'],receipt_sha256=sha(RUN/'publication-repair-receipt-v2.json'),all_original785_FINAL_bindings_unchanged=True,source_math_native_acceptance_unchanged=True,actual_batched_scoped_gate=load(RUN/'scoped-diff-audit-final-v2.json'),source_scope_gate='source-scope-final-v2',chapter_complete=False,goal_complete=False))
subprocess.run([sys.executable,'-B','-X','utf8',str(RUN/'commit-owned-v2.py'),'Bind final FTL-state contributor and source-preservation gates'],check=True)
assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],text=True).strip()
cmd=[sys.executable,'-B','-X','utf8',str(RUN/'audit-committed-raw-v1.py')];temporary=Path('tmp/online-ftl-state-raw-audit-v1.log');start=time.time()
with temporary.open('wb') as stream:child=subprocess.run(cmd,stdout=stream,stderr=subprocess.STDOUT)
write(RUN/'committed-raw-audit-v1.log',temporary.read_bytes());write(RUN/'committed-raw-audit-v1-exit.json',dict(command=cmd,cwd=ROOT.as_posix(),exit_code=child.returncode,seconds=round(time.time()-start,3),log_sha256=sha(RUN/'committed-raw-audit-v1.log'),stdout_ignored_until_completion=True));assert child.returncode==0
subprocess.run([sys.executable,'-B','-X','utf8',str(RUN/'commit-owned-v2.py'),'Preserve raw FTL-state evidence before authorized draft publication'],check=True)
assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],text=True).strip()
gate('push-creation-v1','git','-c','credential.helper=','-c','credential.helper=!gh auth git-credential','push','-u','origin',BRANCH)
gate('create-pr-v1',sys.executable,'-B','-X','utf8',RUN/'create-pr-v1.py')
fixed(proving=True,integrated=True)
