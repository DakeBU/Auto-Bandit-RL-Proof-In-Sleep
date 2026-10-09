from common_v1 import *
fixed();targets=load(CONTRACT/'targets-v1.json')['targets'];checks=[]
for t in targets:
    fence=CONTRACT/('public-'+t['id']+'-fence-v1.json')
    gate('fence-'+t['id']+'-v1',sys.executable,'-B','-X','utf8','tools/bandit.py','statement-fence','--declaration',t['name'],'--file',Path(t['path']).relative_to(ROOT),'--output',fence)
    f=load(fence);assert f['statement_hash']==t['statement_hash']
    gate('safe-'+t['id']+'-v1',sys.executable,'-B','-X','utf8','tools/bandit.py','safe-verify','--fence',fence,'--lean-file',t['path'])
    checks.append(dict(id=t['id'],name=t['name'],actual_statement_hash_unchanged=True,fence_path=fence.resolve().as_posix(),fence_sha256=sha(fence),actual_safe_verify_exit=0,source_acceptance_not_inferred=True))
fixed()
write(RUN/'public-fence-audit-v1.json',dict(targets=checks,actual_native_fences=len(checks),actual_native_safe_checks=len(checks),all_statement_hashes_equal_frozen_draft=True,all_public_bytes_unchanged=True,chapter_accepted=False,goal_complete=False))
print('Actual current native statement fences/safe checks:',len(checks),flush=True)
