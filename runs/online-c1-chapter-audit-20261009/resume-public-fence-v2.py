from common_v1 import *
fixed()
write(RUN/'public-fence-failure-v1.md','''public-fence-audit-v1.py actually exited1 after49 real native statement-fence/safe-verify pairs passed. The50th input resolves through the shared .lake/packages junction to E:/ABRL/research/.lake/packages/mathlib; the utility incorrectly required its absolute source path to be lexically under this worktree. No50th native command had run and no whole audit receipt was emitted. V2 preserves all49 logs/fences and uses the native supported absolute read-only file path for the exact pinned upstream theorem. No dependency source/junction/compiler/API or mathematical target was changed.''')
targets=load(CONTRACT/'targets-v1.json')['targets'];checks=[]
for t in targets:
    if t['id']=='A050':
        fence=CONTRACT/('public-'+t['id']+'-fence-v2.json')
        gate('fence-'+t['id']+'-v2',sys.executable,'-B','-X','utf8','tools/bandit.py','statement-fence','--declaration',t['name'],'--file',t['path'],'--output',fence)
        gate('safe-'+t['id']+'-v2',sys.executable,'-B','-X','utf8','tools/bandit.py','safe-verify','--fence',fence,'--lean-file',t['path'])
        version='v2'
    else:
        fence=CONTRACT/('public-'+t['id']+'-fence-v1.json');version='v1'
    assert load(fence)['statement_hash']==t['statement_hash']
    assert load(RUN/('fence-'+t['id']+'-'+version+'-exit.json'))['actual_exit']==0
    assert load(RUN/('safe-'+t['id']+'-'+version+'-exit.json'))['actual_exit']==0
    checks.append(dict(id=t['id'],name=t['name'],actual_statement_hash_unchanged=True,fence_path=fence.resolve().as_posix(),fence_sha256=sha(fence),actual_safe_verify_exit=0,source_acceptance_not_inferred=True))
fixed()
write(RUN/'public-fence-audit-v2.json',dict(targets=checks,actual_native_fences=50,actual_native_safe_checks=50,all_statement_hashes_equal_frozen_draft=True,all_public_bytes_unchanged=True,original_partial_v1_failure_retained=True,chapter_accepted=False,goal_complete=False))
print('Actual50 current native fences/safe checks passed; upstream shared junction preserved.',flush=True)
