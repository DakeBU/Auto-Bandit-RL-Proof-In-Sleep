"""Use existing manifest schema: affected production surfaces versus owned test evidence."""
from common_v4 import *
fixed(True,True);passed('history-bindings-v2-01');passed('project-gates-v2-01')
assert load(RUN/'contributor-exact-v1-01-exit.json')['exit_code']==1
assert 'not changed protected/production surfaces: Tests.lean, Tests/OnlineConvexNondifferentiabilityCanary.lean' in (RUN/'contributor-exact-v1-01.log').read_text(encoding='utf-8')
p=Path('research-wiki/contribution-contracts/online-convex-nondifferentiability-20261007.json');old=p.read_bytes();write(RUN/'snapshots/manifest-before-test-surface-schema-repair-v2.txt',old)
d=load(p);tests=['Tests.lean',CANARY.as_posix()];assert all(t in d['affected_files'] for t in tests)
d['affected_files']=[t for t in d['affected_files'] if t not in tests]
assert d['verification']['owned_test_files']==[CANARY.as_posix()]
d['verification']['owned_test_root_files']=['Tests.lean']
p.write_bytes((json.dumps(d,ensure_ascii=False,indent=2)+'\n').encode())
write(RUN/'contributor-schema-repair-v2.json',dict(failed_attempt='contributor-exact-v1-01',existing_checker_unchanged=True,reason='Existing affected_files checks protected production surfaces only, while Tests has separate owned-test evidence fields',old_snapshot='snapshots/manifest-before-test-surface-schema-repair-v2.txt',new_manifest_sha256=sha(p),tests_still_explicitly_owned=d['verification']['owned_test_files'],test_root_still_recorded=d['verification']['owned_test_root_files'],source_headers_bodies_root_Tests_unchanged=True,mathematical_repairs=[]))
oldscript=RUN/'source-site-gates-v2.py';t=oldscript.read_text(encoding='utf-8')
t=t.replace("gate('history-bindings-v2-01',sys.executable,'-B','-X','utf8',RUN/'verify-history-bindings-v2.py')","passed('history-bindings-v2-01')")
t=t.replace('contributor-exact-v1-01','contributor-exact-v2-01')
write(RUN/'source-site-gates-v3.py',t);compile(t,str(RUN/'source-site-gates-v3.py'),'exec')
t=(RUN/'bind-integrated-gates-v1.py').read_text(encoding='utf-8').replace('contributor-exact-v1-01','contributor-exact-v2-01').replace("'Full harness v1 tracked-source fence failure; stage owned Lean files only and rerun actual root/Tests/full harness v2'","'Full harness v1 tracked-source fence failure; stage owned Lean files only and rerun actual root/Tests/full harness v2','Exact contributor v1 rejected Tests in production-surface list; existing schema retained, tests remain in explicit owned-test fields, exact v2 recheck'")
write(RUN/'bind-integrated-gates-v2.py',t);compile(t,str(RUN/'bind-integrated-gates-v2.py'),'exec')
fixed(True,True);print('Manifest-only schema repair preserves explicit test ownership and all compiled source bytes; contributor v2 actual recheck remains required.')
