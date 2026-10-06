"""Retrieve current real APIs and compile the exact retained definition/equivalence."""
from common_v2 import *
fixed();passed('freeze-draft-v1-01')
for command in ['statement-fence','retrieval-record','lifecycle-event','list-lean-decls','search-memory','reference-index','list-mathlib','list-papers','list-weapons','safe-verify','trial-log','frontier-refresh','frontier-shadow']:
 native(command+'-help-v1-01',command,'--help')
event('draft',dict(frozen_headers=load(RUN/'draft-freeze-v1.json')['headers'],source_package_accepted=False,retained_proofs=1,retained_definitions=1,new_proofs=0,source_convention='Explicit NNReal incl0; literal negative real-L zero-dimensional obstruction requires reviewer judgment.'))
for command in ['list-mathlib','list-papers','list-weapons']:native(command+'-v1',command)
native('local-declaration-search-v1','list-lean-decls','lipschitz','--statement')
native('local-declaration-search-v2','list-lean-decls','subgradient_exists_of_domain_interior','--statement')
native('local-memory-search-v1','search-memory','convex proper interior Lipschitz every global subgradient nonnegative constant')
generated('readiness-probes-before-use-v1.json',[RUN/'leaves/pinned-APIs-v1.lean',RUN/'leaves/actual-types-v1.lean',RUN/'leaves/export-ready-dependencies-v1.lean'])
gate('retained-focused-v1-01','lake','build','BanditRLProof.OnlineLipschitzSubgradient','Tests.OnlineLipschitzSubgradientCanary')
assert 'Build completed successfully' in (RUN/'retained-focused-v1-01.log').read_text(encoding='utf-8')
gate('actual-types-v1-01','lake','env','lean',RUN/'leaves/actual-types-v1.lean')
gate('pinned-APIs-v1-01','lake','env','lean',RUN/'leaves/pinned-APIs-v1.lean')
gate('compiled-ready-graph-v1-01','lake','env','lean','--run',RUN/'leaves/export-ready-dependencies-v1.lean',RUN/'compiled-ready-graph-v1.json')
gate('reference-index-scoped-v1-01',sys.executable,'-B','-X','utf8',RUN/'scoped-reference-index-v1.py')
fixed();print('Actual focused/types/APIs/compiled readiness/retrieval passed; source-convention stabilization remainspending.')
