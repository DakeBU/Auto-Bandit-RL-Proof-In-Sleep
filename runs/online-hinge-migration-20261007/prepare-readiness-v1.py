"""Retrieve actual APIs and compile current named declarations before source stabilization."""
from common_v2 import *
fixed();passed('freeze-draft-v1-01')
for command in ['statement-fence','retrieval-record','lifecycle-event','list-lean-decls','search-memory','reference-index','list-mathlib','list-papers','list-weapons','safe-verify','trial-log','frontier-refresh','frontier-shadow']:
 native(command+'-help-v1-01',command,'--help')
event('draft',dict(frozen_headers=load(RUN/'draft-freeze-v1.json')['headers'],source_package_accepted=False,retained_proofs=13,retained_definitions=2,new_proofs=0))
for command in ['list-mathlib','list-papers','list-weapons']:native(command+'-v1',command)
native('local-declaration-search-v1','list-lean-decls','hinge','--statement')
native('local-declaration-search-v2','list-lean-decls','affine_subdifferential','--statement')
native('local-memory-search-v1','search-memory','hinge finite maximum full subdifferential')
source=RUN/'leaves/pinned-APIs-v1.lean';text=source.read_text(encoding='utf-8')
assert '#check @convexExtended_iff_toReal' in text
write(RUN/'leaves/pinned-APIs-v2.lean',text.replace('#check @convexExtended_iff_toReal','#check @'+PRE+'convexExtended_iff_toReal'))
write(RUN/'API-pre-use-qualification-v2.json',dict(original=source.as_posix(),original_sha256=sha(source),unused_original_probe_preserved=True,actual_failed_probe=False,correction='The shared convexExtended_iff_toReal is namespace-qualified in v2 before any probe is executed; original producer is unchanged.',source_or_statement_changed=False))
generated('readiness-probes-before-use-v1.json',[RUN/'leaves/pinned-APIs-v2.lean',RUN/'leaves/actual-types-v1.lean',RUN/'leaves/export-ready-dependencies-v1.lean'])
gate('retained-focused-v1-01','lake','build','BanditRLProof.OnlineHinge','Tests.OnlineHingeCanary')
assert 'Build completed successfully' in (RUN/'retained-focused-v1-01.log').read_text(encoding='utf-8')
gate('actual-types-v1-01','lake','env','lean',RUN/'leaves/actual-types-v1.lean')
gate('pinned-APIs-v2-01','lake','env','lean',RUN/'leaves/pinned-APIs-v2.lean')
gate('compiled-ready-graph-v1-01','lake','env','lean','--run',RUN/'leaves/export-ready-dependencies-v1.lean',RUN/'compiled-ready-graph-v1.json')
fixed();print('Actual focused compilation/types/qualified API probe/production readiness graph passed; source stabilization pending.')
