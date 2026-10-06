from common import *
f=fixed();L=RUN/'leaves'
public=[PRE+n for n in f['headers']];canary=['NormalIndicatorProbe.interval_boundary_and_outside_canary','NormalIndicatorProbe.thin_singleton_all_normals_canary','NormalGeometryProbe.interval_interior_canary','NormalGeometryProbe.e0','NormalGeometryProbe.e1','NormalGeometryProbe.two_dimensional_unit_boundary_canary'];q=public+canary
write(RUN/'public-named-declarations-v1.json',dict(production_proofs=[PRE+n for n in f['proof_names']],owned_definition=[PRE+'SourceNormalCone'],whole_canary_proofs=[n for n in canary if n.rsplit('.',1)[1] not in ['e0','e1']],whole_canary_definitions=['NormalGeometryProbe.e0','NormalGeometryProbe.e1'],axiom_probe=q,all_named=10,new_math_or_tests=0))
write(L/'public-all-axioms-v1.lean','import BanditRLProof\nimport Tests.OnlineNormalConeCanary\n'+'\n'.join('#print axioms '+n for n in q))
s=(L/'export-ready-dependencies-v1.lean').read_text(encoding='utf-8');a=s.index('def targets :');b=s.index('\ndef moduleName',a)
s=s[:a]+'def targets : Array Name := #[\n '+',\n '.join('`'+n for n in q)+']\n'+s[b:]
s=s.replace('`BanditRLProof }]','`BanditRLProof }, { module := `Tests.OnlineNormalConeCanary }]')
s=s.replace('four retained normal-cone production nodes: one definition/three proofs; direct type/value occurrence only; canaries not yet exported','TEN selected compiled nodes: THREE production proofs/ONE owned definition, FOUR whole canary proofs/TWO TEST basis definitions; direct type/value occurrences only, not fullregistrygraph')
write(L/'export-public-dependencies-v1.lean',s)
s=Path('runs/online-subgradient-absolute-migration-20261007/preserve-native-prefix-v2.py').read_text(encoding='utf-8')
s=s.replace("load(RUN/'historical-raw-supersession-v1.json')", "load(RUN/'historical-raw-supersession-v2.json')")
write(RUN/'preserve-native-prefix-v1.py',s)
native('safe-verify-help-v1-01','safe-verify','--help')
generated('proving-generated-before-use-v1.json',[L/'public-all-axioms-v1.lean',L/'export-public-dependencies-v1.lean',RUN/'public-named-declarations-v1.json',RUN/'preserve-native-prefix-v1.py'])
print('All10 currentkernel names/10node selectedexporter/exact reviewed-log preservation prepared; original math fixed.')
