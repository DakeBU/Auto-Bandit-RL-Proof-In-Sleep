from common import *
f=fixed();L=RUN/'leaves'
public=['SourceNormalCone']+f['proof_names']
canary=['NormalIndicatorProbe.interval_boundary_and_outside_canary','NormalIndicatorProbe.thin_singleton_all_normals_canary','NormalGeometryProbe.interval_interior_canary','NormalGeometryProbe.e0','NormalGeometryProbe.e1','NormalGeometryProbe.two_dimensional_unit_boundary_canary']
write(L/'actual-types-v1.lean','import BanditRLProof\nimport Tests.OnlineNormalConeCanary\n'+'\n'.join('#check @'+PRE+n for n in public)+'\n'+'\n'.join('#check @'+n for n in canary)+'\n'+'\n'.join('#print '+PRE+n for n in ['SourceNormalCone','SourceSubdifferential','extendedIndicator','SourceProper','effectiveDomain']))
apis=[PRE+'sourceProper_indicator_iff',PRE+'effectiveDomain_indicator',PRE+'subgradient_point_finite','Metric.mem_nhds_iff','mem_interior_iff_mem_nhds','interior_subset','norm_smul_inv_norm','real_inner_le_norm','norm_sub_sq_real','real_inner_self_eq_norm_sq','real_inner_smul_right','real_inner_smul_left','norm_smul_of_nonneg','norm_eq_zero','EReal.coe_le_coe_iff']
write(L/'pinned-APIs-v1.lean','import BanditRLProof\n'+'\n'.join('#check @'+n for n in apis))
s=Path('runs/online-subgradient-absolute-migration-20261007/leaves/export-ready-dependencies-v1.lean').read_text(encoding='utf-8')
a=s.index('def targets :');b=s.index('\ndef moduleName',a)
s=s[:a]+'def targets : Array Name := #[\n '+',\n '.join('`'+PRE+n for n in public)+']\n'+s[b:]
s=s.replace('four retained scalar absolute-value proof bodies; direct type/value occurrence only; canary not yet exported','four retained normal-cone production nodes: one definition/three proofs; direct type/value occurrence only; canaries not yet exported')
write(L/'export-ready-dependencies-v1.lean',s)
write(RUN/'API-route-before-proof-v1.json',dict(source_card='ORABONA-V10-EX2.25',mathlib_card='MLIB-ORDER-ALGEBRA and current metric/inner-product APIs; actual compiled signatures required',pinned_probe_APIs=apis,required_files=['research-wiki/mathlib/theorem-cards.md','research-wiki/mathlib-candidates/README.md'],status='project-local retained producers/Mathlib import-candidates until this run probe',new_general_lemma=False,external_dependency=False,pin_change=False,intended_route=load(CONTRACT/'initial-dependency-DAG.json'),whole_canary_proofs=4,whole_canary_definitions=2,new_math_or_tests=0))
generated('readiness-generated-before-use-v1.json',[L/'actual-types-v1.lean',L/'pinned-APIs-v1.lean',L/'export-ready-dependencies-v1.lean',RUN/'common.py',RUN/'run-command.py'])
print('Exact10 declared actualtypes/fullowned-and-borrowed contexts,15 pinnedAPIs and4node readiness exporter prepared; no mathematical editing.')
