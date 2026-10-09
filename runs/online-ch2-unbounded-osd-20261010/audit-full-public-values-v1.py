from canary_driver import *
import re
canary_guard()
assert load(RUN/'finiteDim_source_lower_bound-focused-inspected-v1.json')['compiled_module_markers']
proof_names=[r['name'] for r in targets.values()]
test_names=[r['name'] for r in canaries['targets']]
definition_names=['BanditRL.OnlineUnboundedOSD.'+n for n in ['powerSteps','phi','switchSlope','switchLoss']]
names=definition_names+proof_names+test_names
probe='import Tests.OnlineUnboundedOSDCanary\n'+''.join('#check @'+n+'\n#print axioms '+n+'\n' for n in names)
probe+='\nnamespace BanditRL.OnlineUnboundedOSDCanary\nopen BanditRL.OnlineUnboundedOSD Set Finset\n'+''.join(row['header'].replace('theorem '+row['name'].rsplit('.',1)[1],'example',1)+' := by\n  exact '+row['name']+'\n' for row in canaries['targets'])+'\nend BanditRL.OnlineUnboundedOSDCanary\n'
write(RUN/'FullSourceCanaryPublicV1.lean',probe)
code,out=capture('full-source-canary-public-v1','lake','env','lean',RUN/'FullSourceCanaryPublicV1.lean')
axioms=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",out,re.S)
empty=re.findall(r"'([^']+)' does not depend on any axioms",out)
assert {n for n,a in axioms}|set(empty)==set(names)
assert all(set(map(str.strip,a.split(',')))<={'propext','Classical.choice','Quot.sound'} for n,a in axioms)
assert 'sorryAx' not in out
write(RUN/'full-source-canary-public-inspected-v1.json',dict(actual_exit=code,raw_stdout=out,axiom_lists=axioms,empty_axiom_lists=empty,complete_test_conjunctions=[7,9],public_definitions=4,public_proof_terminals=11,public_canaries=2,full_examples_elaborated=True,package_accepted=False))
graph=(ROOT/'runs/online-ch2-prescient-source-20261010/export-selected-dependencies-v1.lean').read_text(encoding='utf8')
a=graph.index('def targets : Array Name := #[');b=graph.index('\n\ndef moduleName',a)
graph=graph[:a]+'def targets : Array Name := #[\n'+',\n'.join('`'+n for n in names)+']'+graph[b:]
graph=graph.replace('Tests.OnlinePrescientBregmanSourceCanary','Tests.OnlineUnboundedOSDCanary')
graph=graph.replace('Six frozen production proofs and two complete concrete Test conjunctions plus referenced compiler-generated Test auxiliaries.','Four exact source definitions, eleven frozen production proofs and two complete7/9conjunct Test canaries plus referenced compiler-generated Test auxiliaries.')
write(RUN/'export-selected-dependencies-v1.lean',graph)
capture('selected-graph-export-command-v1','lake','env','lean','--run',RUN/'export-selected-dependencies-v1.lean',RUN/'selected-value-graph-v1.json')
numeric=(ROOT/'runs/online-ch2-prescient-source-20261010/audit-two-numeric-branches-v1.lean').read_text(encoding='utf8')
numeric=numeric.replace('Tests.OnlinePrescientBregmanSourceCanary','Tests.OnlineUnboundedOSDCanary')
a=numeric.index('  for (name,index,required) in #[');b=numeric.index('] do',a)+len('] do')
numeric=numeric[:a]+'''  for (name,index,required) in #[
    (`BanditRL.OnlineUnboundedOSDCanary.scalar_actual_two_rounds,6,`BanditRL.OnlineUnboundedOSD.switching_scalar_regret_identity),
    (`BanditRL.OnlineUnboundedOSDCanary.finiteDim_source_lower_bound,6,`BanditRL.OnlineUnboundedOSD.switching_vector_lower_bound),
    (`BanditRL.OnlineUnboundedOSDCanary.finiteDim_source_lower_bound,7,`BanditRL.OnlineUnboundedOSD.switching_vector_lower_bound),
    (`BanditRL.OnlineUnboundedOSDCanary.finiteDim_source_lower_bound,8,`BanditRL.OnlineUnboundedOSD.theorem_5_4)] do'''+numeric[b:]
write(RUN/'audit-selected-canary-branches-v1.lean',numeric)
capture('selected-canary-branches-command-v1','lake','env','lean','--run',RUN/'audit-selected-canary-branches-v1.lean',RUN/'selected-canary-branches-v1.json')
g=load(RUN/'selected-value-graph-v1.json');nd={n['name']:n for n in g['nodes']}
assert set(names)<=set(nd) and all(nd[n]['has_value'] for n in names)
p='BanditRL.OnlineUnboundedOSD.'
pairs=[(p+'currentSubgradient_affine','BanditRL.OnlineConvex.affine_subdifferential'),(p+'step_affine_fullSpace',p+'currentSubgradient_affine'),(p+'step_affine_fullSpace','BanditRL.OnlineHuber.project_fullSpace'),(p+'iterate_affine_prefix',p+'step_affine_fullSpace'),(p+'switching_scalar_regret_identity',p+'iterate_affine_prefix'),(p+'switching_scalar_regret_identity',"Finset.sum_Ico_Ico_comm'"),(p+'switching_scalar_lower_bound',p+'switching_scalar_regret_identity'),(p+'switching_scalar_lower_bound',p+'phi_range'),(p+'switching_scalar_lower_bound','AntitoneOn.sum_le_integral_Ico'),(p+'switching_scalar_lower_bound','MonotoneOn.integral_le_sum_Ico'),(p+'switching_scalar_lower_bound','integral_rpow'),(p+'switching_vector_lower_bound',p+'switching_scalar_lower_bound'),(p+'switching_vector_lower_bound',p+'iterate_affine_prefix'),(p+'theorem_5_4',p+'switching_vector_lower_bound'),(p+'theorem_5_4',p+'switching_loss_regular'),(p+'theorem_5_4','exists_norm_eq')]
pairs.extend((test_names[0],p+n) for n in ['iterate_affine_prefix','switching_scalar_regret_identity','powerSteps_pos'])
pairs.extend((test_names[1],p+n) for n in ['iterate_affine_prefix','switching_loss_regular','phi_range','switching_vector_lower_bound','theorem_5_4'])
for a,b in pairs:assert b in nd[a]['value_dependencies'],(a,b)
tails=load(RUN/'selected-canary-branches-v1.json')['rows']
assert len(tails)==4 and all(r['required_present'] for r in tails)
capture('safe-verify-help-v1',sys.executable,'-B','-X','utf8','tools/bandit.py','safe-verify','--help')
versions=load(RUN/'full-body-obligations-v1.json')['terminal_evidence']
for row in list(targets.values())+canaries['targets']:
    name=row['name'];short=name.rsplit('.',1)[1];file=TEST if name in test_names else PUBLIC
    version=1 if name in test_names else versions[short][1]
    tag='selector' if short=='currentSubgradient_affine' else short
    native=CONTRACT/((tag if tag=='selector' else short)+'-native-extracted-v'+str(version)+'.json')
    assert native.exists(),native
    capture('safe-verify-'+short+'-command-v1',sys.executable,'-B','-X','utf8','tools/bandit.py','safe-verify','--fence',native.relative_to(ROOT))
write(RUN/'full-public-values-inspected-v1.json',dict(public_nodes=len(names),total_selected_nodes=len(nd),generated_auxiliaries=len(nd)-len(names),coalesced_direct_TYPE_VALUE_presences=len(g['edges']),required_VALUE_pairs=pairs,selected_canary_branches=tails,complete_canary_conjunction_sizes=[7,9],public_definitions=4,proof_terminals=11,full_source_terminal='BanditRL.OnlineUnboundedOSD.theorem_5_4',actual_sources=rows([PUBLIC,TEST]),frozen_statements_unchanged=True,semantic_canary_BODY='required/open',combined_root_Tests_full_harness='required/open',publication_registry_site='required/open',package_accepted=False,chapter_complete=False,whole_Goal='ACTIVE'))
canary_guard()
