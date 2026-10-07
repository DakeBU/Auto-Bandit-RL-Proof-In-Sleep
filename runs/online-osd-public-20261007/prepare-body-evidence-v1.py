"""Audit actual unchanged complete OSD values and all public canary/helper declarations."""
from common_v2 import *
fixed();passed('stabilize-v1-01');passed('public-canary-focused-v1-01')
headers=load(CONTRACT/'headers-v2.json');public_proofs=[PRE+n for n in headers]
public_defs=[PRE+n for n in re.findall(r'^def\s+(\w+)',PUBLIC.read_text(encoding='utf-8'),re.M)];public_abbrevs=[PRE+n for n in re.findall(r'^abbrev\s+(\w+)',PUBLIC.read_text(encoding='utf-8'),re.M)]
tests=[];test_defs=[];test_abbrevs=[];namespace=None
for line in CANARY.read_text(encoding='utf-8').splitlines():
 m=re.match(r'^namespace (\w+)',line)
 if m:namespace=m.group(1)
 m=re.match(r'^(theorem|def|abbrev)\s+(\w+)',line)
 if m:
  assert namespace;{'theorem':tests,'def':test_defs,'abbrev':test_abbrevs}[m.group(1)].append(namespace+'.'+m.group(2))
 if line.startswith('end '):namespace=None
assert [len(x) for x in [public_proofs,public_defs,public_abbrevs,tests,test_defs,test_abbrevs]]==[15,5,1,24,7,1]
targets=public_proofs+public_defs+public_abbrevs+tests+test_defs+test_abbrevs;assert len(targets)==len(set(targets))==53
write(RUN/'public-named-declarations-v1.json',dict(retained_public_proofs=public_proofs,retained_public_definitions=public_defs,retained_public_abbreviations=public_abbrevs,retained_test_proofs=tests,retained_test_definitions=test_defs,retained_test_abbreviations=test_abbrevs,named_checks=53,new_proofs=0,new_definitions=0,all_whole_canary_helpers_counted=True))
write(RUN/'leaves/actual-all-public-types-v1.lean','import Tests.OnlineSubgradientDescentCanary\n'+'\n'.join('#check @'+n for n in targets))
write(RUN/'leaves/public-all-axioms-v1.lean','import Tests.OnlineSubgradientDescentCanary\n'+'\n'.join('#print axioms '+n for n in targets))
text=Path('runs/online-convex-uncountability-20261007/leaves/export-public-dependencies-v1.lean').read_text(encoding='utf-8').replace('OnlineConvexUncountabilityCanary','OnlineSubgradientDescentCanary')
start=text.index('def targets : Array Name := #[');end=text.index(']\n',start)+1
text=text[:start]+'def targets : Array Name := #[\n '+',\n '.join('`'+n for n in targets)+']'+text[end:]
text=text.replace('selected actual new uncountability proof nodes','selected53 existing actual OSD production/canary nodes; not newly authored proofs')
write(RUN/'leaves/export-public-dependencies-v1.lean',text)
write(RUN/'body-probes-before-first-use-v1.json',dict(rows=[dict(path=p.as_posix(),sha256=sha(p)) for p in [RUN/'leaves/actual-all-public-types-v1.lean',RUN/'leaves/public-all-axioms-v1.lean',RUN/'leaves/export-public-dependencies-v1.lean']],new_source_proofs=False))
gate('actual-all-public-types-v1-01','lake','env','lean',RUN/'leaves/actual-all-public-types-v1.lean')
gate('public-all-axioms-v1-01','lake','env','lean',RUN/'leaves/public-all-axioms-v1.lean')
gate('compiled-public-graph-v1-01','lake','env','lean','--run',RUN/'leaves/export-public-dependencies-v1.lean',RUN/'compiled-public-graph-v1.json')
for n,h in load(CONTRACT/'native-statement-fingerprints-v1.json').items():
 fence=RUN/('native-public-fences/'+n+'.json')
 native('public-fence-'+n+'-v1','statement-fence','--declaration',PRE+n,'--file',PUBLIC,'--output',fence);assert load(fence)['statement_hash']==h
 native('public-safe-'+n+'-v1','safe-verify','--fence',fence,'--lean-file',PUBLIC,'--lean-file',CANARY)
raw=(RUN/'public-all-axioms-v1-01.log').read_text(encoding='utf-8');assert 'sorryAx' not in raw
matches=re.findall(r"(?:^|\n)'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",raw)
assert len(matches)==53 and {n for n,a in matches}==set(targets)
axes={n:[a for a in re.sub(r'\s+','',s).split(',') if a] for n,s in matches};assert all(set(a)<={'propext','Classical.choice','Quot.sound'} for a in axes.values())
g=load(RUN/'compiled-public-graph-v1.json');assert len(g['nodes'])==53 and all(n['has_value'] for n in g['nodes'])
assert sum(n['kind']=='theorem' for n in g['nodes'])==39 and sum(n['kind']=='definition' for n in g['nodes'])==14
pairs={(e['source'],e['target']) for e in g['edges'] if e['kind']=='value' or e['also_in_value']}
required=[['lemma_2_31','BanditRL.OnlineConvex.subgradient_point_finite'],['lemma_2_31','BanditRL.OnlineGradientDescent.proposition_2_11'],['finite_loss',PRE+'currentSubgradient_mem'],['finite_loss','BanditRL.OnlineConvex.subgradient_point_finite'],['iterate_mem','BanditRL.OnlineGradientDescent.project_spec'],['iterate_support',PRE+'currentSubgradient_mem'],['iterate_support',PRE+'iterate_mem'],['iterate_finite_loss',PRE+'finite_loss'],['one_step_chain',PRE+'lemma_2_31'],['one_step_chain',PRE+'iterate_support'],['one_step',PRE+'one_step_chain'],['regret_fixed',PRE+'one_step_chain'],['regret_fixed_coarse',PRE+'regret_fixed'],['regret_variable_bound',PRE+'one_step'],['regret_variable_bound','BanditRL.OnlineGradientDescent.weighted_potential_sum'],['regret_variable',PRE+'regret_variable_bound'],['regret_variable','Metric.dist_le_diam_of_mem'],['regret_tuned_distance',PRE+'regret_fixed'],['regret_tuned',PRE+'regret_tuned_distance']]
required=[[PRE+a,b] for a,b in required]+[['OSDOutsideProbe.arbitrary_current_and_actual_clipping',PRE+'lemma_2_31'],['OSDAlgorithmProbe.fixed_bound_with_terminal',PRE+'regret_fixed'],['OSDAlgorithmProbe.variable_bound_with_terminal',PRE+'regret_variable_bound'],['OSDAlgorithmProbe.tuned_all_comparators',PRE+'regret_tuned'],['OSDAlgorithmProbe.future_inputs_do_not_change_output',PRE+'iterate_prefix']]
for p in required:assert tuple(p) in pairs,p
write(RUN/'compiled-dependencies-v1.json',dict(status='passed',selected_nodes=53,proof_nodes=39,definition_nodes_including_two_abbreviations=14,direct_references=len(g['edges']),required_value_pairs=required,actual_producer_chain_and_canary_calls=True,not_full_registry_graph=True,new_proofs=0))
m=re.search(r'Build completed successfully \((\d+) jobs\)',(RUN/'public-canary-focused-v1-01.log').read_text(encoding='utf-8'));assert m
write(RUN/'public-actual-bindings-v1.json',dict(status='compiled current unchanged existing bodies',module_sha256=sha(PUBLIC),canary_sha256=sha(CANARY),retained_public_proofs=15,retained_public_definitions=5,retained_public_abbreviations=1,retained_test_proofs=24,retained_test_definitions=7,retained_test_abbreviations=1,new_proofs=0,new_definitions=0,named_kernel_checks=53,axes=axes,native_guards=15,raw_metadata_version=2,all_raw_and_native_headers_unchanged=True,focused_jobs=int(m.group(1)),cached_jobs_included=True,source_package_accepted=False,chapter_complete=False,goal_complete=False))
native('compiled-worker-trial-v1','trial-log','--task',TASK,'--role','lower','--kind','build','--status','compiled','--run-id',RUN.name,'--attempt-id','OSD-PUBLIC-REUSE-V1','--lean',PUBLIC,'--statement-hash',load(CONTRACT/'native-statement-fingerprints-v1.json')['regret_tuned'],'--reused-declaration',PRE+'regret_tuned','--verifier-evidence',RUN/'public-actual-bindings-v1.json','--harness','hierarchical','--progress-class','retrieval-reuse','--notes','Actual existing15 public proofs/5defs/1abbrev and whole24 TESTproofs/7defs/1abbrev compile;53 named/kernel audits15 guards and genuine producer value graph. ZERO newly authored proof, current BODY/combined/reader/FINAL/native/PR pending. Same canonical choice only; generic legal finite-history family and chapters remain REQUIRED.')
write(RUN/'proof-obligations-proving-v1.json',dict(stage='proving',public_existing_targets=dict(count=15,state='actual current body/canary/types/kernel/frozen/value gates passed, distinct BODY pending'),new_proofs=0,required_next='Generic legal finite-history policy/Example2.32/linearization/unitanalysis/remaining Chapter1/2/nine OTHERChapter1 gaps/necessary appendices',chapter_complete=False,goal_complete=False))
fixed();print('Actual existing15 proof/5def/1abbrev wholecanary24 proof/7def/1abbrev,53 kernel checks/15 guards/selected53 nodes/'+str(len(g['edges']))+' directrefs/'+str(len(required))+' required valuepairs; current BODY pending/newproofs0.')
