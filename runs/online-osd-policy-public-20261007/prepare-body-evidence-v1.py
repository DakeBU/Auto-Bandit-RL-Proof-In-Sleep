"""Audit actual whole existing policy and canary values after source stabilization."""
from common_v1 import *
fixed();passed('stabilize-v1-01');passed('public-canary-focused-v1-01')
r=load(RUN/'source-contract-receipt-v1.json');assert sha(r['report'])==r['report_sha256']
reviewed={x['path']:x['sha256'] for x in r['reviewed_files']}
for x in load(RUN/'source-contract-inputs-v1.json')['rows']:assert reviewed[x['path']]==x['sha256'] and sha(x['path'])==x['sha256']
headers=load(CONTRACT/'headers-v1.json');public_proofs=[PRE+n for n in headers]
public_defs=[PRE+n for n in re.findall(r'^def\s+(\w+)',PUBLIC.read_text(encoding='utf-8'),re.M)]
public_abbrevs=[PRE+n for n in re.findall(r'^abbrev\s+(\w+)',PUBLIC.read_text(encoding='utf-8'),re.M)]
tests=[];test_defs=[];test_abbrevs=[];namespace=None
for line in CANARY.read_text(encoding='utf-8').splitlines():
 m=re.match(r'^namespace (\w+)',line)
 if m:namespace=m.group(1)
 m=re.match(r'^(theorem|def|abbrev)\s+(\w+)',line)
 if m:
  assert namespace;{'theorem':tests,'def':test_defs,'abbrev':test_abbrevs}[m.group(1)].append(namespace+'.'+m.group(2))
 if line.startswith('end '):namespace=None
assert [len(x) for x in [public_proofs,public_defs,public_abbrevs,tests,test_defs,test_abbrevs]]==[21,7,2,74,11,7]
targets=public_proofs+public_defs+public_abbrevs+tests+test_defs+test_abbrevs;assert len(targets)==len(set(targets))==122
write(RUN/'public-named-declarations-v1.json',dict(public_proofs=public_proofs,public_definitions=public_defs,public_abbreviations=public_abbrevs,test_proofs=tests,test_definitions=test_defs,test_abbreviations=test_abbrevs,named_checks=122,new_proofs=0,new_definitions=0,all_whole_canary_helpers_counted=True))
write(RUN/'leaves/actual-all-public-types-v1.lean','import Tests.OnlineSubgradientPolicyCanary\n'+'\n'.join('#check @'+n for n in targets))
write(RUN/'leaves/public-all-axioms-v1.lean','import Tests.OnlineSubgradientPolicyCanary\n'+'\n'.join('#print axioms '+n for n in targets))
text=Path('runs/online-osd-public-20261007/leaves/export-public-dependencies-v1.lean').read_text(encoding='utf-8').replace('OnlineSubgradientDescentCanary','OnlineSubgradientPolicyCanary')
start=text.index('def targets : Array Name := #[');end=text.index(']\n',start)+1
text=text[:start]+'def targets : Array Name := #[\n '+',\n '.join('`'+n for n in targets)+']'+text[end:]
text=text.replace('selected53 existing actual OSD production/canary nodes','selected122 existing actual finite-history policy production/canary nodes')
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
assert len(matches)==122 and {n for n,a in matches}==set(targets)
axes={n:[a for a in re.sub(r'\s+','',s).split(',') if a] for n,s in matches};assert all(set(a)<={'propext','Classical.choice','Quot.sound'} for a in axes.values())
g=load(RUN/'compiled-public-graph-v1.json');assert len(g['nodes'])==122 and all(n['has_value'] for n in g['nodes'])
assert sum(n['kind']=='theorem' for n in g['nodes'])==95 and sum(n['kind']=='definition' for n in g['nodes'])==27
pairs={(e['source'],e['target']) for e in g['edges'] if e['kind']=='value' or e['also_in_value']}
required=[['history','BanditRL.OnlineGradientDescent.project'],['history_mem','BanditRL.OnlineGradientDescent.project_spec'],['output_mem',PRE+'history_mem'],['history_prefix',PRE+'history_succ'],['output_prefix',PRE+'history_prefix'],['oracle_feedback',PRE+'output_mem'],['trajectory_finite_loss','BanditRL.OnlineSubgradientDescent.finite_loss'],['trajectory_finite_loss',PRE+'output_mem'],['one_step_chain','BanditRL.OnlineSubgradientDescent.lemma_2_31'],['one_step_chain',PRE+'output_succ'],['one_step',PRE+'one_step_chain'],['regret_fixed',PRE+'one_step_chain'],['regret_fixed_coarse',PRE+'regret_fixed'],['regret_variable_bound',PRE+'one_step'],['regret_variable_bound','BanditRL.OnlineGradientDescent.weighted_potential_sum'],['regret_variable_bound',PRE+'output_mem'],['regret_variable',PRE+'regret_variable_bound'],['regret_variable','Metric.dist_le_diam_of_mem'],['regret_tuned_distance',PRE+'regret_fixed'],['regret_tuned',PRE+'regret_tuned_distance'],['canonicalPolicy_legal','BanditRL.OnlineSubgradientDescent.currentSubgradient_mem'],['canonical_output',PRE+'output_succ'],['canonical_selected',PRE+'canonical_output']]
required=[[PRE+a,b] for a,b in required]+[['OSDPolicyProbe.history_changes_actual_support','OSDPolicyProbe.ga_one'],['OSDPolicyProbe.history_changes_actual_support','OSDPolicyProbe.gb_one'],['OSDPolicyProbe.a_exact_fixed_bound',PRE+'regret_fixed'],['OSDPolicyProbe.offPath_actual_fixed',PRE+'regret_fixed'],['OSDPolicyProbe.offPath_tuned_all_comparators',PRE+'regret_tuned'],['OSDPolicyProbe.harmonic_actual_variable',PRE+'regret_variable_bound'],['OSDPolicyProbe.invalid_future_causal',PRE+'output_prefix'],['OSDPolicyProbe.canonical_invalid_future_bridge',PRE+'canonical_output'],['OSDPolicyProbe.zero_horizon_actual_fixed',PRE+'regret_fixed']]
for p in required:assert tuple(p) in pairs,p
write(RUN/'compiled-dependencies-v1.json',dict(status='passed',selected_nodes=122,proof_nodes=95,definition_nodes_including_nine_abbreviations=27,direct_references=len(g['edges']),required_value_pairs=required,actual_producer_chain_and_nontrivial_canary_calls=True,not_full_registry_graph=True,new_proofs=0))
m=re.search(r'Build completed successfully \((\d+) jobs\)',(RUN/'public-canary-focused-v1-01.log').read_text(encoding='utf-8'));assert m
write(RUN/'public-actual-bindings-v1.json',dict(status='compiled current unchanged existing bodies',module_sha256=sha(PUBLIC),canary_sha256=sha(CANARY),retained_public_proofs=21,retained_public_definitions=7,retained_public_abbreviations=2,retained_test_proofs=74,retained_test_definitions=11,retained_test_abbreviations=7,new_proofs=0,new_definitions=0,named_kernel_checks=122,axes=axes,native_guards=21,all_complete_raw_and_native_headers_unchanged=True,focused_jobs=int(m.group(1)),cached_jobs_included=True,source_package_accepted=False,chapter_complete=False,goal_complete=False))
native('compiled-worker-trial-v1','trial-log','--task',TASK,'--role','lower','--kind','build','--status','compiled','--run-id',RUN.name,'--attempt-id','OSD-POLICY-PUBLIC-REUSE-V1','--lean',PUBLIC,'--statement-hash',load(CONTRACT/'native-statement-fingerprints-v1.json')['regret_tuned'],'--reused-declaration',PRE+'regret_tuned','--verifier-evidence',RUN/'public-actual-bindings-v1.json','--harness','hierarchical','--progress-class','retrieval-reuse','--notes','Actual existing21 proofs7defs2abbr/whole74canaryproofs11defs7abbr;122 names/kernel audits21guards and actual producer/canary value graph. ZERO newly authored proofs/definitions; current BODY/combined/reader/FINAL/native/PR separate pending.')
write(RUN/'proof-obligations-proving-v1.json',dict(stage='proving',existing_public_targets=dict(count=21,state='current body/canary/types/kernel/frozen/value checks passed; distinct BODY pending'),new_proofs=0,required_remaining='Example2.32/linearization/unitanalysis/remainingChapter1/2/nineOTHERChapter1 contracts/necessaryappendices;3-16 unenumerated',chapter_complete=False,goal_complete=False))
fixed();print('Existing21 public/full74canary actual122 kernel checks21 guards/selected122 nodes/'+str(len(g['edges']))+' directrefs/'+str(len(required))+' required valuepairs passed; distinct BODY pending, newproofs0.')
