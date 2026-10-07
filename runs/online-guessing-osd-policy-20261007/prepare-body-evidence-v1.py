from common_v1 import *
headers();assert load(RUN/'public-canary-focused-v2-01-exit.json')['exit_code']==0
PRE='BanditRL.OnlineGuessingSubgradientPolicy.';TEST='GuessingPolicyProbe.'
public=[PRE+n for n in load(CONTRACT/'headers-v1.json')]
text=CANARY.read_text(encoding='utf-8')
proofs=[TEST+n for n in re.findall(r'(?m)^theorem (\w+)\b',text)]
defs=[TEST+n for n in re.findall(r'(?m)^def (\w+)\b',text)]
abbreviations=[TEST+n for n in re.findall(r'(?m)^abbrev (\w+)\b',text)]
assert len(public)==4 and not re.findall(r'(?m)^def |^abbrev ',PUBLIC.read_text(encoding='utf-8'))
names=public+proofs+defs+abbreviations;assert len(names)==len(set(names))
write(RUN/'public-named-declarations-v1.json',dict(public_proofs=public,new_public_definitions=0,test_proofs=proofs,test_definitions=defs,test_abbreviations=abbreviations,named_checks=len(names),source_scope='Four new public proof declarations; full actual canary helpers counted, old canonical/policy modules byte-frozen.'))
source='import Tests.OnlineGuessingSubgradientPolicyCanary\n'
write(RUN/'leaves/all-public-types-v1.lean',source+'\n'.join('#check @'+n for n in names))
write(RUN/'leaves/all-axioms-v1.lean',source+'\n'.join('#print axioms '+n for n in names))
template=Path('runs/online-osd-policy-public-20261007/leaves/export-public-dependencies-v1.lean').read_text(encoding='utf-8')
start=template.index('def targets : Array Name := #[');end=template.index(']\n',start)+1
template=template[:start]+'def targets : Array Name := #[\n '+',\n '.join('`'+n for n in names)+']'+template[end:]
template=template.replace('Tests.OnlineSubgradientPolicyCanary','Tests.OnlineGuessingSubgradientPolicyCanary')
template=template.replace('#[{ module := `BanditRLProof }, { module := `Tests.OnlineGuessingSubgradientPolicyCanary }]', '#[{ module := `Tests.OnlineGuessingSubgradientPolicyCanary }]')
template=template.replace('("root_module", toJson "BanditRLProof")','("root_module", toJson "Tests.OnlineGuessingSubgradientPolicyCanary")')
template=template.replace('selected122 existing actual finite-history policy production/canary nodes; not newly authored proofs; direct type/value occurrences only, not full registry graph','Current new4 public proof bodies and whole actual guessing-history canary; compiled Test module environment, direct type/value occurrences only; not full registry or combined-root gate')
write(RUN/'leaves/export-actual-dependencies-v1.lean',template)
pairs=[
[PRE+'selected_bound','BanditRL.OnlineGuessingSubgradient.loss_subgradient_bound'],
[PRE+'step_clamp','BanditRL.OnlineSubgradientPolicy.output_succ'],
[PRE+'step_clamp','BanditRL.OnlineGradientDescent.project_unitInterval'],
[PRE+'example_2_32',PRE+'selected_bound'],
[PRE+'example_2_32','BanditRL.OnlineGuessingSubgradient.loss_on_unitInterval'],
[PRE+'example_2_32','BanditRL.OnlineSubgradientPolicy.regret_tuned'],
[PRE+'example_2_32_average_eventually',PRE+'example_2_32'],
[PRE+'example_2_32_average_eventually','Real.tendsto_sqrt_atTop'],
[PRE+'example_2_32_average_eventually','tendsto_inv_atTop_zero'],
[TEST+'policy_on_absolute','BanditRL.OnlineGuessingSubgradient.loss_subgradient_positive'],
[TEST+'policy_on_absolute','BanditRL.OnlineGuessingSubgradient.loss_subgradient_negative'],
[TEST+'policy_on_absolute','BanditRL.OnlineGuessingSubgradient.loss_subgradient_zero'],
[TEST+'policy_legal',TEST+'policy_on_absolute'],
[TEST+'a_one',PRE+'step_clamp'],[TEST+'b_one',PRE+'step_clamp'],
[TEST+'history_changes_kink_choice',TEST+'ga_two'],[TEST+'history_changes_kink_choice',TEST+'gb_two'],
[TEST+'a_actual_fixed','BanditRL.OnlineSubgradientPolicy.regret_fixed'],[TEST+'a_actual_fixed',TEST+'policy_legal'],
[TEST+'a_selected_bound',PRE+'selected_bound'],
[TEST+'a_tuned_all_comparators',PRE+'example_2_32'],[TEST+'a_tuned_all_comparators',TEST+'policy_legal'],
[TEST+'a_horizon_family_average',PRE+'example_2_32_average_eventually'],[TEST+'a_horizon_family_average',TEST+'policy_legal'],
[TEST+'invalid_future_causal','BanditRL.OnlineSubgradientPolicy.output_prefix'],[TEST+'zero_rate_infeasible_initial',PRE+'step_clamp']]
write(RUN/'value-pairs-before-first-export-v1.json',dict(required_pairs=pairs,scope='Actual producer/control flow/public guarantees and canary use, direct proof VALUE references. Type-only references do not satisfy pairs.',new_public_proofs=4,new_public_definitions=0))
gate('all-public-types-v1-01','lake','env','lean',RUN/'leaves/all-public-types-v1.lean')
gate('all-axioms-v1-01','lake','env','lean',RUN/'leaves/all-axioms-v1.lean')
gate('compiled-value-graph-v1-01','lake','env','lean','--run',RUN/'leaves/export-actual-dependencies-v1.lean',RUN/'compiled-value-graph-v1.json')
raw=(RUN/'all-axioms-v1-01.log').read_text(encoding='utf-8');assert 'sorryAx' not in raw
matches=re.findall(r"(?:^|\n)'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",raw)
assert len(matches)==len(names) and {n for n,a in matches}==set(names)
axes={n:[a for a in re.sub(r'\s+','',s).split(',') if a] for n,s in matches}
assert all(set(a)<={'propext','Classical.choice','Quot.sound'} for a in axes.values())
graph=load(RUN/'compiled-value-graph-v1.json');assert len(graph['nodes'])==len(names) and all(n['has_value'] for n in graph['nodes'])
actual={(e['source'],e['target']) for e in graph['edges'] if e['kind']=='value' or e['also_in_value']}
for pair in pairs:assert tuple(pair) in actual,pair
for n in load(CONTRACT/'headers-v1.json'):
 native('body-safe-'+n+'-v1','safe-verify','--fence',str(RUN/'native-public-fences'/(n+'-full-v1.json')),'--lean-file',PUBLIC,'--lean-file',CANARY)
jobs=re.search(r'Build completed successfully \((\d+) jobs\)',(RUN/'public-canary-focused-v2-01.log').read_text(encoding='utf-8'));assert jobs
write(RUN/'body-bindings-v1.json',dict(status='actual-focused-public-and-whole-canary-types-kernel-values-fences-passed',public_sha256=sha(PUBLIC),canary_sha256=sha(CANARY),public_proofs=4,new_public_definitions=0,canary_proofs=len(proofs),canary_definitions=len(defs),canary_abbreviations=len(abbreviations),named_kernel_checks=len(names),axes=axes,focused_jobs=int(jobs.group(1)),cached_jobs_included=True,native_guards=4,selected_nodes=len(graph['nodes']),selected_proof_nodes=sum(n['kind']=='theorem' for n in graph['nodes']),selected_definition_nodes=sum(n['kind']=='definition' for n in graph['nodes']),direct_references=len(graph['edges']),required_value_pairs=pairs,all_complete_headers_unchanged=True,source_BODY_review='pending',source_package_accepted=False,chapter_complete=False,goal_complete=False))
native('proof-repair-record-v1-01','lifecycle-event','--session',TASK,'--event','repair','--payload-json',json.dumps(dict(run_id=RUN.name,contract_version=1,retained_failures=['first-public-leaf-safe-v1-01','public-canary-focused-v1-01'],repair='Literal sourceguard annotations and canary rewrite/elaboration only; public four types/bodies unchanged; canary full headers unchanged',chapter_complete=False,goal_complete=False)))
native('proof-repair-resumed-v1-01','lifecycle-event','--session',TASK,'--event','proving','--payload-json',json.dumps(dict(run_id=RUN.name,contract_version=1,frozen_statement_version_unchanged=True,actual_verifier=RUN.joinpath('body-bindings-v1.json').as_posix(),chapter_complete=False,goal_complete=False)))
native('candidate-event-v1-01','lifecycle-event','--session',TASK,'--event','candidate','--payload-json',json.dumps(dict(run_id=RUN.name,contract_version=1,body_bindings=RUN.joinpath('body-bindings-v1.json').as_posix(),BODY_review='pending',combined_and_reader_gates='pending',chapter_complete=False,goal_complete=False)))
headers();print('Actual',len(names),'kernel checks /',len(pairs),'prespecified directVALUE pairs passed; distinct BODY/integrated gates pending.')
