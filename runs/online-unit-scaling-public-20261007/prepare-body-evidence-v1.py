from common_v1 import *
fixed();assert load(RUN/'public-canary-focused-v1-exit.json')['exit_code']==0
def names(p,pre,k):return [pre+n for n in re.findall(r'^(?:noncomputable )?'+k+r'\s+(\w+)',p.read_text(encoding='utf-8'),re.M)]
pp=[PRE+n for n in load(CONTRACT/'headers-v1.json')];pd=names(PUBLIC,PRE,'def')+names(PUBLIC,PRE,'abbrev');tp=names(CANARY,TEST,'theorem');td=names(CANARY,TEST,'def');ta=names(CANARY,TEST,'abbrev')
assert [len(x) for x in [pp,pd,tp,td,ta]]==[22,4,30,3,3]
allnames=pp+pd+tp+td+ta;assert len(set(allnames))==len(allnames)==62
write(RUN/'public-named-declarations-v1.json',dict(public_proofs=pp,public_definitions=pd,test_proofs=tp,test_definitions=td,test_abbreviations=ta,named_checks=62,new_proofs=0,new_definitions=0))
imp='import Tests.OnlineUnitScalingCanary\n';write(RUN/'leaves/all-public-types-v1.lean',imp+'\n'.join('#check @'+n for n in allnames));write(RUN/'leaves/all-axioms-v1.lean',imp+'\n'.join('#print axioms '+n for n in allnames))
template=Path('runs/online-linearization-public-20261007/leaves/export-actual-dependencies-v2.lean').read_text(encoding='utf-8');start=template.index('def targets : Array Name := #[');end=template.index(']\n',start)+1
template=template[:start]+'def targets : Array Name := #[\n '+',\n '.join('`'+n for n in allnames)+']'+template[end:]
template=template.replace('Tests.OnlineLinearizationCanary','Tests.OnlineUnitScalingCanary').replace('Existing18 linearization proof bodies/9defs/3abbr and whole canary; compiled TEST environment selected65 actual nodes/direct type-value references, not full registry/combined gate; ZERO new mathematics','Existing22 unit-scaling proof bodies/3 definitions/1 abbreviation and whole canary; compiled TEST environment selected62 actual nodes/direct type-value references, not full registry/combined gate; ZERO new mathematics')
write(RUN/'leaves/export-actual-dependencies-v1.lean',template)
pairs=load('runs/online-unit-scaling-20261004/compiled-dependencies.json')['required_proof_value_checks'];assert len(pairs)==21
extra=[(TEST+a,PRE+b) for a,b in [('dimensions_eta', 'unit_exponents'), ('dimensions_regret', 'regret_unit_exponents'), ('real_scaled_gradient', 'gradient_scaled'), ('positive_eta', 'scaled_eta_positive'), ('correct_path', 'output_scaling'), ('wrong_path', 'wrong_step_output'), ('transformed_selected', 'selected_scaling'), ('transformed_legal', 'legal_feedback_scaling'), ('correct_regret', 'regret_scaling'), ('scaled_energy', 'energy_scaling'), ('scaled_distance', 'distance_square_scaling'), ('actual_sharp_bound', 'regret_fixed_scaled'), ('coarse_bound_invariant', 'upper_bound_scaling'), ('identity_scale', 'output_scaling'), ('zero_horizon_actual_sharp', 'regret_fixed_scaled')]]
extra.extend((TEST+a,TEST+b) for a,b in [('loss_on', 'support'), ('legal', 'support'), ('legal', 'selected_one'), ('selected_one', 'real_linear_gradient'), ('physical_path_difference', 'correct_path'), ('physical_path_difference', 'wrong_path'), ('sharp_rhs', 'positive_old_energy'), ('sharp_rhs', 'positive_terminal')])
for pair in extra:
 if list(pair) not in pairs:pairs.append(list(pair))
assert len(pairs)==44
write(RUN/'value-pairs-before-first-export-v1.json',dict(required_pairs=pairs,scope='Prespecified actual direct proof VALUE constants:21 historical producer checks and23 actual dimensional/chainrule/recursivepath/legal/sharp/boundary canary calls. Type-only occurrences insufficient.',new_proofs=0))
gate('all-public-types-v1','lake','env','lean',RUN/'leaves/all-public-types-v1.lean');gate('all-axioms-v1','lake','env','lean',RUN/'leaves/all-axioms-v1.lean');gate('compiled-value-graph-v1','lake','env','lean','--run',RUN/'leaves/export-actual-dependencies-v1.lean',RUN/'compiled-value-graph-v1.json')
raw=(RUN/'all-axioms-v1.log').read_text(encoding='utf-8');assert 'sorryAx' not in raw
matches=re.findall(r"(?:^|\n)'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",raw);assert len(matches)==62 and {n for n,a in matches}==set(allnames)
axes={n:[a for a in re.sub(r'\s+','',s).split(',') if a] for n,s in matches};assert all(set(a)<={'propext','Classical.choice','Quot.sound'} for a in axes.values())
graph=load(RUN/'compiled-value-graph-v1.json');assert len(graph['nodes'])==62 and all(n['has_value'] for n in graph['nodes'])
assert sum(n['kind']=='theorem' for n in graph['nodes'])==52 and sum(n['kind']=='definition' for n in graph['nodes'])==10
actual={(e['source'],e['target']) for e in graph['edges'] if e['kind']=='value' or e['also_in_value']}
for pair in pairs:assert tuple(pair) in actual,pair
for n,h in load(CONTRACT/'native-statement-fingerprints-v1.json').items():
 fence=RUN/'native-public-fences'/(n+'-full-v1.json');args=['statement-fence','--declaration',PRE+n,'--file',PUBLIC,'--output',fence]
 for g in load(Path('docs/contracts/online-unit-scaling-v1')/(n+'.json'))['source_assumptions']:args.extend(['--source-assumption',g])
 native('public-fence-'+n+'-v1',*args);assert load(fence)['statement_hash']==h
 native('public-safe-'+n+'-v1','safe-verify','--fence',fence,'--lean-file',PUBLIC,'--lean-file',CANARY)
jobs=re.search(r'Build completed successfully \((\d+) jobs\)',(RUN/'public-canary-focused-v1.log').read_text(encoding='utf-8'));assert jobs
write(RUN/'body-bindings-v1.json',dict(status='Actual focused/62named kernel/22native guards/44prespecified VALUE/fullcanary checks passed',public_sha256=sha(PUBLIC),canary_sha256=sha(CANARY),public_proofs=22,public_definitions=4,canary_proofs=30,canary_definitions=3,canary_abbreviations=3,named_kernel_checks=62,axes=axes,focused_jobs=int(jobs.group(1)),cached_jobs_included=True,native_guards=22,selected_nodes=62,proof_nodes=52,definition_nodes_including_abbreviation=10,direct_references=len(graph['edges']),required_value_pairs=pairs,new_proofs=0,new_definitions=0,all_complete_headers_and_bodies_unchanged=True,BODY_review='pending',source_package_accepted=False,chapter_complete=False,goal_complete=False))
native('compiled-worker-trial-v1','trial-log','--task',TASK,'--role','lower','--kind','build','--status','compiled','--run-id',RUN.name,'--attempt-id','UNIT-SCALING-PUBLIC-REUSE-V1','--lean',PUBLIC,'--statement-hash',load(CONTRACT/'native-statement-fingerprints-v1.json')['regret_fixed_scaled'],'--verifier-evidence',RUN/'body-bindings-v1.json','--harness','hierarchical','--progress-class','retrieval-reuse','--reused-declaration',PRE+'regret_fixed_scaled','--notes','Existing22public proofs/3defs1abbr/whole30canaryproofs3defs3abbr unchanged. Actual62kernel/22guards/44directVALUE pairs; ZERO new math. BODY/combined/reader/FINAL/nativeaccepted/PR pending; chapter/Goal incomplete.')
native('candidate-event-v1','lifecycle-event','--session',TASK,'--event','candidate','--payload-json',json.dumps(dict(run_id=RUN.name,contract_version=1,body_bindings=RUN.joinpath('body-bindings-v1.json').as_posix(),BODY_review='pending',combined_and_reader='pending',new_proofs=0,chapter_complete=False,goal_complete=False)))
fixed();print('Actual existing22 bodies/whole canary checked; current BODY/integration pending.')
