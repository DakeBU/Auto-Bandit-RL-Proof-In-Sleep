from common_v1 import *
fixed();assert load(RUN/'public-canary-focused-v1-01-exit.json')['exit_code']==0
TEST='GuessingOSDProbe.'
public_proofs=[PRE+n for n in load(CONTRACT/'headers-v1.json')]
public_defs=[PRE+n for n in re.findall(r'^def\s+(\w+)',PUBLIC.read_text(encoding='utf-8'),re.M)]
testtext=CANARY.read_text(encoding='utf-8')
proofs=[TEST+n for n in re.findall(r'^theorem\s+(\w+)',testtext,re.M)]
defs=[TEST+n for n in re.findall(r'^def\s+(\w+)',testtext,re.M)]
abbr=[TEST+n for n in re.findall(r'^abbrev\s+(\w+)',testtext,re.M)]
assert [len(x) for x in [public_proofs,public_defs,proofs,defs,abbr]]==[12,1,27,6,1]
names=public_proofs+public_defs+proofs+defs+abbr;assert len(set(names))==len(names)==47
write(RUN/'public-named-declarations-v1.json',dict(public_proofs=public_proofs,public_definitions=public_defs,test_proofs=proofs,test_definitions=defs,test_abbreviations=abbr,named_checks=47,new_proofs=0,new_definitions=0))
imp='import Tests.OnlineGuessingSubgradientCanary\n'
write(RUN/'leaves/all-public-types-v1.lean',imp+'\n'.join('#check @'+n for n in names))
write(RUN/'leaves/all-axioms-v1.lean',imp+'\n'.join('#print axioms '+n for n in names))
template=Path('runs/online-guessing-osd-policy-20261007/leaves/export-actual-dependencies-v1.lean').read_text(encoding='utf-8')
start=template.index('def targets : Array Name := #[');end=template.index(']\n',start)+1
template=template[:start]+'def targets : Array Name := #[\n '+',\n '.join('`'+n for n in names)+']'+template[end:]
template=template.replace('Tests.OnlineGuessingSubgradientPolicyCanary','Tests.OnlineGuessingSubgradientCanary')
template=template.replace('Current new4 public proof bodies and whole actual guessing-history canary; compiled Test module environment, direct type/value occurrences only; not full registry or combined-root gate','Existing twelve canonical guessing proof bodies/one loss definition and whole actual canary; compiled TEST module, selected47 actual nodes/direct type-value references, not full registry or combined-root gate; ZERO new mathematics')
write(RUN/'leaves/export-actual-dependencies-v1.lean',template)
pairs=load('runs/online-guessing-osd-20261004/compiled-dependencies.json')['required_proof_value_checks']
pairs.extend([[TEST+'canonical_tie_in_full_interval','BanditRL.OnlineSubgradientDescent.currentSubgradient_mem'],[TEST+'output_one',PRE+'loss_step_clamp'],[TEST+'output_two',PRE+'loss_step_clamp'],[TEST+'four_round_fixed_with_terminal','BanditRL.OnlineSubgradientDescent.regret_fixed'],[TEST+'four_round_bound_rhs_exact',TEST+'four_round_positive_terminal'],[TEST+'all_comparators_four',PRE+'example_2_32'],[TEST+'actual_raw_overshoot_and_clamp',PRE+'loss_step_clamp'],[TEST+'invalid_future_does_not_change_output',PRE+'guessing_prefix'],[TEST+'eventual_one_sided_horizon_family',PRE+'example_2_32_average_eventually']])
write(RUN/'value-pairs-before-first-export-v1.json',dict(required_pairs=pairs,scope='Prespecified direct proof VALUE references, type-only occurrences insufficient; producer/public-terminal/whole nondegenerate canary. Existing16 historical producer pairs reused and nine canary pairs added before first current export.',new_proofs=0))
gate('all-public-types-v1-01','lake','env','lean',RUN/'leaves/all-public-types-v1.lean')
gate('all-axioms-v1-01','lake','env','lean',RUN/'leaves/all-axioms-v1.lean')
gate('compiled-value-graph-v1-01','lake','env','lean','--run',RUN/'leaves/export-actual-dependencies-v1.lean',RUN/'compiled-value-graph-v1.json')
raw=(RUN/'all-axioms-v1-01.log').read_text(encoding='utf-8');assert 'sorryAx' not in raw
matches=re.findall(r"(?:^|\n)'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",raw)
assert len(matches)==47 and {n for n,a in matches}==set(names)
axes={n:[a for a in re.sub(r'\s+','',s).split(',') if a] for n,s in matches}
assert all(set(a)<={'propext','Classical.choice','Quot.sound'} for a in axes.values())
graph=load(RUN/'compiled-value-graph-v1.json');assert len(graph['nodes'])==47 and all(n['has_value'] for n in graph['nodes'])
assert sum(n['kind']=='theorem' for n in graph['nodes'])==39 and sum(n['kind']=='definition' for n in graph['nodes'])==8
actual={(e['source'],e['target']) for e in graph['edges'] if e['kind']=='value' or e['also_in_value']}
for pair in pairs:assert tuple(pair) in actual,pair
guards={'loss_subgradient_positive':['(hxy : y < x)'],'loss_subgradient_negative':['(hxy : x < y)'],'loss_subgradient_bound':['(hg : g ∈ SourceSubdifferential (loss y) x)'],'current_subgradient_bound':['(hx : x ∈ Icc (0 : ℝ) 1)'],'guessing_prefix':['(hη : ∀ s < t, η s = η\' s)','(hy : ∀ s < t, y s = y\' s)'],'example_2_32':['(hx₁ : x₁ ∈ Icc (0 : ℝ) 1)','(hT : 0 < T)','(hy : ∀ t < T, y t ∈ Icc (0 : ℝ) 1)'],'example_2_32_average_eventually':['(hx₁ : x₁ ∈ Icc (0 : ℝ) 1)','(hy : ∀ t, y t ∈ Icc (0 : ℝ) 1)','(hu : u ∈ Icc (0 : ℝ) 1)','(hε : 0 < ε)']}
for n,h in load(CONTRACT/'native-statement-fingerprints-v1.json').items():
 fence=RUN/'native-public-fences'/(n+'-full-v1.json');args=['statement-fence','--declaration',PRE+n,'--file',PUBLIC,'--output',fence]
 for g in guards.get(n,[]):args.extend(['--source-assumption',g])
 native('public-fence-'+n+'-v1',*args);assert load(fence)['statement_hash']==h
 native('public-safe-'+n+'-v1','safe-verify','--fence',fence,'--lean-file',PUBLIC,'--lean-file',CANARY)
jobs=re.search(r'Build completed successfully \((\d+) jobs\)',(RUN/'public-canary-focused-v1-01.log').read_text(encoding='utf-8'));assert jobs
write(RUN/'body-bindings-v1.json',dict(status='Current actual focused/47 named-kernel/25 prespecifiedVALUE/twelveguard checks passed',public_sha256=sha(PUBLIC),canary_sha256=sha(CANARY),public_proofs=12,public_definitions=1,canary_proofs=27,canary_definitions=6,canary_abbreviations=1,named_kernel_checks=47,axes=axes,focused_jobs=int(jobs.group(1)),cached_jobs_included=True,native_guards=12,selected_nodes=47,proof_nodes=39,definition_nodes_including_abbreviation=8,direct_references=len(graph['edges']),required_value_pairs=pairs,new_proofs=0,new_definitions=0,all_complete_headers_and_bodies_unchanged=True,BODY_review='pending',source_package_accepted=False,chapter_complete=False,goal_complete=False))
native('compiled-worker-trial-v1-01','trial-log','--task',TASK,'--role','lower','--kind','build','--status','compiled','--run-id',RUN.name,'--attempt-id','GUESSING-PUBLIC-REUSE-V1','--lean',PUBLIC,'--statement-hash',load(CONTRACT/'native-statement-fingerprints-v1.json')['example_2_32'],'--verifier-evidence',RUN/'body-bindings-v1.json','--harness','hierarchical','--progress-class','retrieval-reuse','--reused-declaration',PRE+'example_2_32','--notes','Existing twelve proof bodies/one loss definition/full27canaries6defs1abbr unchanged;47named-kernel/twelveguards/25directVALUEpairs. ZERO new math. BODY/combined/reader/FINAL/nativeaccepted/PR pending; chapter/Goal incomplete.')
native('candidate-event-v1-01','lifecycle-event','--session',TASK,'--event','candidate','--payload-json',json.dumps(dict(run_id=RUN.name,contract_version=1,body_bindings=RUN.joinpath('body-bindings-v1.json').as_posix(),BODY_review='pending',combined_and_reader='pending',new_proofs=0,chapter_complete=False,goal_complete=False)))
fixed();print('Existing twelve full bodies/current whole canary:47kernel checks/twelveguards/25prespecifiedVALUEpairs; BODY/integration pending.')
