from common_v1 import *
fixed();assert load(RUN/'public-canary-focused-v1-exit.json')['exit_code']==0
def names(p,pre,k):return [pre+n for n in re.findall(r'^(?:noncomputable )?'+k+r'\s+(\w+)',p.read_text(encoding='utf-8'),re.M)]
pp=[PRE+n for n in load(CONTRACT/'headers-v1.json')];pd=names(PUBLIC,PRE,'def');tp=names(CANARY,TEST,'theorem');td=names(CANARY,TEST,'def');ta=names(CANARY,TEST,'abbrev')
assert [len(x) for x in [pp,pd,tp,td,ta]]==[11,2,23,4,1]
allnames=pp+pd+tp+td+ta;assert len(set(allnames))==len(allnames)==41
write(RUN/'public-named-declarations-v1.json',dict(public_proofs=pp,public_definitions=pd,test_proofs=tp,test_definitions=td,test_abbreviations=ta,named_checks=41,new_proofs=0,new_definitions=0))
imp='import Tests.OnlineOptimalStepCanary\n';write(RUN/'leaves/all-public-types-v1.lean',imp+'\n'.join('#check @'+n for n in allnames));write(RUN/'leaves/all-axioms-v1.lean',imp+'\n'.join('#print axioms '+n for n in allnames))
template=Path('runs/online-linearization-public-20261007/leaves/export-actual-dependencies-v2.lean').read_text(encoding='utf-8');start=template.index('def targets : Array Name := #[');end=template.index(']\n',start)+1
template=template[:start]+'def targets : Array Name := #[\n '+',\n '.join('`'+n for n in allnames)+']'+template[end:]
template=template.replace('Tests.OnlineLinearizationCanary','Tests.OnlineOptimalStepCanary').replace('Existing18 linearization proof bodies/9defs/3abbr and whole canary; compiled TEST environment selected65 actual nodes/direct type-value references, not full registry/combined gate; ZERO new mathematics','Existing11 scalar proof bodies/2 definitions and whole canary; compiled TEST environment selected41 actual nodes/direct type-value references, not full registry/combined gate; ZERO new mathematics')
write(RUN/'leaves/export-actual-dependencies-v1.lean',template)
pairs=load('runs/online-optimal-step-20261004/compiled-dependencies.json')['required_proof_value_checks'];assert len(pairs)==11
extra=[(TEST+a,PRE+b) for a,b in [('positive_optimizer','optimal_positive'),('public_argmin','source_argmin'),('universal','lower_bound'),('unique','optimal_unique'),('tuned','diameter_argmin'),('horizon_one','diameter_argmin'),('zero_distance_no_min','zero_distance_decreases'),('zero_energy_no_min','zero_energy_decreases'),('all_zero','zero_coefficients')]]
extra.extend((TEST+a,TEST+b) for a,b in [('after_one','actual_gradient'),('after_one','actual_projection'),('first_feedback','actual_gradient'),('second_feedback','after_one'),('energy_formula','first_feedback'),('energy_formula','second_feedback'),('same_loss_different_energy','energy_formula')])
for pair in extra:
 if list(pair) not in pairs:pairs.append(list(pair))
assert len(pairs)==27
write(RUN/'value-pairs-before-first-export-v1.json',dict(required_pairs=pairs,scope='Prespecified actual direct proof VALUE constants:11 historical producer checks and16 scalar/zero-boundary/nondegenerate actual same-loss projected OGD eta-energy canary calls. Type-only occurrences insufficient.',new_proofs=0))
gate('all-public-types-v1','lake','env','lean',RUN/'leaves/all-public-types-v1.lean');gate('all-axioms-v1','lake','env','lean',RUN/'leaves/all-axioms-v1.lean');gate('compiled-value-graph-v1','lake','env','lean','--run',RUN/'leaves/export-actual-dependencies-v1.lean',RUN/'compiled-value-graph-v1.json')
raw=(RUN/'all-axioms-v1.log').read_text(encoding='utf-8');assert 'sorryAx' not in raw
matches=re.findall(r"(?:^|\n)'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",raw);assert len(matches)==41 and {n for n,a in matches}==set(allnames)
axes={n:[a for a in re.sub(r'\s+','',s).split(',') if a] for n,s in matches};assert all(set(a)<={'propext','Classical.choice','Quot.sound'} for a in axes.values())
graph=load(RUN/'compiled-value-graph-v1.json');assert len(graph['nodes'])==41 and all(n['has_value'] for n in graph['nodes'])
assert sum(n['kind']=='theorem' for n in graph['nodes'])==34 and sum(n['kind']=='definition' for n in graph['nodes'])==7
actual={(e['source'],e['target']) for e in graph['edges'] if e['kind']=='value' or e['also_in_value']}
for pair in pairs:assert tuple(pair) in actual,pair
for n,h in load(CONTRACT/'native-statement-fingerprints-v1.json').items():
 fence=RUN/'native-public-fences'/(n+'-full-v1.json');args=['statement-fence','--declaration',PRE+n,'--file',PUBLIC,'--output',fence]
 for g in load(Path('docs/contracts/online-optimal-step-v1')/(n+'.json'))['source_assumptions']:args.extend(['--source-assumption',g])
 native('public-fence-'+n+'-v1',*args);assert load(fence)['statement_hash']==h
 native('public-safe-'+n+'-v1','safe-verify','--fence',fence,'--lean-file',PUBLIC,'--lean-file',CANARY)
jobs=re.search(r'Build completed successfully \((\d+) jobs\)',(RUN/'public-canary-focused-v1.log').read_text(encoding='utf-8'));assert jobs
write(RUN/'body-bindings-v1.json',dict(status='Actual focused/41named kernel/11native guards/27prespecified VALUE/fullcanary checks passed',public_sha256=sha(PUBLIC),canary_sha256=sha(CANARY),public_proofs=11,public_definitions=2,canary_proofs=23,canary_definitions=4,canary_abbreviations=1,named_kernel_checks=41,axes=axes,focused_jobs=int(jobs.group(1)),cached_jobs_included=True,native_guards=11,selected_nodes=41,proof_nodes=34,definition_nodes_including_abbreviation=7,direct_references=len(graph['edges']),required_value_pairs=pairs,new_proofs=0,new_definitions=0,all_complete_headers_and_bodies_unchanged=True,BODY_review='pending',source_package_accepted=False,chapter_complete=False,goal_complete=False))
native('compiled-worker-trial-v1','trial-log','--task',TASK,'--role','lower','--kind','build','--status','compiled','--run-id',RUN.name,'--attempt-id','OPTIMAL-STEP-PUBLIC-REUSE-V1','--lean',PUBLIC,'--statement-hash',load(CONTRACT/'native-statement-fingerprints-v1.json')['source_argmin'],'--verifier-evidence',RUN/'body-bindings-v1.json','--harness','hierarchical','--progress-class','retrieval-reuse','--reused-declaration',PRE+'source_argmin','--notes','Existing11public proofs/2defs/whole23canaryproofs4defs1abbr unchanged. Actual41kernel/11guards/27directVALUE pairs; ZERO new math. BODY/combined/reader/FINAL/nativeaccepted/PR pending; chapter/Goal incomplete.')
native('candidate-event-v1','lifecycle-event','--session',TASK,'--event','candidate','--payload-json',json.dumps(dict(run_id=RUN.name,contract_version=1,body_bindings=RUN.joinpath('body-bindings-v1.json').as_posix(),BODY_review='pending',combined_and_reader='pending',new_proofs=0,chapter_complete=False,goal_complete=False)))
fixed();print('Actual existing11 bodies/whole canary checked; current BODY/integration pending.')
