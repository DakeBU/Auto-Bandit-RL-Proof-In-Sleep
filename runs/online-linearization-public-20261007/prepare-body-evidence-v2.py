from common_v2 import *
fixed();assert load(RUN/'public-canary-focused-v2-exit.json')['exit_code']==0
def names(p,pre,k):return [pre+n for n in re.findall(r'^'+k+r'\s+(\w+)',p.read_text(encoding='utf-8'),re.M)]
pp=[PRE+n for n in load(CONTRACT/'headers-v2.json')];pd=names(PUBLIC,PRE,'def');pa=names(PUBLIC,PRE,'abbrev');tp=names(CANARY,TEST,'theorem');td=names(CANARY,TEST,'def');ta=names(CANARY,TEST,'abbrev')
assert [len(x) for x in [pp,pd,pa,tp,td,ta]]==[18,9,3,25,8,2]
allnames=pp+pd+pa+tp+td+ta;assert len(set(allnames))==len(allnames)==65
write(RUN/'public-named-declarations-v2.json',dict(public_proofs=pp,public_definitions=pd,public_abbreviations=pa,test_proofs=tp,test_definitions=td,test_abbreviations=ta,named_checks=65,new_proofs=0,new_definitions=0))
imp='import Tests.OnlineLinearizationCanary\n';write(RUN/'leaves/all-public-types-v2.lean',imp+'\n'.join('#check @'+n for n in allnames));write(RUN/'leaves/all-axioms-v2.lean',imp+'\n'.join('#print axioms '+n for n in allnames))
template=Path('runs/online-guessing-public-20261007/leaves/export-actual-dependencies-v1.lean').read_text(encoding='utf-8');start=template.index('def targets : Array Name := #[');end=template.index(']\n',start)+1
template=template[:start]+'def targets : Array Name := #[\n '+',\n '.join('`'+n for n in allnames)+']'+template[end:]
template=template.replace('Tests.OnlineGuessingSubgradientCanary','Tests.OnlineLinearizationCanary').replace('Existing twelve canonical guessing proof bodies/one loss definition and whole actual canary; compiled TEST module, selected47 actual nodes/direct type-value references, not full registry or combined-root gate; ZERO new mathematics','Existing18 linearization proof bodies/9defs/3abbr and whole canary; compiled TEST environment selected65 actual nodes/direct type-value references, not full registry/combined gate; ZERO new mathematics')
write(RUN/'leaves/export-actual-dependencies-v2.lean',template)
historic=load('runs/online-linearization-20261004/compiled-dependencies.json');pairs=historic['required_proof_value_checks']
extra=[(TEST+'actual_public_comparison',PRE+'regret_comparison'),(TEST+'actual_public_transfer',PRE+'regret_transfer'),(TEST+'actual_public_transfer',TEST+'universal_two'),(TEST+'canonical_producer_instance',PRE+'canonical_regret_comparison'),(TEST+'current_and_future_do_not_change_output',PRE+'output_prefix'),(TEST+'actual_same_linear_run',PRE+'output_linear_run'),(TEST+'actual_strict_slack',TEST+'actual_convex_regret'),(TEST+'actual_strict_slack',TEST+'actual_linear_regret'),(TEST+'zero_horizon_actual_comparison',PRE+'regret_comparison')]
for pair in extra:
 if list(pair) not in pairs:pairs.append(list(pair))
write(RUN/'value-pairs-before-first-export-v2.json',dict(required_pairs=pairs,scope='Prespecified actual direct VALUE references; all historical nineteen producer checks plus distinct whole nondegenerate canary terminal/transfer/strictslack/prefix/T0 calls, before current export. Type-only occurrences insufficient.',new_proofs=0))
gate('all-public-types-v2','lake','env','lean',RUN/'leaves/all-public-types-v2.lean');gate('all-axioms-v2','lake','env','lean',RUN/'leaves/all-axioms-v2.lean');gate('compiled-value-graph-v2','lake','env','lean','--run',RUN/'leaves/export-actual-dependencies-v2.lean',RUN/'compiled-value-graph-v2.json')
raw=(RUN/'all-axioms-v2.log').read_text(encoding='utf-8');assert 'sorryAx' not in raw
matches=re.findall(r"(?:^|\n)'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",raw);assert len(matches)==65 and {n for n,a in matches}==set(allnames)
axes={n:[a for a in re.sub(r'\s+','',s).split(',') if a] for n,s in matches};assert all(set(a)<={'propext','Classical.choice','Quot.sound'} for a in axes.values())
graph=load(RUN/'compiled-value-graph-v2.json');assert len(graph['nodes'])==65 and all(n['has_value'] for n in graph['nodes'])
assert sum(n['kind']=='theorem' for n in graph['nodes'])==43 and sum(n['kind']=='definition' for n in graph['nodes'])==22
actual={(e['source'],e['target']) for e in graph['edges'] if e['kind']=='value' or e['also_in_value']}
for pair in pairs:assert tuple(pair) in actual,pair
for n,h in load(CONTRACT/'native-statement-fingerprints-v2.json').items():
 fence=RUN/'native-public-fences'/(n+'-full-v2.json');args=['statement-fence','--declaration',PRE+n,'--file',PUBLIC,'--output',fence]
 for g in load(Path('docs/contracts/online-linearization-v1')/(n+'.json'))['source_assumptions']:args.extend(['--source-assumption',g])
 native('public-fence-'+n+'-v2',*args);assert load(fence)['statement_hash']==h
 native('public-safe-'+n+'-v2','safe-verify','--fence',fence,'--lean-file',PUBLIC,'--lean-file',CANARY)
jobs=re.search(r'Build completed successfully \((\d+) jobs\)',(RUN/'public-canary-focused-v2.log').read_text(encoding='utf-8'));assert jobs
write(RUN/'body-bindings-v2.json',dict(status='Actual focused/65 named kernel/all18 native guards/prespecifiedVALUE/fullcanary checks passed',public_sha256=sha(PUBLIC),canary_sha256=sha(CANARY),public_proofs=18,public_definitions=9,public_abbreviations=3,canary_proofs=25,canary_definitions=8,canary_abbreviations=2,named_kernel_checks=65,axes=axes,focused_jobs=int(jobs.group(1)),cached_jobs_included=True,native_guards=18,selected_nodes=65,proof_nodes=43,definition_nodes_including_abbreviation=22,direct_references=len(graph['edges']),required_value_pairs=pairs,new_proofs=0,new_definitions=0,all_complete_headers_and_bodies_unchanged=True,BODY_review='pending',source_package_accepted=False,chapter_complete=False,goal_complete=False))
native('compiled-worker-trial-v2','trial-log','--task',TASK,'--role','lower','--kind','build','--status','compiled','--run-id',RUN.name,'--attempt-id','LINEARIZATION-PUBLIC-REUSE-V2','--lean',PUBLIC,'--statement-hash',load(CONTRACT/'native-statement-fingerprints-v2.json')['canonical_regret_comparison'],'--verifier-evidence',RUN/'body-bindings-v2.json','--harness','hierarchical','--progress-class','retrieval-reuse','--reused-declaration',PRE+'canonical_regret_comparison','--notes','Existing18public proofs9defs3abbr/whole25canaryproofs8defs2abbr unchanged. Actual65kernel/18guards/directVALUE; ZERO new math. BODY/combined/reader/FINAL/nativeaccepted/PR pending; chapter/Goal incomplete.')
native('candidate-event-v2','lifecycle-event','--session',TASK,'--event','candidate','--payload-json',json.dumps(dict(run_id=RUN.name,contract_version=2,body_bindings=RUN.joinpath('body-bindings-v2.json').as_posix(),BODY_review='pending',combined_and_reader='pending',new_proofs=0,chapter_complete=False,goal_complete=False)))
fixed();print('Actual existing eighteen bodies and whole canary checked; current BODY/integration pending.')
