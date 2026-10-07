from common_v1 import *
fixed()
defs=load(CONTRACT/'production-definitions-v1.json')
new=load(CONTRACT/'new-public-headers-v1.json')
tests=load(CONTRACT/'planned-canary-headers-v1.json')
testdef=load(CONTRACT/'test-definition-v1.json')['probeTargets']
old=load(CONTRACT/'existing-Mean-headers-v1.json')
contract=(CONTRACT/'contract-v1.md').read_text(encoding='utf-8')
ledger=load('docs/contracts/online-ftl-sharp-v1/chapter-one-source-ledger-draft-v3.json')
ledger['version']='FTL-state-draft-v1';ledger['prior_effective_ledger']=dict(path='docs/contracts/online-ftl-sharp-v1/chapter-one-source-ledger-draft-v3.json',sha256=sha('docs/contracts/online-ftl-sharp-v1/chapter-one-source-ledger-draft-v3.json'),unchanged=True)
ledger['current_package_only']='Two existing FTL source subobligations generalinitial/streaming actual producer; draft9newproof3defs,6testproof1def; no accepted claim'
ledger['new_source_math_closures']=0;ledger['planned_new_source_math_terminals']=2
ledger['prior_source_bound_delivery']=dict(PR=188,head=BASE,receipt='runs/online-ftl-sharp-20261007/delivery-obligations-overlay-v1.json',sha256=sha('runs/online-ftl-sharp-20261007/delivery-obligations-overlay-v1.json'),new_public_math=2)
for row in ledger['maintext_items']:
 if row['source_id'] in ['C1-STABILITY','C1-REFINED-REGRET']:row['current_status']='Two bounded source estimates accepted and delivered in OPEN unmerged PR188; chapter gates remain required'
 if row['source_id']=='C1-FTL':
  row['current_status']='Generalinitial/recursiveproducer exact draftcontract here; previoushalf specialization/causality reused, no new source acceptance yet'
  for sub in row['required_subobligations']:sub['state']='Required; frozen draftcontract in online-ftl-state-v1; CONTRACT/proofs/gates pending'
write(CONTRACT/'chapter-one-source-ledger-draft-v1.json',ledger)
write(CONTRACT/'contract-manifest-v1.json',dict(stage='draft',version=1,source_card_sha256=sha(CONTRACT/'source-card-v1.json'),new_public_headers_sha256=sha(CONTRACT/'new-public-headers-v1.json'),definitions_sha256=sha(CONTRACT/'production-definitions-v1.json'),canary_headers_sha256=sha(CONTRACT/'planned-canary-headers-v1.json'),planned_new_proof_declarations=9,planned_new_definitions=3,existing_Mean_proofs=4,planned_source_subobligation_closures=2,source_package_accepted=False,chapter_complete=False,goal_complete=False))
for folder in ['tasks','conversion-windows','proof-obligations']:
 p=Path(folder)/(TASK+'.md');write(RUN/'snapshots'/('native-scaffold-'+p.as_posix().replace('/','--')),p.read_bytes());p.write_bytes(contract.encode('utf-8'))
write(Path('research-wiki/retrieval-index')/(TASK+'.md'),contract)
write(RUN/'10_upper_director-v1.md','/root staged director: one Chapter1 FTL producer route, current source requires general initialization and no-full-history mean/count state; freeze producer identity rather than assumed certificate. No competing chapters. Two existing subobligations, not nine bookresults; Chapter/Goal not complete.')
write(RUN/'20_architect-v1.md','/root staged architect: alltime empiricalMean recurrence by finite sums with t0 separate; localfirst cancels initial; induction yields exactcount and predictor for alltimes, then prefix/interval/halfconsequences. APIs Finset.sum_range_succ, Nat.cast_add, field_simp/ring, existing meanfeasibility; none copiedupstream theory. One firstready leaf empiricalMean_succ. Generic mean recurrence mathlib-candidate, canonical Mean module with real consumers producer identity and runningaverage retrieval; project-specific state/FTL module owns family. No dependencyupgrade.')
write(RUN/'proof-obligations-draft-v1.json',dict(ready_leaf=PRE+'empiricalMean_succ',terminal=PRE+'ftlState_eq_predict',rows=[dict(name=PRE+n,status='existing compiled proof; current semantic/body review pending') for n in old]+[dict(name=PRE+n,status='frozen draft; no productionbody') for n in new]+[dict(name=TEST+n,status='planned named validation target') for n in tests],mandatory_source_subobligations=2,chapter_total=None,chapter_complete=False,goal_complete=False))
write(RUN/'memory_digest.md','FTL state draft: generalc and local(count,mean) recursion, exact forallstateidentity/strictpast/feasibility/half reuse. Firstupdate separate/alltime empiricalMean recurrence. Generalc endpoint1 gives firsterror1>quarter. No futureoracle/certifiedcost/wholechapter/Goal acceptance.')
for label,args in [('memory-state',['search-memory','running average']),('named-mean',['list-lean-decls','empiricalMean','--statement']),('named-predict',['list-lean-decls','meanPredict','--statement']),('named-state',['list-lean-decls','ftlState','--statement']),('mathlib',['list-mathlib']),('papers',['list-papers']),('weapons',['list-weapons'])]:native('retrieval-'+label+'-v1',*args)
gate('retrieval-actual-Mean-FTL-v1','rg','-n','theorem|def','BanditRLProof/OnlineLearningMean.lean','BanditRLProof/OnlineLearningFTL.lean')
gate('retrieval-actual-sum-v1','rg','-n','prod_range_succ|sum_range_succ','.lake/packages/mathlib/Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean')
write(RUN/'retrieval-decision-v1.json',dict(existing=['empiricalMean_decomposition','empiricalMean_minimizes','empiricalMean_mem','empiricalMean_unique','empiricalMean_update','meanPredict_prefix','meanPredict_regret_refined'],missing='No local general-initial FTL family or genuine mean/count recursive producer found; old recurrence requires positive t',reuse='reuse actual Mean and FTL theorem bodies; add alltime recurrence in Mean, no generic summation duplicates',mathlib_cards=['MLIB-FINSET-SUMS','MLIB-ORDER-ALGEBRA'],mathlib_candidate='Alltime empirical mean recurrence; canonical owning Mean module, not copied projection/probability theory',source_card='ORABONA-V10-C1-FTL-STATE',reference_index_refresh='Not invoked: known finite-sum APIs/unchanged global shared index; scoped native actual declaration searches recorded',conceptual_functor='none-found-with-reason: same scalar squared-loss FTL state representation, no cross-setting transport',no_external_unbuilt_certification=True,no_dependency_upgrade=True))
native('blueprint-own-v1','blueprint-refresh',TASK)
def closed(h,name):
 tail=h[len('theorem '+name):].strip();depth=0
 for j,ch in enumerate(tail):
  if ch in '({[':depth+=1
  elif ch in ')}]':depth-=1
  elif ch==':' and depth==0:
   args=tail[:j].strip();p=tail[j+1:].strip();return ('∀ '+args+',\n    '+p if args else p)
 raise ValueError(name)
aliases={'empiricalMean':'a','ftlPredict':'b','ftlMeanStep':'c','ftlState':'d','meanPredict':'e','probeTargets':'f'}
def neutral(text):
 for n,alias in aliases.items():text=re.sub(r'\b'+n+r'\b',alias,text)
 return text
ctx='import Mathlib.Tactic\nnamespace Neutral\nnoncomputable def a (y : ℕ → ℝ) (n : ℕ) : ℝ := (∑ t ∈ Finset.range n, y t) / n\n'
ctx+='\n'.join(neutral(v) for v in defs.values())+'\nnoncomputable def e (y : ℕ → ℝ) (t : ℕ) : ℝ := if t = 0 then 1/2 else a y t\n'+neutral(testdef)+'\n'
headers=list(old.items())+list(new.items())+list(tests.items())
props='\n\n'.join('def N%02d : Prop :=\n    '%i+neutral(closed(h,n)) for i,(n,h) in enumerate(headers,1))+'\n'
scratch=ctx+props+'\n'.join('#check N%02d'%i for i in range(1,20))+'\nend Neutral\n'
write(RUN/'leaves/neutral-closed-props-v1.lean',scratch);gate('neutral-closed-props-v1','lake','env','lean',RUN/'leaves/neutral-closed-props-v1.lean')
identity='import BanditRLProof.OnlineLearningFTL\n'+scratch+'\ndef propositionOf {P : Prop} (_ : P) : Prop := P\n'
identity+='\n'.join('example : Neutral.N%02d = propositionOf (@%s%s) := by rfl'%(i,PRE,n) for i,n in enumerate(old,1))+'\n'
write(RUN/'leaves/existing-Mean-type-identities-v1.lean',identity);gate('existing-Mean-type-identities-v1','lake','env','lean',RUN/'leaves/existing-Mean-type-identities-v1.lean')
write(RUN/'neutral-map-v1.json',[dict(neutral='N%02d'%i,actual=(PRE if i<=13 else TEST)+n,kind='existing Mean proof' if i<=4 else 'new production target' if i<=13 else 'named validation target') for i,(n,h) in enumerate(headers,1)])
write(RUN/'blind-packet-v1.md','''# Exact neutral propositions
Read ONLY this packet. Requested GPT-6 Astra/medium/no escalation or runtime attestation. Prior actor history must be disclosed; do not lookup source/actual aliases/bodies/old verdicts. Reconstruct EVERY N01–N19 in natural language and LaTeX with seven slots each: objects/quantifiers/assumptions/conclusion/constants-indices/probability-information/boundary. Reconstruct also each actual context definition a–f and the local update's permittedinputs. Distinguish mathematical stream notation from proved strictpast use; d0 stores initial, not a0; positivecounts divide by realcount+1; generalinitial need not have midpointquarter guarantee. Closed tests are numerical validation propositions, not universal source results. No source acceptance decision. Write ONLY blind-decoder-v1.md and blind-decoder-receipt-v1.json in this RUN, actor.task=/root/osd_blind; input/report nestedpath/sha256_raw_bytes, proposition_ids N01–N19, semantic_slots_per_proposition7, prior_history_disclosure, requested_model GPT-6 Astra/requested_reasoning_effort medium/runtime_model_attested false.
```lean
'''+scratch+'\n```\n')
write(RUN/'neutral-type-bindings-v1.json',dict(status='19 exact closed proposition types and 4 existing Mean exact rfl identities compiled; not proof-body completion',blind_packet_sha256=sha(RUN/'blind-packet-v1.md'),new_production_bodies_not_written=True,source_review_pending=True))
fixed();print('Draft actual19 proposition types compiled; CONTRACT/decoder pending; production bodies unwritten.')
