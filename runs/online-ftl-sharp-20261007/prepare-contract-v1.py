from common_v1 import *
fixed()
new={
'meanPredict_initial_stability':'''theorem meanPredict_initial_stability (y : ℕ → ℝ)
    (hy : y 0 ∈ Set.Icc (0 : ℝ) 1) :
    (meanPredict y 0 - y 0)^2 - (empiricalMean y 1 - y 0)^2 ≤ (1 : ℝ) / 4''',
'meanPredict_regret_refined':'''theorem meanPredict_regret_refined (y : ℕ → ℝ) (T : ℕ) (hT : 0 < T)
    (hy : ∀ t < T, y t ∈ Set.Icc (0 : ℝ) 1) :
    (∑ t ∈ Finset.range T, (meanPredict y t - y t)^2) -
      (∑ t ∈ Finset.range T, (empiricalMean y T - y t)^2) ≤
        (1 : ℝ) / 4 + ∑ t ∈ Finset.range (T - 1), 4 / ((t : ℝ) + 2)'''}
plan={
'endpoint_values':'''theorem endpoint_values :
    (meanPredict (fun _ => 0) 0 - 0)^2 - (empiricalMean (fun _ => 0) 1 - 0)^2 = (1 : ℝ) / 4 ∧
    (meanPredict (fun _ => 1) 0 - 1)^2 - (empiricalMean (fun _ => 1) 1 - 1)^2 = (1 : ℝ) / 4 ∧
    (meanPredict (fun _ => 0) 0 - 0)^2 - (empiricalMean (fun _ => 0) 1 - 0)^2 ≤ (1 : ℝ) / 4 ∧
    (meanPredict (fun _ => 1) 0 - 1)^2 - (empiricalMean (fun _ => 1) 1 - 1)^2 ≤ (1 : ℝ) / 4''',
'interior_value':'''theorem interior_value :
    (meanPredict (fun _ => (1 : ℝ) / 2) 0 - 1 / 2)^2 -
      (empiricalMean (fun _ => (1 : ℝ) / 2) 1 - 1 / 2)^2 = 0 ∧
    (meanPredict (fun _ => (1 : ℝ) / 2) 0 - 1 / 2)^2 -
      (empiricalMean (fun _ => (1 : ℝ) / 2) 1 - 1 / 2)^2 < (1 : ℝ) / 4''',
'outside_interval':'''theorem outside_interval :
    (meanPredict (fun _ => 2) 0 - 2)^2 - (empiricalMean (fun _ => 2) 1 - 2)^2 = (9 : ℝ) / 4 ∧
    (meanPredict (fun _ => 2) 0 - 2)^2 - (empiricalMean (fun _ => 2) 1 - 2)^2 > (1 : ℝ) / 4''',
'one_round_refined':'''theorem one_round_refined :
    ((∑ t ∈ Finset.range 1, (meanPredict (fun _ => 0) t - 0)^2) -
      (∑ t ∈ Finset.range 1, (empiricalMean (fun _ => 0) 1 - 0)^2) = (1 : ℝ) / 4) ∧
    ((∑ t ∈ Finset.range 1, (meanPredict (fun _ => 0) t - 0)^2) -
      (∑ t ∈ Finset.range 1, (empiricalMean (fun _ => 0) 1 - 0)^2) ≤
        (1 : ℝ) / 4 + ∑ t ∈ Finset.range (1 - 1), 4 / ((t : ℝ) + 2))''',
'two_round_refined':'''theorem two_round_refined :
    ((∑ t ∈ Finset.range 2, (meanPredict probeTargets t - probeTargets t)^2) -
      (∑ t ∈ Finset.range 2, (empiricalMean probeTargets 2 - probeTargets t)^2) = (3 : ℝ) / 4) ∧
    ((∑ t ∈ Finset.range 2, (meanPredict probeTargets t - probeTargets t)^2) -
      (∑ t ∈ Finset.range 2, (empiricalMean probeTargets 2 - probeTargets t)^2) ≤
        (1 : ℝ) / 4 + ∑ t ∈ Finset.range (2 - 1), 4 / ((t : ℝ) + 2)) ∧
    ((1 : ℝ) / 4 + ∑ t ∈ Finset.range (2 - 1), 4 / ((t : ℝ) + 2)) = 9 / 4''',
'future_independence':'''theorem future_independence :
    meanPredict (fun _ => 0) 1 = meanPredict probeTargets 1 ∧
    (0 : ℝ) ≠ probeTargets 1'''}
write(CONTRACT/'new-public-headers-v1.json',new);write(CONTRACT/'planned-canary-headers-v1.json',plan)
write(CONTRACT/'new-public-fingerprints-v1.json',{n:hashlib.sha256(h.encode()).hexdigest() for n,h in new.items()})
write(CONTRACT/'planned-canary-fingerprints-v1.json',{n:hashlib.sha256(h.encode()).hexdigest() for n,h in plan.items()})
context=PUBLIC.read_text(encoding='utf-8');write(CONTRACT/'existing-context-and-proof-v1.txt',context)
contract='''# FTL sharp first-round and refined regret contract v1

Pinned source ORABONA-V10-C1-FTL-SHARP, arXiv1912.13213v10,21 June2026, SHA256 cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17. Theorem1.3 printed4/PDF16 and its proof printed5/PDF17; source harmonic step printed6/PDF18. Exact source pages and original causal definition are frozen. Existing5 proofs/1 definition are reuse/current semantic review, NOT new mathematics. Exactly2 new genuine unnumbered maintext bounds: initial1/4 and cumulative1/4+4 sum later1/t. Exactly6 validation proofs/1 test definition planned; none of those are additional book source results.

Deterministic scalar guessing game: arbitrary real target stream y, each target in[0,1] at the relevant finite prefix; predict BEFORE revealing that target. Actual predictor meanPredict y0=1/2 and meanPredict y t=empiricalMean y t for t>0; empiricalMean y t averages exactly y0,...,y(t-1). Source y_(t+1) is Lean y t, source x_(t+1) is meanPredict y t, source x*_n is empiricalMean y n for n>0. Empty empiricalMean y0=0 is bookkeeping and is NOT initial prediction1/2. No independence/expectation/high-probability/randomness assumptions and no minimax or full-book completion claim.

Initial source bound needs only first target y0 in[0,1]; it is independent of future y. Exact difference (meanPredict y0-y0)^2-(empiricalMean y1-y0)^2 <=1/4. Current-prefix leader after one observation is y0, so the second term is0. Interval condition yields y0(1-y0)>=0, hence (1/2-y0)^2<=1/4. Endpoints attain1/4, midpoint yields0, target2 outside interval yields9/4; no assumption may be removed silently.

Refined finite-horizon endpoint: T>0 and EVERY t<T target in[0,1]; SAME actual predictor and SAME final empiricalMean yT. Loss difference versus this minimizer is <=1/4+sum over Lean t in range(T-1) of4/((t:real)+2), EXACT source0.25+4 sum(t=2..T)1/t. All denominators t+2>0, no zero division and no T0 terminal claim. T1 tail empty and endpoint sharp. The source min over[0,1] is represented by empiricalMean yT: existing feasibility and global minimization prove it is a feasible minimizer. No assumed per-step regret/stability bound and no arbitrary comparator substituted for the source best-fixed minimum. Existing general Mean dependencies are genuinely compiled APIs, inspected and reused; their separate current module migration remains required, not newly counted here.

Single proof route: real finite-prefix mean update/feasibility -> existing derived stability; produced feasible prefix argmins via empiricalMean_mem/minimizes -> accepted Be-the-Leader comparison; new initial bound + existing later4/(t+1) bound -> sum with first term separated -> same regret endpoint. Actual API Finset.sum_range_succ' separates sum of shifted later terms PLUS initial term, with addition commuted explicitly. All old FTL theorem headers/bodies stay exact original prefix; new two proofs append before namespace end. No new generic finite-sum wrappers, dependency or toolchain changes.

Allowed edits: OWNrun/contract/task/obligations/conversion/retrieval/blueprint/contribution and OWN append-only native rows; owning FTL module ONLY append these two exact proofs; six-header new canary module with one explicit test function and exactly one Tests-root import. Old public library root, all other source modules, existing canaries/pins/old contracts/inventory/previousrun bindings/globalSGB immutable. After CONTRACT/BODY acceptance, only existing FTL sourcecard2/FTL public notes plus two new source-bound cards/notes and route boundary metadata may change. Existing Be-the-Leader/other source cards, all decoded existing math strings/curated IDs/other Books/moduleglobs must stay unchanged. Same shared Lean registry:2new public proof nodes, no per-Book proof tree. Existing/prospective proof dependencies must be verified from actual proof VALUE export; teaching/source/conceptual links are overlays.

Required separate gates: closed exact types+neutral reconstruction+anti-anchored CONTRACT; stabilized/proving only ready leaves; focused bodies and named public+canary checks, original/new full guards and raw fingerprints, axioms/noSorry, nondegenerate canaries, BODY; root/Tests/fullharness, OWN shadow, contributor exactbase and honest main-relative diagnostic, clean current Leanverifiedsite/shared registry with2new proof nodes/current source/reader HTML/pixels; FINAL/native accepted and actual scoped commit/push/draftPR/appattachment/DIRECT. Distinct required reused automated actors GPT-6 Astra/medium, prior history disclosed/no human/external/runtime attestation. No single runtime enforces all paper/source/file/role conventions.

WholeGoalACTIVE/unbudgeted. This source-bound package does not complete Chapter1 or the main-relative integration; current Chapter1 maintext ledger requires separate chapter-wide review. All unresolved9-origin-main migration/integration gaps remain until actual scoped gate proves resolution; retain prior Foundations gap. Chapter2 mandatorytotal null/incomplete;3-16unenumerated; requiredappendices. Historical coverage unchanged. No merge/deploy/main/live/retirement/chapter/Goal completion.
'''
write(CONTRACT/'contract-v1.md',contract)
write(CONTRACT/'conversion-window-v1.md',contract.split('Deterministic scalar')[1].split('Single proof route:')[0])
write(CONTRACT/'semantic-signature-v1.json',dict(objects='Scalar real target stream; interval[0,1], mean predictor and produced empirical-mean minimizers',quantifiers='All y; initial bound only y0; refined all positive T and every t<T bounded',assumptions='Exact relevant interval support and positive refined horizon; actual predictor/argmins produced, no assumed stability',conclusion='Initial loss difference<=1/4; SAME actual-predictor best-fixed regret<=1/4+4 sum later1/t',indices='Source1/Lean0, source x*_n=empiricalMean n only n>0; initial1/2!=emptymean0; range(T-1) denom realt+2',information='Strict-prefix causality, includes arbitrary targets selected after prediction; hindsight current-prefix leaders only auxiliary; deterministic',evidence='Separate review/Lean/axioms/canary/combined/site/FINAL/native/PR; wholeGoalACTIVE'))
write(CONTRACT/'dependency-DAG-v1.json',dict(status='Initial planned DAG; actual VALUE required',terminal=PRE+'meanPredict_regret_refined',edges=[['meanPredict,empiricalMean,interval positivity',PRE+'meanPredict_initial_stability'],[PRE+'empiricalMean_update,empiricalMean_mem',PRE+'meanPredict_stability'],[PRE+'empiricalMean_mem,empiricalMean_minimizes',PRE+'lemma_1_2'],[PRE+'lemma_1_2',PRE+'meanPredict_regret_refined'],[PRE+'meanPredict_initial_stability',PRE+'meanPredict_regret_refined'],[PRE+'meanPredict_stability',PRE+'meanPredict_regret_refined'],['Finset.sum_range_succ\'',PRE+'meanPredict_regret_refined']],source_min_conversion='Feasibility+global minimizing empiricalMean, not exogenous regret certificate'))
write(CONTRACT/'proof-value-obligations-v1.json',dict(required_pairs=[[PRE+'meanPredict_regret_refined',PRE+n] for n in ['meanPredict_initial_stability','meanPredict_stability','lemma_1_2','empiricalMean_mem','empiricalMean_minimizes']]+[[TEST+'endpoint_values',PRE+'meanPredict_initial_stability'],[TEST+'one_round_refined',PRE+'meanPredict_regret_refined'],[TEST+'two_round_refined',PRE+'meanPredict_regret_refined'],[TEST+'future_independence',PRE+'meanPredict_prefix']],prespecified_before_proving=True))
write(CONTRACT/'contract-manifest-v1.json',dict(stage='draft',version=1,source_card_sha256=sha(CONTRACT/'source-card-v1.json'),existing_proof_headers_sha256=sha(CONTRACT/'existing-proof-headers-v1.json'),new_public_headers_sha256=sha(CONTRACT/'new-public-headers-v1.json'),planned_canary_headers_sha256=sha(CONTRACT/'planned-canary-headers-v1.json'),existing_public_proofs=5,existing_public_definitions=1,planned_new_public_proofs=2,planned_new_public_definitions=0,new_named_validation_proofs=6,source_package_accepted=False,chapter_complete=False,goal_complete=False))
for p in [Path('tasks')/(TASK+'.md'),Path('conversion-windows')/(TASK+'.md'),Path('proof-obligations')/(TASK+'.md')]:
 write(RUN/'snapshots'/('native-scaffold-'+p.as_posix().replace('/','--')),p.read_bytes());p.write_bytes((contract+'\n').encode('utf-8'))
write(RUN/'10_upper_director-v1.md','/root same-model staged director: choose single ready Chapter1 FTL route, actual causal predictor/proved feasible argmins, sharpen two explicitly stated maintext bounds; retain old5proofs1definition. No optional agents or later-chapter competitive writes. WholeGoalACTIVE, no chapter acceptance.')
write(RUN/'20_architect-v1.md','/root architect: initial target reduced to(1/2-y0)^2<=1/4; positive-horizon terminal from produced feasible prefix argmins -> lemma1.2 -> actual stability; split first term via Finset.sum_range_succ\', combine initial1/4 and later4/(t+2). Two exact new headers and six test headers frozen. Mathlib-candidate: none; algorithm-specific source endpoints reuse general sum/order APIs, no generic wrappers.')
write(RUN/'proof-obligations-draft-v1.json',dict(required=[dict(name=PRE+n,state='Existing complete proof/current semantic and body review pending') for n in load(CONTRACT/'existing-proof-headers-v1.json')]+[dict(name=PRE+n,state='Exact new source terminal, proof pending') for n in new]+[dict(name=TEST+n,state='Exact named validation target, proof pending') for n in plan],source_mathematical_terminals_planned=2,chapter1_ledger_review_pending=True,chapter2_mandatorytotal=None,chapters3_16='unenumerated',chapter_complete=False,goal_complete=False))
write(RUN/'memory_digest.md','FTL source initial1/4 and refined1/4+4 later harmonic sum; exact causal source/proved feasibleargmins, existingcoarse/log endpoints retained. Two true maintext targets pending. Chapter1ledger/Chapter2incomplete/3-16unenumerated/wholeGoalACTIVE. No accepted claims.')
write(Path('research-wiki/retrieval-index')/(TASK+'.md'),contract)
native('retrieval-memory-meanPredict-v1','search-memory','meanPredict')
native('retrieval-named-meanPredict-v1','list-lean-decls','meanPredict','--statement')
native('retrieval-named-empiricalMean-v1','list-lean-decls','empiricalMean','--statement')
native('retrieval-list-mathlib-v1','list-mathlib');native('retrieval-list-papers-v1','list-papers');native('retrieval-list-weapons-v1','list-weapons')
gate('retrieval-actual-sum-API-v1','rg','-n','prod_range_succ|prod_range_add','.lake/packages/mathlib/Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean')
gate('retrieval-actual-existing-API-v1','rg','-n','meanPredict|empiricalMean|lemma_1_2|harmonic_le_one_add_log','BanditRLProof/OnlineLearningFTL.lean','BanditRLProof/OnlineLearningMean.lean','BanditRLProof/OnlineLearningFoundations.lean','.lake/packages/mathlib/Mathlib/NumberTheory/Harmonic/Bounds.lean')
write(RUN/'retrieval-decision-v1.json',dict(classification='Algorithm-specific two missing source bounds; reuse existing five complete FTL proofs and meanPredict definition, general sums/order imported',new_generic_helpers=0,mathlib_cards=['MLIB-FINSET-SUMS','MLIB-ORDER-ALGEBRA','MLIB-REAL-LOG-SQRT'],cards_read=True,source_card='ORABONA-V10-C1-FTL-SHARP',no_dependency_upgrade=True,no_external_unbuilt_dependency_certification=True,reference_index_refresh='not invoked: no new generic lemma/API; preserve global index instead of unrelated refresh',mathlib_candidate='none: algorithm-specific endpoints; exact Finset APIs reused',conceptual_functor='none-found-with-reason: refinement inside same scalar squared-loss FTL game, no cross-setting transport'))
native('blueprint-own-task-v1','blueprint-refresh',TASK)
owned=load(RUN/'owned-commit-paths-v1.json');owned.append('research-wiki/proof-blueprints/'+TASK+'.md');Path(RUN/'owned-commit-paths-v1.json').write_bytes((json.dumps(owned,indent=2)+'\n').encode())
def closed(h,name):
 tail=h[len('theorem '+name):].strip();depth=0
 for j,ch in enumerate(tail):
  if ch in '({[':depth+=1
  elif ch in ')}]':depth-=1
  elif ch==':' and depth==0:
   args=tail[:j].strip();prop=tail[j+1:].strip();return ('∀ '+args+',\n    '+prop if args else prop)
 raise ValueError(name)
allheaders=list(load(CONTRACT/'existing-proof-headers-v1.json').items())+list(new.items())+list(plan.items())
def neutral(p):return p.replace('meanPredict','b').replace('empiricalMean','a').replace('probeTargets','c')
scratch='''import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic
namespace Neutral
noncomputable def a (y : ℕ → ℝ) (n : ℕ) : ℝ := (∑ t ∈ Finset.range n, y t) / n
noncomputable def b (y : ℕ → ℝ) (t : ℕ) : ℝ := if t = 0 then 1/2 else a y t
def c (t : ℕ) : ℝ := if t = 0 then 0 else 1
'''
scratch+='\n\n'.join('def N%02d : Prop :=\n    '%i+neutral(closed(h,n)) for i,(n,h) in enumerate(allheaders,1))+'\n'
scratch+='\n'.join('#check N%02d'%i for i in range(1,len(allheaders)+1))+'\n#check Finset.sum_range_succ\'\nend Neutral\n'
write(RUN/'leaves/neutral-closed-props-v1.lean',scratch);gate('neutral-closed-props-v1','lake','env','lean',RUN/'leaves/neutral-closed-props-v1.lean')
identity='import BanditRLProof.OnlineLearningFTL\n'+scratch+'\ndef propositionOf {P : Prop} (_ : P) : Prop := P\n'
identity+='\n'.join('example : Neutral.N%02d = propositionOf (@%s%s) := by rfl'%(i,PRE,n) for i,n in enumerate(load(CONTRACT/'existing-proof-headers-v1.json'),1))+'\n'
write(RUN/'leaves/existing-public-type-identities-v1.lean',identity);gate('existing-public-type-identities-v1','lake','env','lean',RUN/'leaves/existing-public-type-identities-v1.lean')
write(RUN/'neutral-map-v1.json',[dict(neutral='N%02d'%i,actual=(PRE if i<=7 else TEST)+n,kind='existing public source proof' if i<=5 else 'new public source-bound target' if i<=7 else 'named validation target') for i,(n,h) in enumerate(allheaders,1)])
write(RUN/'blind-packet-v1.md','''# Source-blind exact propositions
Read ONLY this packet. GPT-6 Astra/medium, no escalation/runtime attestation. Reused actor prior history must be disclosed. Reconstruct EVERY N01-N13 in natural language AND LaTeX; seven semantic slots for EACH: objects, quantifiers, assumptions, conclusion, constants/indices, probability/feedback/information, boundary. a is empty-prefix mean0 but b at0 is1/2, they differ. c is explicit test target sequence. Do not look up source identity, original aliases, theorem bodies or verdicts. Distinguish universal hypotheses, closed numerical tests and prefix agreement. No source/proof acceptance verdict. Write ONLY blind-decoder-v1.md and blind-decoder-receipt-v1.json in this RUN; receipt actor.task=/root/osd_blind; input/report nested path/sha256_raw_bytes, proposition_ids N01-N13, semantic_slots_per_proposition7, prior_history_disclosure; requested_model GPT-6 Astra/requested_reasoning_effort medium/runtime_model_attested false.
```lean
'''+scratch+'\n```\n')
write(RUN/'neutral-type-bindings-v1.json',dict(status='Actual13 closedProps and five existing public exact-type rfl compiled',planned_new_actual_public_and_canary_type_identity_pending=True,blind_packet_sha256=sha(RUN/'blind-packet-v1.md'),source_review_pending=True,new_proofs_not_written=True))
runtime='C:/Users/admin/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/python.exe'
write(RUN/'render-source-child-v1.py',"""from pathlib import Path
import hashlib,json,pypdfium2 as pdfium
p=Path('../research-online-ogd/tmp/pdfs/orabona-v10.pdf')
assert hashlib.sha256(p.read_bytes()).hexdigest()=='cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17'
d=pdfium.PdfDocument(str(p))
for n in [16,17,18]:
 out=Path('runs/online-ftl-sharp-20261007/source-pdf%d-v1.png'%n);assert not out.exists()
 page=d[n-1];page.render(scale=2).to_pil().save(str(out));page.close();print(json.dumps(dict(pdf_page=n,image=str(out),sha256=hashlib.sha256(out.read_bytes()).hexdigest())))
d.close()
""")
gate('source-render-v1',runtime,'-B','-X','utf8',RUN/'render-source-child-v1.py')
fixed();print('Actual13 neutral closed targets and five old type identities compiled; source images rendered. Required decoder/CONTRACT before proving.')
