from common_v1 import *
fixed()
old=load(CONTRACT/'existing-public-headers-v1.json')
defs={
'embed':'''def embed {X : Type*} (V W : Set X) (hVW : V ⊆ W) : ↥V → ↥W :=
  fun u => ⟨u.val, hVW u.property⟩''',
'sourceV':'def sourceV : Set ℝ := Set.Icc 0 1',
'outputW':'def outputW : Set ℝ := Set.Icc 0 2',
'domainLoss':'def domainLoss : ℕ → ↥outputW → ℝ := fun _ x => -x.val',
'output':'''def output : ℕ → ↥outputW := fun _ => ⟨2, by norm_num [outputW]⟩''',
'referenceOne':'def referenceOne : ↥outputW := ⟨1, by norm_num [outputW]⟩',
'referenceZero':'def referenceZero : ↥outputW := ⟨0, by norm_num [outputW]⟩',
'liftedComparators':'def liftedComparators : Set ↥outputW := {x | x.val ∈ sourceV}'
}
tests={
'domain_gap_sum':'''theorem domain_gap_sum {X : Type*} (V W : Set X) (hVW : V ⊆ W)
    (loss : ℕ → ↥W → ℝ) (prediction : ℕ → ↥W) (u : ↥V) (T : ℕ) :
    comparatorRegret loss prediction (embed V W hVW u) T =
      ∑ t ∈ Finset.range T, (loss t (prediction t) - loss t (embed V W hVW u))''',
'restriction_commutes':'''theorem restriction_commutes {X : Type*} (V W : Set X) (hVW : V ⊆ W)
    (loss : ℕ → ↥W → ℝ) (prediction : ℕ → ↥V) (u : ↥V) (T : ℕ) :
    comparatorRegret (fun t v => loss t (embed V W hVW v)) prediction u T =
      comparatorRegret loss (fun t => embed V W hVW (prediction t)) (embed V W hVW u) T''',
'proper_inclusion':'''theorem proper_inclusion :
    sourceV ⊆ outputW ∧ (2 : ℝ) ∈ outputW ∧ (2 : ℝ) ∉ sourceV''',
'loss_prefix':'''theorem loss_prefix {X : Type*} (W : Set X)
    (loss other : ℕ → ↥W → ℝ) (prediction : ℕ → ↥W) (u : ↥W) (T : ℕ)
    (h : ∀ t < T, ∀ x : ↥W, loss t x = other t x) :
    comparatorRegret loss prediction u T = comparatorRegret other prediction u T''',
'zero_horizon':'''theorem zero_horizon {X : Type*} (W : Set X)
    (loss : ℕ → ↥W → ℝ) (prediction : ℕ → ↥W) (u : ↥W) :
    comparatorRegret loss prediction u 0 = 0''',
'outside_prediction_and_negative_regret':'''theorem outside_prediction_and_negative_regret :
    (output 0).val ∈ outputW ∧ (output 0).val ∉ sourceV ∧
      comparatorRegret domainLoss output referenceOne 2 = -2''',
'same_prediction_two_comparators':'''theorem same_prediction_two_comparators :
    referenceZero.val ∈ sourceV ∧ referenceOne.val ∈ sourceV ∧
      comparatorRegret domainLoss output referenceZero 2 = -4 ∧
      comparatorRegret domainLoss output referenceOne 2 = -2''',
'negative_game_noRegret':'''theorem negative_game_noRegret :
    NoRegret liftedComparators domainLoss output'''
}
write(CONTRACT/'planned-test-definitions-v1.json',defs)
write(CONTRACT/'planned-canary-headers-v1.json',tests)
write(CONTRACT/'canary-statement-fingerprints-v1.json',{n:hashlib.sha256(h.encode()).hexdigest() for n,h in tests.items()})
write(CONTRACT/'test-definition-fingerprints-v1.json',{n:hashlib.sha256(d.encode()).hexdigest() for n,d in defs.items()})
doc='''/-!
# Comparator regret and eventual upper no-regret

Source: Orabona, arXiv:1912.13213v10 (21 June 2026), Chapter 1,
printed page 2 / PDF page 14, comparator-regret definition, Remark 1.1,
and footnote 1. Source round `t + 1` is Lean index `t`.

For outputs in `W` and comparators in `V ⊆ W`, instantiate the shared
carrier `X` with `↥W`, provide losses on `↥W`, and restrict comparators
to `{w : ↥W | w.val ∈ V}`. A loss defined only on `V` cannot be evaluated
at outputs outside `V`. The footnote supplies no generic performance bound.

`comparatorRegret` compares a supplied prediction sequence with one fixed
comparator and keeps the loss sequence explicit (Remark 1.1). It neither
constructs a causal learner nor asserts that a best comparator exists.

`NoRegret` means that, for each fixed feasible comparator and every positive
epsilon, normalized regret is eventually at most epsilon. This upper
condition does not assert existence of an ordinary limit, convergence to
zero, or nonnegative regret. It agrees with the source's displayed limit
inequality when that limit exists. `noRegret_of_vanishing_bound` is a
bound-to-property adapter, whose regret premise must come from a producer.
-/'''
write(CONTRACT/'planned-module-doc-v1.txt',doc)
contract='''# Regret domains and existing API contract v1

Pinned Orabona arXiv1912.13213v10, 21 June 2026, SHA cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17. Printed page 2/PDF14 comparator definition, Remark1.1, footnote1. A bounded SOURCE-MAPPING audit of required C1-REGRET-DIFFERENT-ACTION-COMPARATOR-SETS and complete existing Regret module: two definitions/two proof bodies, zero new production mathematics/registry nodes. Footnote1 supplies no universal W performance theorem. This does not close all of C1-REGRET or the chapter.

Exact typed interpretation: arbitrary carrier X, sets V⊆W, losses ℕ→Subtype W→Real, predictions ℕ→Subtype W, comparator u:Subtype V embedded into W by inclusion. Restrict feasible comparators inside Subtype W to values in V. For source Euclidean vectors instantiate X accordingly; algebraic API's arbitrary carrier is an explicit structural generalization. Source t=1..T is Lean range T/index t+1; T=0 sums empty and normalized quotient uses Lean's total real division, while eventual atTop semantics ignores that finite exceptional index.

The SAME supplied prediction sequence is quantified before every fixed comparator. Loss sequence remains explicit; its prefix suffices to evaluate regret with SAME prediction and comparator, not a causality theorem for arbitrary externally supplied prediction. An arbitrary sequence can depend on future data; comparator API alone certifies no causal producer. Loss must be defined on W, not evaluated outside V-only domain. No probability, filtration, measurability, boundedness, differentiability, compactness, minimizer or nonnegative-regret assumption for finite algebra. Generic best-fixed minimum existence is not guaranteed; actual squared-game mean minimizer is already an independently audited producer and not re-proved here.

NoRegret is forall fixed feasible u, forall epsilon>0, eventually normalized regret<=epsilon. Source displayed limit<=0 is interpreted as an eventual upper condition: agrees when ordinary limit exists, does not supply limit existence/convergence tozero/nonnegative regret. noRegret_of_vanishing_bound assumes an actual eventual normalized regret upper bound tending tozero for each comparator, then combines eventual inequalities. It is a consumer adapter, not an algorithm theorem. New test negative_game_noRegret supplies an ACTUAL derived inequality for explicit test-game, never an assumed desired regret certificate.

Illustrative generalized game ONLY, distinct from source squared guessing: V=[0,1], W=[0,2], output constantly2 without future/comparator input, loss_t(x)=-x defined on W. Proper inclusion witnessed by2 outsideV. Same outputs at horizon2 give regret -4 versus0 and -2 versus1. This validates negative regret and comparator independence; it is no general W performance claim. Domain_gap_sum reuses actual shared sum proof at Subtype W; restriction commutes by exact pullback and embedding; loss-prefix invariance proves evaluation prefix dependency; zero-horizon covers empty sum; actual all-horizon nonpositive gap derives from comparator value<=1 and output2, and uses shared noRegret adapter with bound0. Eight meaningful validation propositions/eight fixture definitions are not eight source results or new production graph nodes.

Frozen headers and full existing module rawbytes recorded; proof/definition bytes and old native hashes remain exact. Allowed future production change only insertion of planned-module-doc-v1.txt immediately before open Filter; reviewed source publication, not mathematics. This is necessary to honestly list a changed production file in contributor manifest; the actual main-relative gate decides whether existing Regret migration gap resolves, without waiver. Conversion window allows new Tests module eight frozen statements/eight fixturedefs, ONE Tests root import after BODY, own contracts/run/task/retrieval/blueprint/contribution/native append entries, and narrowly owned canonical Regret reading/sourcecard/publicnotes/chapter boundary after BODY. Public root, all other Lean/tests/source inventory/old contracts/old evidence/pins/mathlib/global SGB/otherBooks/curated routeIDs/scanner/declaration-boundary config/old reader math stay unchanged. No separate Book library or parser change.

Roles: /root staged director/architect/formalizer/lower; mandatory distinct reused decoder and anti-anchored source reviewer, prior actor histories disclosed, requested GPT-6 Astra/medium; no human/external or runtime model attestation. Contract accepted before proof work; frozen terminal unchanged; actual native CLI records versus file/prompt conventions distinguished. Proof attempt logs, actual header fences, exact types, kernel axioms, public canaries, selected VALUE dependencies, BODY review, root/Tests/full harness/shadow/contributor, clean Leanverified shared registry/site and actual pixels, FINAL review/native accepted/commit/push/draft PR are separate gates.

One required semantic domain mapping may close only after all gates. Chapter1 16 source items but mandatory proof totalnull, logarithmic lower bound required and all other unresolved module/source obligations preserved. Chapter2 incomplete/null,3–16 unenumerated and necessary appendices required; whole Goal ACTIVE. Exact stacked base OPEN draft PR189 head3e473465298ea1ea10b7771608497d34e558fbeb, not main. No merge/live/retirement/chapter completion.
'''
write(CONTRACT/'contract-v1.md',contract)
write(CONTRACT/'semantic-signature-v1.json',dict(objects='Subtype W losses/output; V subset W feasible comparators embedded in W',quantifier_order='same supplied prediction before all fixed comparators; no arbitrary sequence causal claim',assumptions='set inclusion for embedding; finite algebra arbitrary types; adapter eventual bound plus Tendsto0',conclusion='finite difference of sums and eventual epsilon upper NoRegret',normalization='source round t+1 = Lean t; range T; T0 empty; no limit existence or nonnegativity',information='generic API supplied sequence; illustrative constant2 uses neither future nor comparator',boundary='no generic W algorithm/minimum existence/general performance/squared guessing claim'))
write(CONTRACT/'initial-dependency-DAG-v1.json',dict(edges=[['domain_gap_sum','comparatorRegret_eq_sum'],['restriction_commutes','comparatorRegret definition'],['loss_prefix','Finset.sum_congr'],['zero_horizon','empty sum'],['negative_game_noRegret','comparatorRegret_eq_sum'],['negative_game_noRegret','noRegret_of_vanishing_bound'],['negative_game_noRegret','Finset.sum_nonpos']],status='planned dependencies, not compiler proof graph'))
write(CONTRACT/'proof-value-obligations-v1.json',dict(required_pairs=[[TEST+'domain_gap_sum',PRE+'comparatorRegret_eq_sum'],[TEST+'negative_game_noRegret',PRE+'comparatorRegret_eq_sum'],[TEST+'negative_game_noRegret',PRE+'noRegret_of_vanishing_bound']],prespecified_before_proving=True))
ledger=load('docs/contracts/online-ftl-state-v1/chapter-one-source-ledger-draft-v1.json')
assert len(ledger['maintext_items'])==16 and ledger['mandatory_total'] is None
ledger['version']='regret-domains-draft-v1';ledger['prior_effective_ledger']=dict(path='docs/contracts/online-ftl-state-v1/chapter-one-source-ledger-draft-v1.json',sha256=sha('docs/contracts/online-ftl-state-v1/chapter-one-source-ledger-draft-v1.json'),unchanged=True)
ledger['enumeration_status']='16 source items retained; proof-leaf total null; current bounded domain audit draft, no chapter closure'
ledger['current_package_only']='Required W/V semantic domain mapping; no new production proof/definition; complete existing Regret API audit; eight tests not source results'
ledger['new_source_math_closures']=0;ledger['planned_new_source_math_terminals']=0
ledger['prior_FTL_state_delivery']=dict(PR=189,head=BASE,receipt='runs/online-ftl-state-20261007/delivery-obligations-overlay-v1.json',sha256=sha('runs/online-ftl-state-20261007/delivery-obligations-overlay-v1.json'))
for item in ledger['maintext_items']:
 if item['source_id']=='C1-FTL':
  item['current_status']='Two source subobligations delivered OPEN unmerged PR189; full chapter reconciliation still required'
  for sub in item['required_subobligations']:sub['state']='Bounded producer delivered PR189 exact head in prior_FTL_state_delivery; no chapter closure'
 if item['source_id']=='C1-REGRET':
  for sub in item['required_subobligations']:sub['state']='Required; current domain audit draft; contract/proofs/current gates pending'
write(CONTRACT/'chapter-one-source-ledger-draft-v1.json',ledger)
for folder in ['tasks','conversion-windows','proof-obligations']:
 p=Path(folder)/(TASK+'.md');write(RUN/'snapshots'/('native-scaffold-'+p.as_posix().replace('/','--')+'.raw'),p.read_bytes());p.write_bytes(contract.encode())
write(Path('research-wiki/retrieval-index')/(TASK+'.md'),'# Scoped retrieval\n\nActual native searches and Mathlib rg logs in '+RUN.as_posix()+'. Reuse shared comparatorRegret/NoRegret/sum proof/vanishing-bound adapter. No external dependency or new generic guarantee. Complete source/contract in '+CONTRACT.as_posix()+'.')
write(RUN/'10_upper_director-v1.md','/root staged director: bounded required W/V source mapping + current2proof2def audit, preserve all other mandatory obligations; zero new production math.')
write(RUN/'20_architect-v1.md','/root staged architect: typed W loss and V embeddings; reuse actual shared API, scalar outside-domain/negative-regret canaries, exact finite sums and derived nonpositive normalized regret. First ready leaf typed domain_gap_sum; one lower route.')
write(RUN/'memory_digest.md','Draft W/V typed Regret source mapping; epsilon eventual upper semantics; two existing proofs/two definitions exact; eight tests planned, no performance or chapter acceptance.')
write(RUN/'proof-obligations-draft-v1.json',dict(rows=[dict(name=PRE+n,state='existing body and header; current review pending') for n in old]+[dict(name=TEST+n,state='frozen planned test') for n in tests],required_domain_mapping=1,new_production_math=0,chapter_total=None,chapter_complete=False,goal_complete=False))
native('blueprint-own-v1','blueprint-refresh',TASK)
def closed(h,name):
 tail=h[len('theorem '+name):].strip();depth=0
 for j,ch in enumerate(tail):
  if ch in '({[':depth+=1
  elif ch in ')}]':depth-=1
  elif ch==':' and depth==0:
   args=tail[:j].strip();p=tail[j+1:].strip();return ('∀ '+args+',\n    '+p if args else p)
 raise ValueError(name)
aliases={'comparatorRegret':'a','NoRegret':'b','embed':'c','sourceV':'d','outputW':'e','domainLoss':'f','output':'g','referenceOne':'h','referenceZero':'i','liftedComparators':'j'}
def neutral(text):
 for n,alias in aliases.items():text=re.sub(r'\b'+n+r'\b',alias,text)
 return text
ctx='''import Mathlib.Tactic.NormNum
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Instances.Real.Lemmas
open Filter
namespace Neutral
noncomputable def a {X : Type*} (loss : ℕ → X → ℝ) (prediction : ℕ → X) (u : X) (T : ℕ) : ℝ :=
  (∑ t ∈ Finset.range T, loss t (prediction t)) - ∑ t ∈ Finset.range T, loss t u
def b {X : Type*} (V : Set X) (loss : ℕ → X → ℝ) (prediction : ℕ → X) : Prop :=
  ∀ u ∈ V, ∀ ε : ℝ, 0 < ε → ∀ᶠ T in atTop, a loss prediction u T / T ≤ ε
'''
ctx+='\n\n'.join(neutral(d) for d in defs.values())+'\n'
headers=list(old.items())+list(tests.items())
scratch=ctx+'\n\n'.join('def N%02d : Prop :=\n    '%i+neutral(closed(h,n)) for i,(n,h) in enumerate(headers,1))+'\n'+'\n'.join('#check N%02d'%i for i in range(1,11))+'\nend Neutral\n'
write(RUN/'leaves/neutral-closed-props-v1.lean',scratch);gate('neutral-closed-props-v1','lake','env','lean',RUN/'leaves/neutral-closed-props-v1.lean')
identity='import BanditRLProof.OnlineLearningRegret\n'+scratch+'\ndef propositionOf {P : Prop} (_ : P) : Prop := P\n'
identity+='\n'.join('example : Neutral.N%02d = propositionOf (@%s%s) := by rfl'%(i,PRE,n) for i,n in enumerate(old,1))+'\n'
write(RUN/'leaves/existing-public-type-identities-v1.lean',identity);gate('existing-public-type-identities-v1','lake','env','lean',RUN/'leaves/existing-public-type-identities-v1.lean')
write(RUN/'neutral-map-v1.json',[dict(neutral='N%02d'%i,actual=(PRE if i<=2 else TEST)+n,kind='existing public proof' if i<=2 else 'named validation target') for i,(n,h) in enumerate(headers,1)])
write(RUN/'blind-packet-v1.md','''# Exact neutral propositions
Read ONLY this packet. Requested GPT-6 Astra/medium/no escalation; no runtime attestation. Disclose prior actor history and do not lookup source identity, actual aliases, bodies or old verdicts. Reconstruct EVERY N01–N10 in natural language and LaTeX, seven slots each: objects/quantifiers/assumptions/conclusion/constants and indices/probability and information/boundary. Reconstruct context a–j, typed loss domain, embedding/restriction and numerical counter-boundaries. No source acceptance decision. Write ONLY blind-decoder-v1.md and blind-decoder-receipt-v1.json in this RUN, actor.task=/root/osd_blind; input/report nested path/sha256_raw_bytes, proposition_ids N01–N10, semantic_slots_per_proposition7, prior_history_disclosure, requested_model GPT-6 Astra/requested_reasoning_effort medium/runtime_model_attested false.
```lean
'''+scratch+'\n```\n')
write(RUN/'neutral-type-bindings-v1.json',dict(status='10 exact closed types and 2 existing public exact rfl identities compiled; no new test bodies yet',blind_packet_sha256=sha(RUN/'blind-packet-v1.md'),planned_production_math=0,source_review_pending=True))
write(RUN/'source-pixel-review-v1.json',dict(actor='/root',actual_tool='view_image',path=(RUN/'source-pdf14-v1.png').as_posix(),sha256=sha(RUN/'source-pdf14-v1.png'),pdf_page=14,printed_page=2,observed='Original rendered PDF viewed: finite regret formula, displayed limit wording, Remark1.1 and W-superset-V footnote; no generic W theorem',independent_external_review=False))
fixed();print('Actual10 closed proposition types compiled; exact existing2 proof types; draft pending distinct decoder/CONTRACT review, zero test theorem bodies written.')
