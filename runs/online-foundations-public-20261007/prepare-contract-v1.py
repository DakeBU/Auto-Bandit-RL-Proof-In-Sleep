from common_v1 import *
fixed()
header=(CONTRACT/'header-v1.txt').read_text(encoding='utf-8').strip()
plan={
'prefix_minimizers':'''theorem prefix_minimizers :
    ∀ n, 0 < n → n ≤ 2 → ∀ u ∈ (Set.univ : Set Bool),
      (∑ t ∈ Finset.range n, demoLoss t (demoLeader n)) ≤
        ∑ t ∈ Finset.range n, demoLoss t u''',
'instantiated_compare':'''theorem instantiated_compare :
    (∑ t ∈ Finset.range 2, demoLoss t (demoLeader (t + 1))) ≤
      ∑ t ∈ Finset.range 2, demoLoss t (demoLeader 2)''',
'strict_values':'''theorem strict_values :
    (∑ t ∈ Finset.range 2, demoLoss t (demoLeader (t + 1))) = -2 ∧
    (∑ t ∈ Finset.range 2, demoLoss t (demoLeader 2)) = 0 ∧
    (∑ t ∈ Finset.range 2, demoLoss t (demoLeader (t + 1))) <
      ∑ t ∈ Finset.range 2, demoLoss t (demoLeader 2)''',
'zero_horizon':'''theorem zero_horizon {X : Type*} (V : Set X) (loss : ℕ → X → ℝ)
    (leader : ℕ → X) :
    (∑ t ∈ Finset.range 0, loss t (leader (t + 1))) ≤
      ∑ t ∈ Finset.range 0, loss t (leader 0)''',
'one_horizon':'''theorem one_horizon {X : Type*} (loss : ℕ → X → ℝ) (leader : ℕ → X) :
    (∑ t ∈ Finset.range 1, loss t (leader (t + 1))) =
      ∑ t ∈ Finset.range 1, loss t (leader 1)''',
'without_optimality':'''theorem without_optimality :
    let leader : ℕ → Bool := fun n => n = 2
    (∀ n, 0 < n → n ≤ 2 → leader n ∈ (Set.univ : Set Bool)) ∧
    (∑ t ∈ Finset.range 1, demoLoss t true) <
      (∑ t ∈ Finset.range 1, demoLoss t (leader 1)) ∧
    (∑ t ∈ Finset.range 2, demoLoss t (leader (t + 1))) >
      ∑ t ∈ Finset.range 2, demoLoss t (leader 2)''',
'without_feasibility':'''theorem without_feasibility :
    let loss : ℕ → Bool → ℝ := fun t b => if b then if t = 0 then -10 else 5 else 0
    let leader : ℕ → Bool := fun n => n = 2
    let V : Set Bool := {false}
    (∀ n, 0 < n → n ≤ 2 → ∀ u ∈ V,
      (∑ t ∈ Finset.range n, loss t (leader n)) ≤ ∑ t ∈ Finset.range n, loss t u) ∧
    leader 2 ∉ V ∧
    (∑ t ∈ Finset.range 2, loss t (leader (t + 1))) >
      ∑ t ∈ Finset.range 2, loss t (leader 2)'''}
write(CONTRACT/'planned-canary-headers-v1.json',plan)
write(CONTRACT/'planned-canary-fingerprints-v1.json',{n:hashlib.sha256(h.encode()).hexdigest() for n,h in plan.items()})
scope='One existing public Be-the-Leader proof reused; ZERO new public mathematical proofs, definitions, source closures or production registry nodes. Seven new named validation proofs planned, not seven source theorems.'
remaining='Eight OTHER Chapter1 modules still require current semantic/contributor migration; all Chapter1/2 remaining maintext and necessary appendices REQUIRED. Chapter2 mandatory total null/incomplete; Chapters3-16 unenumerated. Whole Goal ACTIVE/unbudgeted; no chapter acceptance, merge/deploy/main/live/retirement.'
contract='''# Be-the-Leader current contract v1

Pinned source Orabona arXiv:1912.13213v10,21 June2026, SHA256 cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17. Lemma1.2 printed4/PDF16, with context Chapter1 printed1-6/PDF13-18 and separate history/exercises printed7/PDF19. Existing historical proof retained byte-for-byte; historical accepted-local Chapter1 status is not a current chapter gate.

For every horizon T, arbitrary ambient type X, subset V, real-valued losses and chosen leader n, assume membership leader n in V and prefix optimality against EVERY u in V at EACH positive n<=T. Then the sum over source current-prefix leaders is at most the sum at final leader T. Existing Lean generalizes source V subset real Euclidean space to arbitrary X; no vector operations, convexity, compactness, topology or probability are used. The source's minimizer existence is represented by supplied leader/membership/argmin data, not proved for arbitrary V/loss. For T>0 these assumptions imply V inhabited; T0 has empty sums and requires no leader0 feasibility. Both membership and prefix argmin are real hypotheses and must not be erased.

Index conversion: source loss ell_t corresponds to Lean loss(t-1); source x*_n corresponds to Lean leader n, for n>=1. Summation Finset.range T uses loss t(leader(t+1)); final uses leader T. These are hindsight current-prefix minimizers INCLUDING the current loss. They are an auxiliary proof sequence and do not constitute a causal prediction strategy; the causal FTL prediction is a distinct source x*_(t-1), whose theorem belongs to a later package. No current-loss-before-output algorithm, universal algorithm existence, no-regret/logarithmic bound, stochastic expectation or minimax guarantee is asserted by this lemma.

Proof route: existing induction on T, remove identical final-round terms, use induction at n and prefix argmin n with feasible leader(n+1). n0 branch is empty. Actual finite-sum successor and order transitivity APIs retrieved. Complete statement/native old-v2 hash frozen, not only conclusion. Seven new named canaries (frozen full headers) validate actual Bool prefix minimizers for losses true:-2 then3 / false:0, changing leaders true thenfalse, comparison -2<=0 and strict -2<0; empty-horizon vacuity, one-round identical sides, concrete failure without optimality and concrete failure with optimality but infeasible final leader. Actual hypotheses produced by finite cases, not assumed desired stability/regret inequalities. New test declarations are neither new public source closures nor duplicated library wrappers.

Allowed edit window: OWNrun/contract/task/conversion/obligations/retrieval/contribution, seven-header new test module and exactly one Tests-root import, OWN append-only native rows. Existing public proof, old Chapter1 canary, ALL other library modules/root/pins/old contracts/inventory/globalSGB immutable. After CONTRACT and BODY acceptance, only the existing Lemma1.2 source card and public note plus online-foundations route boundary metadata may change; preserve all decoded math strings, all other foundation source cards/notes, every curated declaration name, all other Books and module globs. Final reviewer separately binds current reader bytes while original CONTRACT/BODY snapshot bindings stay immutable. Same project, shared declaration registry; no per-Book proof tree/dependency upgrade.

Required evidence: actual closed neutral types and exact source-type identity, distinct mandatory decoder and anti-anchored CONTRACT; ready existing-proof/test proving route; focused named public/test checks, all axioms, full source-assumption/native guards, prespecified actual direct VALUE pairs; BODY; combined root/Tests/full harness, exactbase and honest main-relative contributor gates, own shadow, same registry/URLs, clean Lean-verified local site, actual source/reader pixels, separate FINAL/native acceptance/draftPR delivery. Distinct reused automated actors requested GPT-6 Astra/medium; prior history disclosed, no human/external/runtime attestation. Single-runtime lifecycle events do not enforce all file/source/role conventions.
'''
write(CONTRACT/'contract-v1.md',contract+'\n'+scope+'\n'+remaining)
write(CONTRACT/'conversion-window-v1.md',contract.split('Index conversion:')[1].split('Proof route:')[0].strip()+'\n'+remaining)
write(CONTRACT/'semantic-signature-v1.json',dict(objects='Arbitrary type X/subset V, real losses, chosen hindsight prefix leaders; source real-Euclidean specialization',quantifiers='For all T/loss/leader with each positive prefix n<=T membership and minimization against every feasible u',assumptions='Exactly supplied positive-prefix membership+argmin; no convexity/algorithm-existence assumption',conclusion='Current-prefix leaders cumulative real loss <= SAME final leader cumulative loss',constants_indices='Finite rangeT, source ell_(t+1)=loss t; source x*_n=leader n, final leaderT; T0 extension/one-round equality',information='Auxiliary hindsight sequence includes current loss; no causal prediction or probability theorem',evidence_permissions='Separate source/type/proof/kernel/canary/combined/reader/FINAL/native/PR gates; no external/runtime model attestation',boundary=remaining))
write(CONTRACT/'dependency-DAG-v1.json',dict(kind='Initial dependency graph; actual compiled VALUE export required later',edges=[dict(parent='Finset.sum_range_succ',child=PRE+'lemma_1_2'),dict(parent='OrderTransitivity',child=PRE+'lemma_1_2'),dict(parent='positive-prefix membership+argmin',child=PRE+'lemma_1_2')],future_source_consumer=PRE+'theorem_1_3',future_consumer_not_currently_accepted=True))
write(CONTRACT/'contract-manifest-v1.json',dict(stage='draft',version=1,source_card_sha256=sha(CONTRACT/'source-card-v1.json'),public_header_sha256=sha(CONTRACT/'header-v1.txt'),planned_canary_headers_sha256=sha(CONTRACT/'planned-canary-headers-v1.json'),existing_proof_reuse=True,new_public_math=0,new_named_tests=7,source_package_accepted=False,chapter_complete=False,goal_complete=False))
for p in [Path('tasks')/(TASK+'.md'),Path('conversion-windows')/(TASK+'.md'),Path('proof-obligations')/(TASK+'.md')]:
 write(RUN/'snapshots'/('native-scaffold-'+p.as_posix().replace('/','--')),p.read_bytes());p.write_bytes((contract+'\n'+scope+'\n'+remaining+'\n').encode('utf-8'))
write(RUN/'10_upper_director-v1.md','/root same-model staged director: choose dependency-ready existing Lemma1.2; no optional agents, only required distinct semantic actors. '+scope+' '+remaining)
write(RUN/'20_architect-v1.md','/root architect: original induction/cancellation/prefix-min against feasible finalleader unchanged. Seven full test targets frozen before proving; actual cases produce prefix assumptions. '+scope+' '+remaining)
write(RUN/'proof-obligations-draft-v1.json',dict(required=[dict(name=PRE+'lemma_1_2',state='Existing exact proof; current source/body/public audit pending')]+[dict(name=TEST+n,state='Frozen named validation target; body pending') for n in plan],new_source_math_closures=0,remaining_required=remaining,chapter2_mandatory_total=None,chapter_complete=False,goal_complete=False))
write(RUN/'memory-digest-draft-v1.md',scope+' '+remaining)
gate('actual-API-retrieval-v1','rg','-n','lemma_1_2|sum_range_succ|theorem_1_3|demoLoss|demoLeader',PUBLIC,'BanditRLProof/OnlineLearningFTL.lean','Tests/OnlineLearningChapterOneCanary.lean','.lake/packages/mathlib/Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean')
def closed(h,name):
 tail=h[len('theorem '+name):].strip();depth=0
 for j,ch in enumerate(tail):
  if ch in '({[':depth+=1
  elif ch in ')}]':depth-=1
  elif ch==':' and depth==0:
   args=tail[:j].strip();prop=tail[j+1:].strip();return ('∀ '+args+',\n '+prop if args else prop).replace('Type*','Type u')
 raise ValueError(name)
originals=[closed(header,'lemma_1_2')]+[closed(h,n) for n,h in plan.items()]
def neutral(p):return p.replace('demoLoss','a').replace('demoLeader','b')
scratch='''import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
namespace Neutral
universe u
def a (t : ℕ) (b : Bool) : ℝ := if b then if t = 0 then -2 else 3 else 0
def b (n : ℕ) : Bool := n = 1
'''
scratch+='\n\n'.join('def N%02d : Prop :=\n '%i+neutral(p) for i,p in enumerate(originals,1))+'\n'
scratch+='\n'.join('#check N%02d'%i for i in range(1,9))+'\nend Neutral\n'
write(RUN/'leaves/neutral-closed-props-v1.lean',scratch)
gate('neutral-closed-props-v1','lake','env','lean',RUN/'leaves/neutral-closed-props-v1.lean')
identity='import BanditRLProof.OnlineLearningFoundations\n'+scratch+'''
universe u
def propositionOf {P : Prop} (_ : P) : Prop := P
example : Neutral.N01.{u} = propositionOf (@BanditRL.OnlineLearning.lemma_1_2.{u}) := by rfl
'''
write(RUN/'leaves/exact-public-type-v1.lean',identity);gate('exact-public-type-v1','lake','env','lean',RUN/'leaves/exact-public-type-v1.lean')
write(RUN/'neutral-map-v1.json',[dict(neutral='N%02d'%i,actual=PRE+'lemma_1_2' if i==1 else TEST+list(plan)[i-2],kind='existing source terminal' if i==1 else 'planned named validation test') for i in range(1,9)])
write(RUN/'blind-packet-v1.md','''# Source-blind closed propositions
Read ONLY this packet. Requested GPT-6 Astra/medium, no escalation/runtime attestation. Disclose reused actor prior history. Reconstruct EVERY N01-N08 in natural language and LaTeX, all seven slots: objects/spaces, quantifiers, assumptions, conclusion, constants/indices, operation/information, boundaries. Do not search source identities, original aliases, theorem bodies or previous verdicts. Report each definition's exact scope; a/b are explicit total functions. No theorem/proof acceptance verdict requested.
```lean
'''+scratch+'''
```
Write ONLY blind-decoder-v1.md and blind-decoder-receipt-v1.json in this RUN. Receipt actor.task=/root/osd_blind, input/report nested path and sha256_raw_bytes, proposition_ids N01-N08, semantic_slots_per_proposition7, prior_history_disclosure, requested_model GPT-6 Astra/requested_reasoning_effort medium/runtime_model_attested false. No source/proof/review edits.
''')
write(RUN/'neutral-type-bindings-v1.json',dict(status='Actual eight closedProps and existing public exact-type rfl compiled',public_source_sha256=sha(PUBLIC),packet_sha256=sha(RUN/'blind-packet-v1.md'),planned_canary_headers_sha256=sha(CONTRACT/'planned-canary-headers-v1.json'),canary_actual_type_identity_pending=True,source_review_pending=True))
fixed();print('Source/one full public/seven test targets and actual neutral type checks frozen; distinct decoder/CONTRACT pending.')
