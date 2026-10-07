from common_v1 import *
fixed()
context='''import BanditRLProof.OnlineLearningAsymptotic
import Mathlib.Tactic

open Filter
namespace BanditRL.OnlineLearning

/-- Literal ordinary-real-limit reading, kept separate from the shared upper condition. -/
def LimitNoRegret {X : Type*} (V : Set X) (loss : ℕ → X → ℝ)
    (prediction : ℕ → X) : Prop :=
  ∀ u ∈ V, ∃ a : ℝ, a ≤ 0 ∧
    Tendsto (fun T : ℕ => comparatorRegret loss prediction u T / T) atTop (nhds a)

namespace NoRegretCounterexample

/-- A nonnegative horizon potential with alternating normalized values. -/
noncomputable def potential (T : ℕ) : ℝ :=
  if T % 2 = 0 then (T : ℝ) else 0

/-- Actual exogenous real affine losses; no horizon-dependent learner. -/
noncomputable def loss (t : ℕ) (x : ℝ) : ℝ :=
  (potential (t + 1) - potential t) * x

end NoRegretCounterexample
end BanditRL.OnlineLearning
'''
write(CONTRACT/'public-context-v1.lean',context)
entries=[
('noRegret_limit_nonpos','BanditRL.OnlineLearning.', '''theorem noRegret_limit_nonpos {X : Type*} (V : Set X)
    (loss : ℕ → X → ℝ) (prediction : ℕ → X)
    (hNR : NoRegret V loss prediction) (u : X) (hu : u ∈ V) (a : ℝ)
    (hl : Tendsto (fun T : ℕ => comparatorRegret loss prediction u T / T) atTop (nhds a)) :
    a ≤ 0''',[]),
('limitNoRegret_implies_noRegret','BanditRL.OnlineLearning.', '''theorem limitNoRegret_implies_noRegret {X : Type*} (V : Set X)
    (loss : ℕ → X → ℝ) (prediction : ℕ → X)
    (hL : LimitNoRegret V loss prediction) :
    NoRegret V loss prediction''',[]),
('limitNoRegret_iff_noRegret_of_converges','BanditRL.OnlineLearning.', '''theorem limitNoRegret_iff_noRegret_of_converges {X : Type*} (V : Set X)
    (loss : ℕ → X → ℝ) (prediction : ℕ → X)
    (hc : ∀ u ∈ V, ∃ a : ℝ,
      Tendsto (fun T : ℕ => comparatorRegret loss prediction u T / T) atTop (nhds a)) :
    LimitNoRegret V loss prediction ↔ NoRegret V loss prediction''',['noRegret_limit_nonpos','limitNoRegret_implies_noRegret']),
('regret_eq','BanditRL.OnlineLearning.NoRegretCounterexample.', '''theorem regret_eq (T : ℕ) (u : ℝ) :
    comparatorRegret loss (fun _ => 0) u T = -potential T * u''',[]),
('noRegret','BanditRL.OnlineLearning.NoRegretCounterexample.', '''theorem noRegret :
    NoRegret (Set.Icc (0 : ℝ) 1) loss (fun _ => 0)''',['regret_eq']),
('normalized_even','BanditRL.OnlineLearning.NoRegretCounterexample.', '''theorem normalized_even (n : ℕ) :
    comparatorRegret loss (fun _ => 0) 1 (2 * (n + 1)) /
      ((2 * (n + 1) : ℕ) : ℝ) = -1''',['regret_eq']),
('normalized_odd','BanditRL.OnlineLearning.NoRegretCounterexample.', '''theorem normalized_odd (n : ℕ) :
    comparatorRegret loss (fun _ => 0) 1 (2 * n + 1) /
      ((2 * n + 1 : ℕ) : ℝ) = 0''',['regret_eq']),
('no_limit','BanditRL.OnlineLearning.NoRegretCounterexample.', '''theorem no_limit :
    ¬ ∃ a : ℝ, Tendsto
      (fun T : ℕ => comparatorRegret loss (fun _ => 0) 1 T / T) atTop (nhds a)''',['normalized_even','normalized_odd']),
('strict_separation','BanditRL.OnlineLearning.NoRegretCounterexample.', '''theorem strict_separation :
    NoRegret (Set.Icc (0 : ℝ) 1) loss (fun _ => 0) ∧
      ¬ LimitNoRegret (Set.Icc (0 : ℝ) 1) loss (fun _ => 0)''',['noRegret','no_limit'])]
write(CONTRACT/'targets-v1.json',dict(version=1,public_file=PUBLIC.as_posix(),context_sha256=sha(CONTRACT/'public-context-v1.lean'),targets=[dict(id='B%03d'%(i+1),name=pre+name,header=header,header_sha256=hashlib.sha256(header.encode('utf8')).hexdigest(),dependencies=deps) for i,(name,pre,header,deps) in enumerate(entries)],existing_reuse=['BanditRL.OnlineLearning.meanPredict_noRegret','BanditRL.OnlineLearning.noRegret_of_vanishing_bound','BanditRL.OnlineLearning.comparatorRegret_eq_sum'],terminal_edit_forbidden_after_stabilization=True))
card=dict(source_url='https://arxiv.org/pdf/1912.13213v10',source_version='v10, 21 June 2026',source_sha256=PDF_SHA,printed_page=2,pdf_page=14,source_id='C1-NOREGRET',source_display='For every fixed feasible comparator u, lim_{T→∞} Regret_T(u)/T ≤ 0.',source_phrase='Comparator regret is at most sublinear.',actual_existing_property='For every fixed feasible u and epsilon>0, normalized signed comparator regret is eventually at most epsilon.',literal_reading='For each u, an ordinary real limit exists and is nonpositive; its value may depend on u.',mismatch='Ordinary limit existence is stronger than eventual upper epsilon control. The existing NoRegret definition visibly adopts the latter; it does not imply convergence or a zero limit.',proposed_reconciliation='Keep the pinned source and existing definition unchanged. Add LimitNoRegret, prove equivalence under actual per-comparator convergence, and certify a strict separation in the general source real-loss setting. Publish this as an explicit interpretation/delta, not an unqualified literal equivalence.',counterexample=dict(V='[0,1]',prediction='x_t=0, fixed and strict-past causal',potential='F(T)=T for even T, 0 for odd T',loss='ell_t(x)=(F(t+1)-F(t))*x',regret='R_T(u)=-F(T)u',no_regret='All feasible u≥0 give R_T(u)/T≤0 for all T',nonconvergence='u=1: positive even horizons have -1, odd horizons have 0',boundary='Signed unbounded-over-time affine losses are allowed in the cited general paragraph. Not a squared-loss or time-uniform bounded-loss counterexample; no statement that meanPredict itself lacks a limit.'),status='draft-source-correction; separate independent repair review required',chapter_complete=False,goal_complete=False)
write(CONTRACT/'source-card-v1.json',card)
slots=dict(objects='Generic carrier X for bridges; source real Euclidean case is an instance. Concrete obstruction is real [0,1], total real affine losses and the same constant learner.',quantifiers='Per fixed u; per epsilon threshold may depend on u/epsilon. Limit value may depend on u; convergence premise is explicit before iff. Same counterexample loss sequence for all comparators, with comparator1 proving no limit.',assumptions='No convexity/compactness/bounded-loss hypothesis needed for bridges. Counterexample feasible set is nonempty; predictions constant0; all loss values finite/real but magnitude unbounded in t.',conclusion='Upper eventual signed regret versus ordinary-real-limit existence/nonpositivity. Exact iff only under all feasible comparator convergence. Concrete upper property AND negation of literal LimitNoRegret.',constants='No rate/expectation. Normalization by T; Lean total T0 division harmless to atTop, positive even/odd subsequences -1 and0. Source rounds1..T map to Lean0..T-1.',information='Pure deterministic pathwise statement. Constant learner independent of current/future loss and comparator. Existing meanPredict consumes strict past; its upper no-regret proof is revalidated, not converted to unconditional ordinary limit.',boundary='No limsup implementation theorem, no literal equivalence without convergence, no limit-to-zero/nonnegative regret/uniform-u threshold/randomized law, no meanPredict oscillatory or bounded/squared loss counterexample, no source chapter or whole-program completion.')
write(CONTRACT/'semantic-signature-v1.json',slots)
dag={pre+name:deps for name,pre,header,deps in entries};write(CONTRACT/'initial-DAG-v1.json',dict(nodes=dag,first_ready=['noRegret_limit_nonpos','limitNoRegret_implies_noRegret','regret_eq'],single_lower_route=True,import_ready=['NoRegret','comparatorRegret','le_of_tendsto','tendsto_order','Finset.sum_range_succ','Filter.tendsto_atTop_mono','Tendsto.unique']))
intent='''Source: Orabona v10 printed2/PDF14, comparator-wise no-regret paragraph. Pin source; preserve upper NoRegret and ordinary-limit display as distinct objects. Proposed contract has nine fixed public proofs/three new definitions. It closes a source reconciliation/strict-obstruction dependency, not a blanket Chapter1 or literal meanPredict convergence result. Six main-relative contributor gaps remain required; this package will cover/revalidate Asymptotic, with other five and best-minimum left open.

Conversion authority: no frozen target edit during proof repair. Newversion and distinct source review for any change in assumptions or terminal. Draft->stabilized requires blind reconstruction AND anti-anchored source review plus a separately explicit proposed correction review. Proving selects imported-ready leaves. Candidate requires actual bodies, retrieval, frozen hashes, named canaries and kernel audits. Accepted additionally requires combined root/Tests/fullharness, precise source/reader review, native shadow and site/registry checks, contributor gate and reviewable PR. No single runtime enforces every step.

Source card C1-NOREGRET. Mathlib cards MLIB-ASYMPTOTICS, MLIB-ORDER-ALGEBRA and MLIB-FINSET-SUMS; actual pinned APIs le_of_tendsto/tendsto_order/tendsto_atTop_mono/Tendsto.unique/sum_range_succ. No compatible missing external import needed; no toolchain change. Core limit facts imported; NoRegret wrappers project-local, not new generic topology lemmas. Consumers: per-comparator source display reconciliation and true separation/ordinary-limit canaries; actual meanPredict upper property reused. No proof-weapon theorem dependency or generic regret duplication.

Edit window: new public/test module, this RUN/CONTRACT, this task's task/conversion/obligation/blueprint/retrieval files and three append-only native journals/MANIFEST. Later stabilization may append one root/Test import, one new source reader card and new notes/exact module route binding, plus a new contribution manifest. Old public sources, accepted PR191/190 evidence, oldreader entries/curated IDs, scanner/pins/globalSGB/coverage remain unchanged. Generated site only under tmp; no website/_site mutation.

Root performs staged director, architect/formalizer and one worker route. Reuse distinct required osd_blind and source_reviewer; do not claim independent human/external/runtime review. Source correction is not accepted until separate review. Mandatory total/chapter proof counts remain unknown, not zero. Total Goal active; no merge/deploy/main/live/retirement.
'''
write(CONTRACT/'contract-v1.md',intent)
for folder in ['tasks','conversion-windows','proof-obligations']:
 p=Path(folder)/(TASK+'.md');p.write_bytes(('# '+TASK+'\n\n'+intent+'\nNine frozen obligations remain draft/unproved. Refer to targets-v1.json, semantic-signature-v1.json and initial-DAG-v1.json.\n').encode('utf8'))
for folder in ['proof-blueprints','research-wiki/retrieval-index']:
 write(Path(folder)/(TASK+'.md'),intent)
write(RUN/'10_director.md','Select one C1 NoRegret source-semantic hinge before other chapter work. True limit bridge plus explicit legal counterexample closes this hinge. Leave all other mandatory source obligations visible. '+intent)
write(RUN/'20_architect.md','Imported-ready leaves: use le_of_tendsto and epsilon=a/2 for a≤0; use tendsto_order for literal->upper. Induct on finite loss sums to telescope F(T)u, not assume desired regret. Nonnegative F and u give upper condition; normalized positive even/odd subsequences have different values, Tendsto.unique forbids a common real limit. Convergence-premise iff uses the two bridges. '+intent)
neutral='''import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic
open Filter
universe v
namespace NeutralPacket
noncomputable def r {X : Type v} (f : ℕ → X → ℝ) (p : ℕ → X) (u : X) (N : ℕ) : ℝ :=
  (∑ t ∈ Finset.range N, f t (p t)) - ∑ t ∈ Finset.range N, f t u
def upper {X : Type v} (V : Set X) (f : ℕ → X → ℝ) (p : ℕ → X) : Prop :=
  ∀ u ∈ V, ∀ e : ℝ, 0 < e → ∀ᶠ N in atTop, r f p u N / N ≤ e
def limit {X : Type v} (V : Set X) (f : ℕ → X → ℝ) (p : ℕ → X) : Prop :=
  ∀ u ∈ V, ∃ a : ℝ, a ≤ 0 ∧ Tendsto (fun N : ℕ => r f p u N / N) atTop (nhds a)
noncomputable def h (N : ℕ) : ℝ := if N % 2 = 0 then (N : ℝ) else 0
noncomputable def f (t : ℕ) (x : ℝ) : ℝ := (h (t+1) - h t) * x
noncomputable def q (y : ℕ → ℝ) (t : ℕ) : ℝ :=
  if t = 0 then 1/2 else (∑ i ∈ Finset.range t, y i) / t
def B001 : Prop := ∀ (X : Type v) (V : Set X) (f : ℕ → X → ℝ) (p : ℕ → X),
  upper V f p → ∀ u ∈ V, ∀ a : ℝ,
    Tendsto (fun N : ℕ => r f p u N / N) atTop (nhds a) → a ≤ 0
def B002 : Prop := ∀ (X : Type v) (V : Set X) (f : ℕ → X → ℝ) (p : ℕ → X),
  limit V f p → upper V f p
def B003 : Prop := ∀ (X : Type v) (V : Set X) (f : ℕ → X → ℝ) (p : ℕ → X),
  (∀ u ∈ V, ∃ a : ℝ, Tendsto (fun N : ℕ => r f p u N / N) atTop (nhds a)) →
    (limit V f p ↔ upper V f p)
def B004 : Prop := ∀ (N : ℕ) (u : ℝ), r f (fun _ => 0) u N = -h N * u
def B005 : Prop := upper (Set.Icc (0 : ℝ) 1) f (fun _ => 0)
def B006 : Prop := ∀ n : ℕ, r f (fun _ => 0) 1 (2*(n+1)) / ((2*(n+1) : ℕ) : ℝ) = -1
def B007 : Prop := ∀ n : ℕ, r f (fun _ => 0) 1 (2*n+1) / ((2*n+1 : ℕ) : ℝ) = 0
def B008 : Prop := ¬ ∃ a : ℝ, Tendsto (fun N : ℕ => r f (fun _ => 0) 1 N / N) atTop (nhds a)
def B009 : Prop := upper (Set.Icc (0 : ℝ) 1) f (fun _ => 0) ∧ ¬ limit (Set.Icc (0 : ℝ) 1) f (fun _ => 0)
def B010 : Prop := ∀ y : ℕ → ℝ, (∀ t, y t ∈ Set.Icc (0 : ℝ) 1) →
  upper (Set.Icc (0 : ℝ) 1) (fun t x => (x-y t)^2) (q y)
def B011 : Prop := ∀ (X : Type v) (V : Set X) (f : ℕ → X → ℝ) (p : ℕ → X) (b : X → ℕ → ℝ),
  (∀ u ∈ V, ∀ᶠ N in atTop, r f p u N / N ≤ b u N) →
  (∀ u ∈ V, Tendsto (b u) atTop (nhds 0)) → upper V f p
def B012 : Prop := ∀ (X : Type v) (f : ℕ → X → ℝ) (p : ℕ → X) (u : X) (N : ℕ),
  r f p u N = ∑ t ∈ Finset.range N, (f t (p t) - f t u)
end NeutralPacket
'''
write(RUN/'neutral-packet-v1.lean',neutral)
gate('neutral-context-elaboration-v1','lake','env','lean',RUN/'neutral-packet-v1.lean')
gate('proposed-context-elaboration-v1','lake','env','lean',CONTRACT/'public-context-v1.lean')
write(RUN/'neutral-inputs-v1.json',dict(packet=(RUN/'neutral-packet-v1.lean').as_posix(),packet_sha256=sha(RUN/'neutral-packet-v1.lean'),scope='12 proposition targets and six explicit contextual definitions; reconstruct only, no source/proof/acceptance claim.',source_identity_supplied=False,requested_model='GPT-6 Astra',requested_reasoning_effort='medium',runtime_attested=False))
write(RUN/'source-statement-fingerprint-v1.json',dict(source_sha256=PDF_SHA,source_card_sha256=sha(CONTRACT/'source-card-v1.json'),targets_sha256=sha(CONTRACT/'targets-v1.json'),context_sha256=sha(CONTRACT/'public-context-v1.lean'),neutral_packet_sha256=sha(RUN/'neutral-packet-v1.lean'),semantic_signature_sha256=sha(CONTRACT/'semantic-signature-v1.json'),state='draft, not stabilized or proving'))
fixed();print('Frozen nine public targets; standalone contexts elaborated, theorem proofs not begun')
