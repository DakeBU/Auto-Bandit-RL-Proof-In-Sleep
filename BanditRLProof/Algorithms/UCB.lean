import Mathlib.Data.Fintype.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import BanditRLProof.ConcentrationSubGaussian
import BanditRLProof.ConcentrationVariance
import BanditRLProof.ExpectationPullCount
import BanditRLProof.ExpectationSums
import BanditRLProof.MeasurablePullCount
import BanditRLProof.PolicyMeasurability
import BanditRLProof.ProbabilityUnionBound
import BanditRLProof.Regret

/-!
# UCB surfaces
-/

namespace BanditRLProof
namespace UCB

open MeasureTheory

/-- Parameters for a finite-arm UCB run. -/
structure Spec (K : Nat) where
  hK : 0 < K
  explorationScale : Rat

/-- State visible to an index policy at one time step. -/
structure IndexState (K : Nat) where
  empiricalMean : Fin K → Rat
  pulls : Fin K → Nat

/--
Placeholder score surface for the first dependency-light layer.

The Mathlib/LML migration will refine this to
`mean + sqrt (2 * c * log n / pulls)`.
-/
def score (_spec : Spec K) (state : IndexState K) (arm : Fin K) : Rat :=
  state.empiricalMean arm

@[simp] theorem score_eq_empiricalMean (spec : Spec K) (state : IndexState K)
    (arm : Fin K) :
    score spec state arm = state.empiricalMean arm := rfl

/-- Real-valued UCB confidence score `empirical mean + radius`. -/
def confidenceScore {Arm : Type} (empiricalMean radius : Arm -> Real)
    (arm : Arm) : Real :=
  empiricalMean arm + radius arm

@[simp] theorem confidenceScore_apply
    {Arm : Type} (empiricalMean radius : Arm -> Real) (arm : Arm) :
    confidenceScore empiricalMean radius arm =
      empiricalMean arm + radius arm := rfl

private theorem score_le_foldl_select
    {K : Nat} (scores : Fin K -> Real) (init : Fin K) :
    forall l : List (Fin K),
      (forall a : Fin K, List.Mem a l ->
        scores a <=
          scores
            (l.foldl
              (fun best arm : Fin K =>
                if scores best < scores arm then arm else best)
              init)) /\
      scores init <=
        scores
          (l.foldl
            (fun best arm : Fin K =>
              if scores best < scores arm then arm else best)
            init)
  | [] => by
      exact And.intro
        (by
          intro _ ha
          cases ha)
        (by
          simp)
  | arm :: rest => by
      let select :=
        fun best arm : Fin K =>
          if scores best < scores arm then arm else best
      let next := select init arm
      have ih := score_le_foldl_select (scores := scores) next rest
      have harm_next : scores arm <= scores next := by
        exact if hlt : scores init < scores arm then
          by
            simp [next, select, hlt]
        else
          by
            simp [next, select, hlt, le_of_not_gt hlt]
      exact And.intro
        (by
          intro a ha
          cases ha with
          | head =>
              exact le_trans harm_next ih.2
          | tail _ ha =>
              exact ih.1 a ha)
        (by
          have hinit_next : scores init <= scores next := by
            exact if hlt : scores init < scores arm then
              by
                simpa [next, select, hlt] using le_of_lt hlt
            else
              by
                simp [next, select, hlt]
          exact le_trans hinit_next ih.2)

/--
Concrete finite-arm Real score argmax selector.

The selector scans `List.finRange K`, keeps the previous arm on ties, and uses
`hK` only to seed the nonempty finite arm set. This mirrors the ETC argmax
oracle but targets the Real-valued UCB confidence-score surface.
-/
noncomputable def scoreArgmax
    {K : Nat} (hK : 0 < K) (scores : Fin K -> Real) : Fin K :=
  (List.finRange K).foldl
    (fun best arm : Fin K =>
      if scores best < scores arm then arm else best)
    (Fin.mk 0 hK)

/-- The concrete Real score argmax dominates every arm score. -/
theorem scoreArgmax_spec
    {K : Nat} (hK : 0 < K)
    (scores : Fin K -> Real) (a : Fin K) :
    scores a <= scores (scoreArgmax hK scores) := by
  unfold scoreArgmax
  exact
    (score_le_foldl_select
      (scores := scores)
      (init := Fin.mk 0 hK)
      (List.finRange K)).1 a (List.mem_finRange a)

/-- Concrete UCB action that maximizes the current confidence score. -/
noncomputable def confidenceScoreArgmaxAction
    {Omega : Type} {K : Nat} (hK : 0 < K)
    (empiricalMean : Omega -> Nat -> Fin K -> Real)
    (radius : Nat -> Fin K -> Real) :
    Omega -> Nat -> Fin K :=
  fun omega t =>
    scoreArgmax hK
      (fun arm => confidenceScore (empiricalMean omega t) (radius t) arm)

/--
The concrete confidence-score argmax action supplies score maximality against
any comparison arm.
-/
theorem confidenceScoreArgmaxAction_score_max
    {Omega : Type} {K : Nat} (hK : 0 < K)
    (empiricalMean : Omega -> Nat -> Fin K -> Real)
    (radius : Nat -> Fin K -> Real)
    (omega : Omega) (t : Nat) (arm : Fin K) :
    confidenceScore (empiricalMean omega t) (radius t) arm <=
      confidenceScore (empiricalMean omega t) (radius t)
        (confidenceScoreArgmaxAction hK empiricalMean radius omega t) := by
  unfold confidenceScoreArgmaxAction
  exact
    scoreArgmax_spec hK
      (fun arm => confidenceScore (empiricalMean omega t) (radius t) arm)
      arm

/--
Selected-arm form of `confidenceScoreArgmaxAction_score_max`, matching the
abstract selected-action bridge contract.
-/
theorem confidenceScoreArgmaxAction_score_max_of_selected
    {Omega : Type} {K : Nat} (hK : 0 < K)
    (empiricalMean : Omega -> Nat -> Fin K -> Real)
    (radius : Nat -> Fin K -> Real)
    (omega : Omega) (t : Nat) (best chosen : Fin K)
    (hselected :
      confidenceScoreArgmaxAction hK empiricalMean radius omega t = chosen) :
    confidenceScore (empiricalMean omega t) (radius t) best <=
      confidenceScore (empiricalMean omega t) (radius t) chosen := by
  have hmax :=
    confidenceScoreArgmaxAction_score_max
      hK empiricalMean radius omega t best
  simpa [hselected] using hmax

/-- Mean gap against a designated best arm for Real-valued UCB algebra. -/
def meanGap {Arm : Type} (trueMean : Arm -> Real) (best arm : Arm) : Real :=
  trueMean best - trueMean arm

@[simp] theorem meanGap_apply
    {Arm : Type} (trueMean : Arm -> Real) (best arm : Arm) :
    meanGap trueMean best arm = trueMean best - trueMean arm := rfl

/--
UCB good-event algebra: if the best arm's true mean is below its upper
confidence score, the chosen arm's true mean is above its lower confidence
score, and the chosen arm maximizes the confidence score against the best arm,
then the chosen arm's mean gap is at most twice its radius.
-/
theorem meanGap_le_two_radius_of_confidenceScore_max
    {Arm : Type} (trueMean empiricalMean radius : Arm -> Real)
    (best chosen : Arm)
    (hbest_upper :
      trueMean best <= confidenceScore empiricalMean radius best)
    (hchosen_lower :
      empiricalMean chosen - radius chosen <= trueMean chosen)
    (hscore :
      confidenceScore empiricalMean radius best <=
        confidenceScore empiricalMean radius chosen) :
    meanGap trueMean best chosen <= 2 * radius chosen := by
  unfold meanGap confidenceScore at *
  linarith

/--
Contrapositive consumer for the UCB good-event algebra: under the same good
event and score-maximality hypotheses, a strict `2 * radius < gap` certificate
rules out choosing that arm.
-/
theorem not_two_radius_lt_meanGap_of_confidenceScore_max
    {Arm : Type} (trueMean empiricalMean radius : Arm -> Real)
    (best chosen : Arm)
    (hbest_upper :
      trueMean best <= confidenceScore empiricalMean radius best)
    (hchosen_lower :
      empiricalMean chosen - radius chosen <= trueMean chosen)
    (hscore :
      confidenceScore empiricalMean radius best <=
        confidenceScore empiricalMean radius chosen)
    (hgap_large : 2 * radius chosen < meanGap trueMean best chosen) :
    False := by
  have hgap_le := meanGap_le_two_radius_of_confidenceScore_max
    trueMean empiricalMean radius best chosen hbest_upper hchosen_lower hscore
  linarith

/-- Upper-confidence failure for a random empirical-mean surface. -/
def upperConfidenceBad {Omega Arm : Type}
    (trueMean : Arm -> Real) (empiricalMean : Omega -> Arm -> Real)
    (radius : Arm -> Real) (arm : Arm) : Set Omega :=
  {omega | trueMean arm > confidenceScore (empiricalMean omega) radius arm}

/-- Lower-confidence failure for a random empirical-mean surface. -/
def lowerConfidenceBad {Omega Arm : Type}
    (trueMean : Arm -> Real) (empiricalMean : Omega -> Arm -> Real)
    (radius : Arm -> Real) (arm : Arm) : Set Omega :=
  {omega | empiricalMean omega arm - radius arm > trueMean arm}

/-- Upper-confidence failure is measurable when the arm empirical mean is measurable. -/
theorem measurableSet_upperConfidenceBad
    {Omega Arm : Type} [MeasurableSpace Omega]
    (trueMean : Arm -> Real) (empiricalMean : Omega -> Arm -> Real)
    (radius : Arm -> Real) (arm : Arm)
    (hmeas : Measurable (fun omega : Omega => empiricalMean omega arm)) :
    MeasurableSet (upperConfidenceBad trueMean empiricalMean radius arm) := by
  simpa [upperConfidenceBad, confidenceScore] using
    measurableSet_lt (hmeas.add measurable_const) measurable_const

/-- Lower-confidence failure is measurable when the arm empirical mean is measurable. -/
theorem measurableSet_lowerConfidenceBad
    {Omega Arm : Type} [MeasurableSpace Omega]
    (trueMean : Arm -> Real) (empiricalMean : Omega -> Arm -> Real)
    (radius : Arm -> Real) (arm : Arm)
    (hmeas : Measurable (fun omega : Omega => empiricalMean omega arm)) :
    MeasurableSet (lowerConfidenceBad trueMean empiricalMean radius arm) := by
  simpa [lowerConfidenceBad] using
    measurableSet_lt measurable_const (hmeas.sub measurable_const)

/-- The finite-arm UCB confidence bad event, as a union of upper/lower failures. -/
def confidenceBadEvent {Omega Arm : Type} [Fintype Arm]
    (trueMean : Arm -> Real) (empiricalMean : Omega -> Arm -> Real)
    (radius : Arm -> Real) : Set Omega :=
  ⋃ arm : Arm, upperConfidenceBad trueMean empiricalMean radius arm ∪
    lowerConfidenceBad trueMean empiricalMean radius arm

/-- The finite-arm UCB confidence bad event is measurable from per-arm empirical-mean measurability. -/
theorem measurableSet_confidenceBadEvent
    {Omega Arm : Type} [MeasurableSpace Omega] [Fintype Arm]
    (trueMean : Arm -> Real) (empiricalMean : Omega -> Arm -> Real)
    (radius : Arm -> Real)
    (hmeas : forall arm : Arm,
      Measurable (fun omega : Omega => empiricalMean omega arm)) :
    MeasurableSet (confidenceBadEvent trueMean empiricalMean radius) := by
  unfold confidenceBadEvent
  exact MeasurableSet.iUnion (fun arm =>
    (measurableSet_upperConfidenceBad trueMean empiricalMean radius arm
      (hmeas arm)).union
      (measurableSet_lowerConfidenceBad trueMean empiricalMean radius arm
        (hmeas arm)))

theorem not_upperConfidenceBad_of_not_confidenceBadEvent
    {Omega Arm : Type} [Fintype Arm]
    (trueMean : Arm -> Real) (empiricalMean : Omega -> Arm -> Real)
    (radius : Arm -> Real) (omega : Omega) (arm : Arm)
    (hgood : omega ∉ confidenceBadEvent trueMean empiricalMean radius) :
    omega ∉ upperConfidenceBad trueMean empiricalMean radius arm := by
  intro hbad
  exact hgood (by
    unfold confidenceBadEvent
    exact Set.mem_iUnion.mpr ⟨arm, Or.inl hbad⟩)

theorem not_lowerConfidenceBad_of_not_confidenceBadEvent
    {Omega Arm : Type} [Fintype Arm]
    (trueMean : Arm -> Real) (empiricalMean : Omega -> Arm -> Real)
    (radius : Arm -> Real) (omega : Omega) (arm : Arm)
    (hgood : omega ∉ confidenceBadEvent trueMean empiricalMean radius) :
    omega ∉ lowerConfidenceBad trueMean empiricalMean radius arm := by
  intro hbad
  exact hgood (by
    unfold confidenceBadEvent
    exact Set.mem_iUnion.mpr ⟨arm, Or.inr hbad⟩)

/--
Event-level UCB good-event consumer: outside the finite-arm confidence bad
event, score maximality against the best arm implies the standard
`gap <= 2 * chosenRadius` conclusion.
-/
theorem meanGap_le_two_radius_of_not_confidenceBadEvent
    {Omega Arm : Type} [Fintype Arm]
    (trueMean : Arm -> Real) (empiricalMean : Omega -> Arm -> Real)
    (radius : Arm -> Real) (omega : Omega) (best chosen : Arm)
    (hgood : omega ∉ confidenceBadEvent trueMean empiricalMean radius)
    (hscore :
      confidenceScore (empiricalMean omega) radius best <=
        confidenceScore (empiricalMean omega) radius chosen) :
    meanGap trueMean best chosen <= 2 * radius chosen := by
  have hbest_not :=
    not_upperConfidenceBad_of_not_confidenceBadEvent
      trueMean empiricalMean radius omega best hgood
  have hchosen_not :=
    not_lowerConfidenceBad_of_not_confidenceBadEvent
      trueMean empiricalMean radius omega chosen hgood
  have hbest_upper :
      trueMean best <= confidenceScore (empiricalMean omega) radius best := by
    exact le_of_not_gt hbest_not
  have hchosen_lower :
      empiricalMean omega chosen - radius chosen <= trueMean chosen := by
    exact le_of_not_gt hchosen_not
  exact meanGap_le_two_radius_of_confidenceScore_max
    trueMean (empiricalMean omega) radius best chosen
    hbest_upper hchosen_lower hscore

/--
Finite-arm union bound for the UCB confidence bad event.

This is still an outer-measure bound: it does not require measurability of the
upper/lower confidence failure events.
-/
theorem measure_confidenceBadEvent_le_sum_upper_lower
    {Omega Arm : Type} [MeasurableSpace Omega] [Fintype Arm]
    (mu : Measure Omega)
    (trueMean : Arm -> Real) (empiricalMean : Omega -> Arm -> Real)
    (radius : Arm -> Real) :
    mu (confidenceBadEvent trueMean empiricalMean radius) <=
      (Finset.univ : Finset Arm).sum
        (fun arm =>
          mu (upperConfidenceBad trueMean empiricalMean radius arm) +
            mu (lowerConfidenceBad trueMean empiricalMean radius arm)) := by
  unfold confidenceBadEvent
  calc
    mu (⋃ arm : Arm, upperConfidenceBad trueMean empiricalMean radius arm ∪
        lowerConfidenceBad trueMean empiricalMean radius arm)
        <= (Finset.univ : Finset Arm).sum
            (fun arm =>
              mu (upperConfidenceBad trueMean empiricalMean radius arm ∪
                lowerConfidenceBad trueMean empiricalMean radius arm)) := by
          exact ProbabilityUnionBound.measure_iUnion_fintype_le_sum
            mu (fun arm : Arm =>
              upperConfidenceBad trueMean empiricalMean radius arm ∪
                lowerConfidenceBad trueMean empiricalMean radius arm)
    _ <= (Finset.univ : Finset Arm).sum
          (fun arm =>
            mu (upperConfidenceBad trueMean empiricalMean radius arm) +
              mu (lowerConfidenceBad trueMean empiricalMean radius arm)) := by
          exact Finset.sum_le_sum (fun arm _h =>
            measure_union_le
              (upperConfidenceBad trueMean empiricalMean radius arm)
              (lowerConfidenceBad trueMean empiricalMean radius arm))

/-- Time-indexed UCB confidence bad event. -/
def confidenceBadEventAt {Omega Arm : Type} [Fintype Arm]
    (trueMean : Arm -> Real)
    (empiricalMean : Omega -> Nat -> Arm -> Real)
    (radius : Nat -> Arm -> Real) (t : Nat) : Set Omega :=
  confidenceBadEvent trueMean
    (fun omega arm => empiricalMean omega t arm) (radius t)

/--
The time-indexed UCB confidence bad event is measurable from per-arm empirical
mean measurability at that time.
-/
theorem measurableSet_confidenceBadEventAt
    {Omega Arm : Type} [MeasurableSpace Omega] [Fintype Arm]
    (trueMean : Arm -> Real)
    (empiricalMean : Omega -> Nat -> Arm -> Real)
    (radius : Nat -> Arm -> Real) (t : Nat)
    (hmeas : forall arm : Arm,
      Measurable (fun omega : Omega => empiricalMean omega t arm)) :
    MeasurableSet (confidenceBadEventAt trueMean empiricalMean radius t) := by
  simpa [confidenceBadEventAt] using
    measurableSet_confidenceBadEvent trueMean
      (fun omega arm => empiricalMean omega t arm) (radius t) hmeas

/-- Finite-horizon union of time-indexed UCB confidence bad events. -/
def finiteHorizonConfidenceBadEvent {Omega Arm : Type} [Fintype Arm]
    (trueMean : Arm -> Real)
    (empiricalMean : Omega -> Nat -> Arm -> Real)
    (radius : Nat -> Arm -> Real) (T : Nat) : Set Omega :=
  ⋃ t ∈ Finset.range T,
    confidenceBadEventAt trueMean empiricalMean radius t

/--
Outside the finite-horizon confidence bad event, every time-indexed bad event
inside the horizon is absent.
-/
theorem not_confidenceBadEventAt_of_not_finiteHorizonConfidenceBadEvent
    {Omega Arm : Type} [Fintype Arm]
    (trueMean : Arm -> Real)
    (empiricalMean : Omega -> Nat -> Arm -> Real)
    (radius : Nat -> Arm -> Real) (T : Nat)
    (omega : Omega) (t : Nat) (ht : t < T)
    (hgood :
      omega ∉ finiteHorizonConfidenceBadEvent trueMean empiricalMean radius T) :
    omega ∉ confidenceBadEventAt trueMean empiricalMean radius t := by
  intro hbad
  exact hgood (by
    unfold finiteHorizonConfidenceBadEvent
    exact Set.mem_iUnion.mpr
      ⟨t, Set.mem_iUnion.mpr
        ⟨Finset.mem_range.mpr ht, hbad⟩⟩)

/--
Finite-horizon good-event consumer: outside the finite-horizon confidence bad
event, score maximality at any `t < T` gives the standard UCB gap-radius
bound for the chosen arm.
-/
theorem meanGap_le_two_radius_of_not_finiteHorizonConfidenceBadEvent
    {Omega Arm : Type} [Fintype Arm]
    (trueMean : Arm -> Real)
    (empiricalMean : Omega -> Nat -> Arm -> Real)
    (radius : Nat -> Arm -> Real) (T : Nat)
    (omega : Omega) (t : Nat) (best chosen : Arm)
    (ht : t < T)
    (hgood :
      omega ∉ finiteHorizonConfidenceBadEvent trueMean empiricalMean radius T)
    (hscore :
      confidenceScore (empiricalMean omega t) (radius t) best <=
        confidenceScore (empiricalMean omega t) (radius t) chosen) :
    meanGap trueMean best chosen <= 2 * radius t chosen := by
  have hgood_at :
      omega ∉ confidenceBadEventAt trueMean empiricalMean radius t :=
    not_confidenceBadEventAt_of_not_finiteHorizonConfidenceBadEvent
      trueMean empiricalMean radius T omega t ht hgood
  simpa [confidenceBadEventAt] using
    meanGap_le_two_radius_of_not_confidenceBadEvent
      trueMean (fun omega arm => empiricalMean omega t arm) (radius t)
      omega best chosen hgood_at hscore

/--
Contrapositive finite-horizon good-event consumer: if a chosen arm's gap is
larger than twice its current radius and it beats the best arm's UCB score, the
finite-horizon confidence bad event must occur.
-/
theorem mem_finiteHorizonConfidenceBadEvent_of_two_radius_lt_meanGap_of_score_max
    {Omega Arm : Type} [Fintype Arm]
    (trueMean : Arm -> Real)
    (empiricalMean : Omega -> Nat -> Arm -> Real)
    (radius : Nat -> Arm -> Real) (T : Nat)
    (omega : Omega) (t : Nat) (best chosen : Arm)
    (ht : t < T)
    (hscore :
      confidenceScore (empiricalMean omega t) (radius t) best <=
        confidenceScore (empiricalMean omega t) (radius t) chosen)
    (hgap_large :
      2 * radius t chosen < meanGap trueMean best chosen) :
    omega ∈ finiteHorizonConfidenceBadEvent trueMean empiricalMean radius T := by
  by_contra hgood
  have hgap_le :
      meanGap trueMean best chosen <= 2 * radius t chosen :=
    meanGap_le_two_radius_of_not_finiteHorizonConfidenceBadEvent
      trueMean empiricalMean radius T omega t best chosen ht hgood hscore
  linarith

/--
Event-level form of the finite-horizon large-gap consumer. This is the set
inclusion shape needed before applying measure monotonicity in pull-count
arguments.
-/
theorem scoreMaxEvent_subset_finiteHorizonConfidenceBadEvent_of_two_radius_lt_meanGap
    {Omega Arm : Type} [Fintype Arm]
    (trueMean : Arm -> Real)
    (empiricalMean : Omega -> Nat -> Arm -> Real)
    (radius : Nat -> Arm -> Real) (T : Nat)
    (t : Nat) (best chosen : Arm)
    (ht : t < T)
    (hgap_large :
      2 * radius t chosen < meanGap trueMean best chosen) :
    {omega : Omega |
      confidenceScore (empiricalMean omega t) (radius t) best <=
        confidenceScore (empiricalMean omega t) (radius t) chosen} ⊆
      finiteHorizonConfidenceBadEvent trueMean empiricalMean radius T := by
  intro omega hscore
  exact
    mem_finiteHorizonConfidenceBadEvent_of_two_radius_lt_meanGap_of_score_max
      trueMean empiricalMean radius T omega t best chosen ht hscore hgap_large

/--
Finite-horizon union bound for UCB confidence bad events.

This assembles the single-time upper/lower confidence-event union bound across
`t < T`. It does not produce concentration tails or simplify the resulting
double finite sum.
-/
theorem measure_finiteHorizonConfidenceBadEvent_le_sum_upper_lower
    {Omega Arm : Type} [MeasurableSpace Omega] [Fintype Arm]
    (mu : Measure Omega)
    (trueMean : Arm -> Real)
    (empiricalMean : Omega -> Nat -> Arm -> Real)
    (radius : Nat -> Arm -> Real) (T : Nat) :
    mu (finiteHorizonConfidenceBadEvent trueMean empiricalMean radius T) <=
      (Finset.range T).sum
        (fun t =>
          (Finset.univ : Finset Arm).sum
            (fun arm =>
              mu (upperConfidenceBad trueMean
                (fun omega arm => empiricalMean omega t arm)
                (radius t) arm) +
              mu (lowerConfidenceBad trueMean
                (fun omega arm => empiricalMean omega t arm)
                (radius t) arm))) := by
  unfold finiteHorizonConfidenceBadEvent confidenceBadEventAt
  calc
    mu (⋃ t ∈ Finset.range T,
        confidenceBadEvent trueMean
          (fun omega arm => empiricalMean omega t arm) (radius t))
        <= (Finset.range T).sum
            (fun t =>
              mu (confidenceBadEvent trueMean
                (fun omega arm => empiricalMean omega t arm) (radius t))) := by
          exact ProbabilityUnionBound.measure_biUnion_finset_le
            mu (Finset.range T)
            (fun t =>
              confidenceBadEvent trueMean
                (fun omega arm => empiricalMean omega t arm) (radius t))
    _ <= (Finset.range T).sum
        (fun t =>
          (Finset.univ : Finset Arm).sum
            (fun arm =>
              mu (upperConfidenceBad trueMean
                (fun omega arm => empiricalMean omega t arm)
                (radius t) arm) +
              mu (lowerConfidenceBad trueMean
                (fun omega arm => empiricalMean omega t arm)
                (radius t) arm))) := by
          exact Finset.sum_le_sum (fun t _ht =>
            measure_confidenceBadEvent_le_sum_upper_lower
              mu trueMean
              (fun omega arm => empiricalMean omega t arm) (radius t))

/--
Finite-horizon tail-bound consumer for UCB confidence bad events.

The hypotheses `hupper` and `hlower` are the per-time/per-arm concentration
inputs for the upper and lower confidence failures.  This wrapper only
assembles those local tail budgets across `t < T` and finite arms.
-/
theorem measure_finiteHorizonConfidenceBadEvent_le_tail_sum
    {Omega Arm : Type} [MeasurableSpace Omega] [Fintype Arm]
    (mu : Measure Omega)
    (trueMean : Arm -> Real)
    (empiricalMean : Omega -> Nat -> Arm -> Real)
    (radius : Nat -> Arm -> Real)
    (upperTail lowerTail : Nat -> Arm -> ENNReal) (T : Nat)
    (hupper : forall t arm, t < T ->
      mu (upperConfidenceBad trueMean
        (fun omega arm => empiricalMean omega t arm)
        (radius t) arm) <= upperTail t arm)
    (hlower : forall t arm, t < T ->
      mu (lowerConfidenceBad trueMean
        (fun omega arm => empiricalMean omega t arm)
        (radius t) arm) <= lowerTail t arm) :
    mu (finiteHorizonConfidenceBadEvent trueMean empiricalMean radius T) <=
      (Finset.range T).sum
        (fun t =>
          (Finset.univ : Finset Arm).sum
            (fun arm => upperTail t arm + lowerTail t arm)) := by
  exact
    (measure_finiteHorizonConfidenceBadEvent_le_sum_upper_lower
      mu trueMean empiricalMean radius T).trans
      (Finset.sum_le_sum (fun t ht =>
        Finset.sum_le_sum (fun arm _harm =>
          add_le_add
            (hupper t arm (Finset.mem_range.mp ht))
            (hlower t arm (Finset.mem_range.mp ht)))))

/--
An upper-confidence failure implies an absolute empirical-mean deviation at
least as large as the radius.
-/
theorem upperConfidenceBad_subset_absDeviation
    {Omega Arm : Type}
    (trueMean : Arm -> Real) (empiricalMean : Omega -> Arm -> Real)
    (radius : Arm -> Real) (arm : Arm) :
    upperConfidenceBad trueMean empiricalMean radius arm ⊆
      {omega | radius arm <= |empiricalMean omega arm - trueMean arm|} := by
  intro omega hbad
  have hrad :
      radius arm <= trueMean arm - empiricalMean omega arm := by
    dsimp [upperConfidenceBad, confidenceScore] at hbad
    linarith
  have habs :
      trueMean arm - empiricalMean omega arm <=
        |empiricalMean omega arm - trueMean arm| := by
    have h := neg_le_abs (empiricalMean omega arm - trueMean arm)
    linarith
  exact hrad.trans habs

/--
A lower-confidence failure implies an absolute empirical-mean deviation at
least as large as the radius.
-/
theorem lowerConfidenceBad_subset_absDeviation
    {Omega Arm : Type}
    (trueMean : Arm -> Real) (empiricalMean : Omega -> Arm -> Real)
    (radius : Arm -> Real) (arm : Arm) :
    lowerConfidenceBad trueMean empiricalMean radius arm ⊆
      {omega | radius arm <= |empiricalMean omega arm - trueMean arm|} := by
  intro omega hbad
  have hrad :
      radius arm <= empiricalMean omega arm - trueMean arm := by
    dsimp [lowerConfidenceBad] at hbad
    linarith
  exact hrad.trans (le_abs_self (empiricalMean omega arm - trueMean arm))

/-- Measure monotonicity form of `upperConfidenceBad_subset_absDeviation`. -/
theorem measure_upperConfidenceBad_le_absDeviation
    {Omega Arm : Type} [MeasurableSpace Omega]
    (mu : Measure Omega)
    (trueMean : Arm -> Real) (empiricalMean : Omega -> Arm -> Real)
    (radius : Arm -> Real) (arm : Arm) :
    mu (upperConfidenceBad trueMean empiricalMean radius arm) <=
      mu {omega | radius arm <= |empiricalMean omega arm - trueMean arm|} := by
  exact measure_mono
    (upperConfidenceBad_subset_absDeviation
      trueMean empiricalMean radius arm)

/-- Measure monotonicity form of `lowerConfidenceBad_subset_absDeviation`. -/
theorem measure_lowerConfidenceBad_le_absDeviation
    {Omega Arm : Type} [MeasurableSpace Omega]
    (mu : Measure Omega)
    (trueMean : Arm -> Real) (empiricalMean : Omega -> Arm -> Real)
    (radius : Arm -> Real) (arm : Arm) :
    mu (lowerConfidenceBad trueMean empiricalMean radius arm) <=
      mu {omega | radius arm <= |empiricalMean omega arm - trueMean arm|} := by
  exact measure_mono
    (lowerConfidenceBad_subset_absDeviation
      trueMean empiricalMean radius arm)

/--
Finite-horizon UCB confidence bad-event bound from absolute-deviation tails.

This is the UCB-facing adapter for concentration inequalities that bound
`mu {omega | radius <= |empiricalMean - trueMean|}`.  The same absolute
deviation tail controls both the upper and lower confidence failures.
-/
theorem measure_finiteHorizonConfidenceBadEvent_le_absDeviation_tail_sum
    {Omega Arm : Type} [MeasurableSpace Omega] [Fintype Arm]
    (mu : Measure Omega)
    (trueMean : Arm -> Real)
    (empiricalMean : Omega -> Nat -> Arm -> Real)
    (radius : Nat -> Arm -> Real)
    (tail : Nat -> Arm -> ENNReal) (T : Nat)
    (htail : forall t arm, t < T ->
      mu {omega | radius t arm <=
        |empiricalMean omega t arm - trueMean arm|} <= tail t arm) :
    mu (finiteHorizonConfidenceBadEvent trueMean empiricalMean radius T) <=
      (Finset.range T).sum
        (fun t =>
          (Finset.univ : Finset Arm).sum
            (fun arm => tail t arm + tail t arm)) := by
  exact measure_finiteHorizonConfidenceBadEvent_le_tail_sum
    mu trueMean empiricalMean radius tail tail T
    (fun t arm ht =>
      (measure_upperConfidenceBad_le_absDeviation
        mu trueMean
        (fun omega arm => empiricalMean omega t arm)
        (radius t) arm).trans (htail t arm ht))
    (fun t arm ht =>
      (measure_lowerConfidenceBad_le_absDeviation
        mu trueMean
        (fun omega arm => empiricalMean omega t arm)
        (radius t) arm).trans (htail t arm ht))

/--
Chebyshev tail budget for a UCB empirical mean at time `t` and arm `arm`.

This is intentionally an abstract finite-variance budget: it does not prove the
variance rate of an empirical mean or choose a log/sqrt UCB radius.
-/
noncomputable def chebyshevAbsDeviationTail
    {Omega Arm : Type} [MeasurableSpace Omega]
    (mu : Measure Omega)
    (empiricalMean : Omega -> Nat -> Arm -> Real)
    (radius : Nat -> Arm -> Real) (t : Nat) (arm : Arm) : ENNReal :=
  ENNReal.ofReal
    (ProbabilityTheory.variance
      (fun omega : Omega => empiricalMean omega t arm) mu /
        (radius t arm) ^ 2)

/--
Single-time Chebyshev tail for the UCB absolute-deviation event, under an
explicit mean-identification contract.
-/
theorem measure_absDeviation_le_chebyshev_tail
    {Omega Arm : Type} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (trueMean : Arm -> Real)
    (empiricalMean : Omega -> Nat -> Arm -> Real)
    (radius : Nat -> Arm -> Real) (t : Nat) (arm : Arm)
    (hmem :
      MemLp (fun omega : Omega => empiricalMean omega t arm) 2 mu)
    (hradius : 0 < radius t arm)
    (hmean :
      integral mu (fun omega : Omega => empiricalMean omega t arm) =
        trueMean arm) :
    mu {omega | radius t arm <=
        |empiricalMean omega t arm - trueMean arm|} <=
      chebyshevAbsDeviationTail mu empiricalMean radius t arm := by
  have htail :=
    Concentration.variance_chebyshev_tail
      (mu := mu)
      (X := fun omega : Omega => empiricalMean omega t arm)
      hmem (eps := radius t arm) hradius
  simpa [chebyshevAbsDeviationTail, hmean] using htail

/--
Finite-horizon UCB confidence bad-event bound from Chebyshev absolute-deviation
tails.

This is a concrete concentration producer for the abstract absolute-deviation
tail adapter.  It still leaves empirical-mean construction, variance-rate
simplification, log/sqrt radius choice, pull-count bounds, and final regret to
later leaves.
-/
theorem measure_finiteHorizonConfidenceBadEvent_le_chebyshev_tail_sum
    {Omega Arm : Type} [MeasurableSpace Omega] [Fintype Arm]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (trueMean : Arm -> Real)
    (empiricalMean : Omega -> Nat -> Arm -> Real)
    (radius : Nat -> Arm -> Real) (T : Nat)
    (hmem : forall t arm, t < T ->
      MemLp (fun omega : Omega => empiricalMean omega t arm) 2 mu)
    (hradius : forall t arm, t < T -> 0 < radius t arm)
    (hmean : forall t arm, t < T ->
      integral mu (fun omega : Omega => empiricalMean omega t arm) =
        trueMean arm) :
    mu (finiteHorizonConfidenceBadEvent trueMean empiricalMean radius T) <=
      (Finset.range T).sum
        (fun t =>
          (Finset.univ : Finset Arm).sum
            (fun arm =>
              chebyshevAbsDeviationTail mu empiricalMean radius t arm +
                chebyshevAbsDeviationTail mu empiricalMean radius t arm)) := by
  exact measure_finiteHorizonConfidenceBadEvent_le_absDeviation_tail_sum
    mu trueMean empiricalMean radius
    (fun t arm => chebyshevAbsDeviationTail mu empiricalMean radius t arm)
    T
    (fun t arm ht =>
      measure_absDeviation_le_chebyshev_tail
        mu trueMean empiricalMean radius t arm
        (hmem t arm ht) (hradius t arm ht) (hmean t arm ht))

/--
One-sided sub-Gaussian tail budget for a UCB empirical mean at time `t` and
arm `arm`.

The proxy is for the centered variable `empiricalMean t arm - trueMean arm`.
This one-sided budget is the sharper producer for the existing upper/lower
confidence tail consumer; the absolute-deviation wrapper remains available for
two-sided concentration statements.
-/
noncomputable def subGaussianOneSidedDeviationTail
    {Arm : Type}
    (radius : Nat -> Arm -> Real)
    (proxy : Nat -> Arm -> NNReal) (t : Nat) (arm : Arm) : ENNReal :=
  ENNReal.ofReal
    (Real.exp (-(radius t arm) ^ 2 /
      (2 * ((proxy t arm : NNReal) : Real))))

/--
Radius-budget simplification for the one-sided UCB sub-Gaussian tail.

If `radius^2` dominates `2 * proxy * budget`, the canonical exponential
producer is bounded by `exp (-budget)`. This is the algebraic handoff between
abstract sub-Gaussian tails and later log/sqrt UCB radius choices.
-/
theorem subGaussianOneSidedDeviationTail_le_exp_neg_budget
    {Arm : Type}
    (radius : Nat -> Arm -> Real)
    (proxy : Nat -> Arm -> NNReal) (budget : Nat -> Arm -> Real)
    (t : Nat) (arm : Arm)
    (hproxy : 0 < ((proxy t arm : NNReal) : Real))
    (hradius_sq :
      2 * ((proxy t arm : NNReal) : Real) * budget t arm <=
        (radius t arm) ^ 2) :
    subGaussianOneSidedDeviationTail radius proxy t arm <=
      ENNReal.ofReal (Real.exp (-(budget t arm))) := by
  unfold subGaussianOneSidedDeviationTail
  refine ENNReal.ofReal_le_ofReal ?_
  apply Real.exp_le_exp.mpr
  have hden_pos : 0 < 2 * ((proxy t arm : NNReal) : Real) := by
    exact mul_pos (by norm_num) hproxy
  have hbudget_le :
      budget t arm <=
        (radius t arm) ^ 2 /
          (2 * ((proxy t arm : NNReal) : Real)) := by
    rw [le_div_iff₀ hden_pos]
    simpa [mul_assoc, mul_comm, mul_left_comm] using hradius_sq
  simpa [neg_div] using neg_le_neg hbudget_le

/--
Concrete square-root radius associated with a one-sided sub-Gaussian budget.

The budget is left abstract so later leaves can instantiate it with logarithmic
schedules such as `log (T * |A| / delta)`.
-/
noncomputable def subGaussianBudgetRadius
    {Arm : Type}
    (proxy : Nat -> Arm -> NNReal) (budget : Nat -> Arm -> Real) :
    Nat -> Arm -> Real :=
  fun t arm =>
    Real.sqrt (2 * ((proxy t arm : NNReal) : Real) * budget t arm)

/-- The concrete square-root budget radius is nonnegative. -/
theorem subGaussianBudgetRadius_nonneg
    {Arm : Type}
    (proxy : Nat -> Arm -> NNReal) (budget : Nat -> Arm -> Real)
    (t : Nat) (arm : Arm) :
    0 <= subGaussianBudgetRadius proxy budget t arm := by
  exact Real.sqrt_nonneg _

/--
The concrete square-root budget radius satisfies the radius-square domination
contract consumed by `subGaussianOneSidedDeviationTail_le_exp_neg_budget`.

This uses `Real.sq_sqrt'`, so it does not need a separate nonnegativity
assumption on `budget`.
-/
theorem subGaussianBudgetRadius_sq_domination
    {Arm : Type}
    (proxy : Nat -> Arm -> NNReal) (budget : Nat -> Arm -> Real)
    (t : Nat) (arm : Arm) :
    2 * ((proxy t arm : NNReal) : Real) * budget t arm <=
      (subGaussianBudgetRadius proxy budget t arm) ^ 2 := by
  unfold subGaussianBudgetRadius
  rw [Real.sq_sqrt']
  exact le_max_left _ _

/--
One-sided sub-Gaussian tail bound specialized to the concrete square-root
budget radius.
-/
theorem subGaussianOneSidedDeviationTail_budgetRadius_le_exp_neg_budget
    {Arm : Type}
    (proxy : Nat -> Arm -> NNReal) (budget : Nat -> Arm -> Real)
    (t : Nat) (arm : Arm)
    (hproxy : 0 < ((proxy t arm : NNReal) : Real)) :
    subGaussianOneSidedDeviationTail
        (subGaussianBudgetRadius proxy budget) proxy t arm <=
      ENNReal.ofReal (Real.exp (-(budget t arm))) := by
  exact subGaussianOneSidedDeviationTail_le_exp_neg_budget
    (subGaussianBudgetRadius proxy budget) proxy budget t arm hproxy
    (subGaussianBudgetRadius_sq_domination proxy budget t arm)

/-- Single-time one-sided sub-Gaussian tail for an upper-confidence failure. -/
theorem measure_upperConfidenceBad_le_subGaussian_tail
    {Omega Arm : Type} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (trueMean : Arm -> Real)
    (empiricalMean : Omega -> Nat -> Arm -> Real)
    (radius : Nat -> Arm -> Real)
    (proxy : Nat -> Arm -> NNReal) (t : Nat) (arm : Arm)
    (hradius : 0 <= radius t arm)
    (hsubG :
      ProbabilityTheory.HasSubgaussianMGF
        (fun omega : Omega => empiricalMean omega t arm - trueMean arm)
        (proxy t arm) mu) :
    mu (upperConfidenceBad trueMean
        (fun omega arm => empiricalMean omega t arm)
        (radius t) arm) <=
      subGaussianOneSidedDeviationTail radius proxy t arm := by
  let X : Omega -> Real :=
    fun omega => empiricalMean omega t arm - trueMean arm
  let eps := radius t arm
  let tailReal : Real :=
    Real.exp (-(radius t arm) ^ 2 /
      (2 * ((proxy t arm : NNReal) : Real)))
  have htail_nonneg : 0 <= tailReal := (Real.exp_pos _).le
  have hsubGX :
      ProbabilityTheory.HasSubgaussianMGF X (proxy t arm) mu := by
    simpa [X] using hsubG
  have hneg : ProbabilityTheory.HasSubgaussianMGF
      (-X) (proxy t arm) mu := hsubGX.neg
  have htailReal :
      mu.real {omega | eps <= (-X) omega} <= tailReal := by
    simpa [X, eps, tailReal] using
      (ProbabilityTheory.HasSubgaussianMGF.measure_ge_le
        (X := -X) (c := proxy t arm) hneg hradius)
  have htail :
      mu {omega | eps <= (-X) omega} <= ENNReal.ofReal tailReal := by
    rw [Measure.real] at htailReal
    exact (ENNReal.le_ofReal_iff_toReal_le
      (measure_ne_top mu {omega | eps <= (-X) omega}) htail_nonneg).2
      htailReal
  have hsubset :
      upperConfidenceBad trueMean
          (fun omega arm => empiricalMean omega t arm)
          (radius t) arm ⊆ {omega | eps <= (-X) omega} := by
    intro omega hbad
    dsimp [upperConfidenceBad, confidenceScore] at hbad
    dsimp [X, eps]
    linarith
  exact (measure_mono hsubset).trans htail

/--
Single-time upper-confidence failure bound with an explicit exponential budget.
-/
theorem measure_upperConfidenceBad_le_subGaussian_exp_neg_budget
    {Omega Arm : Type} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (trueMean : Arm -> Real)
    (empiricalMean : Omega -> Nat -> Arm -> Real)
    (radius : Nat -> Arm -> Real)
    (proxy : Nat -> Arm -> NNReal) (budget : Nat -> Arm -> Real)
    (t : Nat) (arm : Arm)
    (hradius : 0 <= radius t arm)
    (hproxy : 0 < ((proxy t arm : NNReal) : Real))
    (hradius_sq :
      2 * ((proxy t arm : NNReal) : Real) * budget t arm <=
        (radius t arm) ^ 2)
    (hsubG :
      ProbabilityTheory.HasSubgaussianMGF
        (fun omega : Omega => empiricalMean omega t arm - trueMean arm)
        (proxy t arm) mu) :
    mu (upperConfidenceBad trueMean
        (fun omega arm => empiricalMean omega t arm)
        (radius t) arm) <=
      ENNReal.ofReal (Real.exp (-(budget t arm))) := by
  exact (measure_upperConfidenceBad_le_subGaussian_tail
    mu trueMean empiricalMean radius proxy t arm hradius hsubG).trans
      (subGaussianOneSidedDeviationTail_le_exp_neg_budget
        radius proxy budget t arm hproxy hradius_sq)

/--
Single-time upper-confidence failure bound for the concrete square-root budget
radius.
-/
theorem measure_upperConfidenceBad_le_subGaussian_budgetRadius
    {Omega Arm : Type} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (trueMean : Arm -> Real)
    (empiricalMean : Omega -> Nat -> Arm -> Real)
    (proxy : Nat -> Arm -> NNReal) (budget : Nat -> Arm -> Real)
    (t : Nat) (arm : Arm)
    (hproxy : 0 < ((proxy t arm : NNReal) : Real))
    (hsubG :
      ProbabilityTheory.HasSubgaussianMGF
        (fun omega : Omega => empiricalMean omega t arm - trueMean arm)
        (proxy t arm) mu) :
    mu (upperConfidenceBad trueMean
        (fun omega arm => empiricalMean omega t arm)
        (subGaussianBudgetRadius proxy budget t) arm) <=
      ENNReal.ofReal (Real.exp (-(budget t arm))) := by
  exact measure_upperConfidenceBad_le_subGaussian_exp_neg_budget
    mu trueMean empiricalMean
    (subGaussianBudgetRadius proxy budget) proxy budget t arm
    (subGaussianBudgetRadius_nonneg proxy budget t arm) hproxy
    (subGaussianBudgetRadius_sq_domination proxy budget t arm) hsubG

/-- Single-time one-sided sub-Gaussian tail for a lower-confidence failure. -/
theorem measure_lowerConfidenceBad_le_subGaussian_tail
    {Omega Arm : Type} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (trueMean : Arm -> Real)
    (empiricalMean : Omega -> Nat -> Arm -> Real)
    (radius : Nat -> Arm -> Real)
    (proxy : Nat -> Arm -> NNReal) (t : Nat) (arm : Arm)
    (hradius : 0 <= radius t arm)
    (hsubG :
      ProbabilityTheory.HasSubgaussianMGF
        (fun omega : Omega => empiricalMean omega t arm - trueMean arm)
        (proxy t arm) mu) :
    mu (lowerConfidenceBad trueMean
        (fun omega arm => empiricalMean omega t arm)
        (radius t) arm) <=
      subGaussianOneSidedDeviationTail radius proxy t arm := by
  let X : Omega -> Real :=
    fun omega => empiricalMean omega t arm - trueMean arm
  let eps := radius t arm
  let tailReal : Real :=
    Real.exp (-(radius t arm) ^ 2 /
      (2 * ((proxy t arm : NNReal) : Real)))
  have htail_nonneg : 0 <= tailReal := (Real.exp_pos _).le
  have hsubGX :
      ProbabilityTheory.HasSubgaussianMGF X (proxy t arm) mu := by
    simpa [X] using hsubG
  have htailReal :
      mu.real {omega | eps <= X omega} <= tailReal := by
    simpa [X, eps, tailReal] using
      (ProbabilityTheory.HasSubgaussianMGF.measure_ge_le
        (X := X) (c := proxy t arm) hsubGX hradius)
  have htail :
      mu {omega | eps <= X omega} <= ENNReal.ofReal tailReal := by
    rw [Measure.real] at htailReal
    exact (ENNReal.le_ofReal_iff_toReal_le
      (measure_ne_top mu {omega | eps <= X omega}) htail_nonneg).2
      htailReal
  have hsubset :
      lowerConfidenceBad trueMean
          (fun omega arm => empiricalMean omega t arm)
          (radius t) arm ⊆ {omega | eps <= X omega} := by
    intro omega hbad
    dsimp [lowerConfidenceBad] at hbad
    dsimp [X, eps]
    linarith
  exact (measure_mono hsubset).trans htail

/--
Single-time lower-confidence failure bound with an explicit exponential budget.
-/
theorem measure_lowerConfidenceBad_le_subGaussian_exp_neg_budget
    {Omega Arm : Type} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (trueMean : Arm -> Real)
    (empiricalMean : Omega -> Nat -> Arm -> Real)
    (radius : Nat -> Arm -> Real)
    (proxy : Nat -> Arm -> NNReal) (budget : Nat -> Arm -> Real)
    (t : Nat) (arm : Arm)
    (hradius : 0 <= radius t arm)
    (hproxy : 0 < ((proxy t arm : NNReal) : Real))
    (hradius_sq :
      2 * ((proxy t arm : NNReal) : Real) * budget t arm <=
        (radius t arm) ^ 2)
    (hsubG :
      ProbabilityTheory.HasSubgaussianMGF
        (fun omega : Omega => empiricalMean omega t arm - trueMean arm)
        (proxy t arm) mu) :
    mu (lowerConfidenceBad trueMean
        (fun omega arm => empiricalMean omega t arm)
        (radius t) arm) <=
      ENNReal.ofReal (Real.exp (-(budget t arm))) := by
  exact (measure_lowerConfidenceBad_le_subGaussian_tail
    mu trueMean empiricalMean radius proxy t arm hradius hsubG).trans
      (subGaussianOneSidedDeviationTail_le_exp_neg_budget
        radius proxy budget t arm hproxy hradius_sq)

/--
Single-time lower-confidence failure bound for the concrete square-root budget
radius.
-/
theorem measure_lowerConfidenceBad_le_subGaussian_budgetRadius
    {Omega Arm : Type} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (trueMean : Arm -> Real)
    (empiricalMean : Omega -> Nat -> Arm -> Real)
    (proxy : Nat -> Arm -> NNReal) (budget : Nat -> Arm -> Real)
    (t : Nat) (arm : Arm)
    (hproxy : 0 < ((proxy t arm : NNReal) : Real))
    (hsubG :
      ProbabilityTheory.HasSubgaussianMGF
        (fun omega : Omega => empiricalMean omega t arm - trueMean arm)
        (proxy t arm) mu) :
    mu (lowerConfidenceBad trueMean
        (fun omega arm => empiricalMean omega t arm)
        (subGaussianBudgetRadius proxy budget t) arm) <=
      ENNReal.ofReal (Real.exp (-(budget t arm))) := by
  exact measure_lowerConfidenceBad_le_subGaussian_exp_neg_budget
    mu trueMean empiricalMean
    (subGaussianBudgetRadius proxy budget) proxy budget t arm
    (subGaussianBudgetRadius_nonneg proxy budget t arm) hproxy
    (subGaussianBudgetRadius_sq_domination proxy budget t arm) hsubG

/--
Finite-horizon UCB confidence bad-event bound from one-sided sub-Gaussian
upper/lower tails.

This is the sharper UCB-facing sub-Gaussian producer for the existing
upper/lower tail consumer. It still leaves empirical-mean construction,
proxy/radius simplification to the textbook log/sqrt form, pull-count bounds,
and final regret to later leaves.
-/
theorem measure_finiteHorizonConfidenceBadEvent_le_subGaussian_oneSided_tail_sum
    {Omega Arm : Type} [MeasurableSpace Omega] [Fintype Arm]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (trueMean : Arm -> Real)
    (empiricalMean : Omega -> Nat -> Arm -> Real)
    (radius : Nat -> Arm -> Real)
    (proxy : Nat -> Arm -> NNReal) (T : Nat)
    (hradius : forall t arm, t < T -> 0 <= radius t arm)
    (hsubG : forall t arm, t < T ->
      ProbabilityTheory.HasSubgaussianMGF
        (fun omega : Omega => empiricalMean omega t arm - trueMean arm)
        (proxy t arm) mu) :
    mu (finiteHorizonConfidenceBadEvent trueMean empiricalMean radius T) <=
      (Finset.range T).sum
        (fun t =>
          (Finset.univ : Finset Arm).sum
            (fun arm =>
              subGaussianOneSidedDeviationTail radius proxy t arm +
                subGaussianOneSidedDeviationTail radius proxy t arm)) := by
  exact measure_finiteHorizonConfidenceBadEvent_le_tail_sum
    mu trueMean empiricalMean radius
    (fun t arm => subGaussianOneSidedDeviationTail radius proxy t arm)
    (fun t arm => subGaussianOneSidedDeviationTail radius proxy t arm)
    T
    (fun t arm ht =>
      measure_upperConfidenceBad_le_subGaussian_tail
        mu trueMean empiricalMean radius proxy t arm
        (hradius t arm ht) (hsubG t arm ht))
    (fun t arm ht =>
      measure_lowerConfidenceBad_le_subGaussian_tail
        mu trueMean empiricalMean radius proxy t arm
        (hradius t arm ht) (hsubG t arm ht))

/--
Finite-horizon confidence bad-event bound with explicit one-sided exponential
budgets.

This is the UCB radius-budget handoff: later leaves can instantiate `budget`
with a log schedule and prove the displayed radius-square domination.
-/
theorem measure_finiteHorizonConfidenceBadEvent_le_subGaussian_exp_neg_budget_sum
    {Omega Arm : Type} [MeasurableSpace Omega] [Fintype Arm]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (trueMean : Arm -> Real)
    (empiricalMean : Omega -> Nat -> Arm -> Real)
    (radius : Nat -> Arm -> Real)
    (proxy : Nat -> Arm -> NNReal) (budget : Nat -> Arm -> Real) (T : Nat)
    (hradius : forall t arm, t < T -> 0 <= radius t arm)
    (hproxy : forall t arm, t < T ->
      0 < ((proxy t arm : NNReal) : Real))
    (hradius_sq : forall t arm, t < T ->
      2 * ((proxy t arm : NNReal) : Real) * budget t arm <=
        (radius t arm) ^ 2)
    (hsubG : forall t arm, t < T ->
      ProbabilityTheory.HasSubgaussianMGF
        (fun omega : Omega => empiricalMean omega t arm - trueMean arm)
        (proxy t arm) mu) :
    mu (finiteHorizonConfidenceBadEvent trueMean empiricalMean radius T) <=
      (Finset.range T).sum
        (fun t =>
          (Finset.univ : Finset Arm).sum
            (fun arm =>
              ENNReal.ofReal (Real.exp (-(budget t arm))) +
                ENNReal.ofReal (Real.exp (-(budget t arm))))) := by
  exact measure_finiteHorizonConfidenceBadEvent_le_tail_sum
    mu trueMean empiricalMean radius
    (fun t arm => ENNReal.ofReal (Real.exp (-(budget t arm))))
    (fun t arm => ENNReal.ofReal (Real.exp (-(budget t arm))))
    T
    (fun t arm ht =>
      measure_upperConfidenceBad_le_subGaussian_exp_neg_budget
        mu trueMean empiricalMean radius proxy budget t arm
        (hradius t arm ht) (hproxy t arm ht)
        (hradius_sq t arm ht) (hsubG t arm ht))
    (fun t arm ht =>
      measure_lowerConfidenceBad_le_subGaussian_exp_neg_budget
        mu trueMean empiricalMean radius proxy budget t arm
        (hradius t arm ht) (hproxy t arm ht)
        (hradius_sq t arm ht) (hsubG t arm ht))

/--
Finite-horizon confidence bad-event bound for the concrete square-root budget
radius.

This is the direct UCB-facing consumer for later logarithmic budget schedules.
-/
theorem measure_finiteHorizonConfidenceBadEvent_le_subGaussian_budgetRadius_sum
    {Omega Arm : Type} [MeasurableSpace Omega] [Fintype Arm]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (trueMean : Arm -> Real)
    (empiricalMean : Omega -> Nat -> Arm -> Real)
    (proxy : Nat -> Arm -> NNReal) (budget : Nat -> Arm -> Real) (T : Nat)
    (hproxy : forall t arm, t < T ->
      0 < ((proxy t arm : NNReal) : Real))
    (hsubG : forall t arm, t < T ->
      ProbabilityTheory.HasSubgaussianMGF
        (fun omega : Omega => empiricalMean omega t arm - trueMean arm)
        (proxy t arm) mu) :
    mu (finiteHorizonConfidenceBadEvent trueMean empiricalMean
        (subGaussianBudgetRadius proxy budget) T) <=
      (Finset.range T).sum
        (fun t =>
          (Finset.univ : Finset Arm).sum
            (fun arm =>
              ENNReal.ofReal (Real.exp (-(budget t arm))) +
                ENNReal.ofReal (Real.exp (-(budget t arm))))) := by
  exact measure_finiteHorizonConfidenceBadEvent_le_subGaussian_exp_neg_budget_sum
    mu trueMean empiricalMean
    (subGaussianBudgetRadius proxy budget) proxy budget T
    (fun t arm _ht =>
      subGaussianBudgetRadius_nonneg proxy budget t arm)
    hproxy
    (fun t arm _ht =>
      subGaussianBudgetRadius_sq_domination proxy budget t arm)
    hsubG

/--
Elementary log-budget simplification used by UCB tail producers.

The positivity hypothesis is the regularity contract for later concrete
schedules such as `scale = T * |A| / delta`.
-/
theorem exp_neg_log_eq_inv {x : Real} (hx : 0 < x) :
    Real.exp (-(Real.log x)) = x⁻¹ := by
  rw [Real.exp_neg, Real.exp_log hx]

/--
Concrete square-root radius with a logarithmic budget.

This is still schedule-agnostic: `scale` is the positive quantity whose inverse
will become the one-sided tail budget after simplifying `exp (-log scale)`.
-/
noncomputable def subGaussianLogBudgetRadius
    {Arm : Type}
    (proxy : Nat -> Arm -> NNReal) (scale : Nat -> Arm -> Real) :
    Nat -> Arm -> Real :=
  subGaussianBudgetRadius proxy (fun t arm => Real.log (scale t arm))

@[simp] theorem subGaussianLogBudgetRadius_apply
    {Arm : Type}
    (proxy : Nat -> Arm -> NNReal) (scale : Nat -> Arm -> Real)
    (t : Nat) (arm : Arm) :
    subGaussianLogBudgetRadius proxy scale t arm =
      Real.sqrt
        (2 * ((proxy t arm : NNReal) : Real) * Real.log (scale t arm)) := rfl

/-- The logarithmic square-root budget radius is nonnegative. -/
theorem subGaussianLogBudgetRadius_nonneg
    {Arm : Type}
    (proxy : Nat -> Arm -> NNReal) (scale : Nat -> Arm -> Real)
    (t : Nat) (arm : Arm) :
    0 <= subGaussianLogBudgetRadius proxy scale t arm := by
  simpa [subGaussianLogBudgetRadius] using
    subGaussianBudgetRadius_nonneg proxy
      (fun t arm => Real.log (scale t arm)) t arm

/--
The logarithmic square-root budget radius satisfies the square-domination
contract with budget `log scale`.
-/
theorem subGaussianLogBudgetRadius_sq_domination
    {Arm : Type}
    (proxy : Nat -> Arm -> NNReal) (scale : Nat -> Arm -> Real)
    (t : Nat) (arm : Arm) :
    2 * ((proxy t arm : NNReal) : Real) * Real.log (scale t arm) <=
      (subGaussianLogBudgetRadius proxy scale t arm) ^ 2 := by
  simpa [subGaussianLogBudgetRadius] using
    subGaussianBudgetRadius_sq_domination proxy
      (fun t arm => Real.log (scale t arm)) t arm

/--
One-sided sub-Gaussian tail bound specialized to a logarithmic square-root
budget radius.
-/
theorem subGaussianOneSidedDeviationTail_logBudgetRadius_le_inv_scale
    {Arm : Type}
    (proxy : Nat -> Arm -> NNReal) (scale : Nat -> Arm -> Real)
    (t : Nat) (arm : Arm)
    (hproxy : 0 < ((proxy t arm : NNReal) : Real))
    (hscale : 0 < scale t arm) :
    subGaussianOneSidedDeviationTail
        (subGaussianLogBudgetRadius proxy scale) proxy t arm <=
      ENNReal.ofReal ((scale t arm)⁻¹) := by
  have htail :=
    subGaussianOneSidedDeviationTail_budgetRadius_le_exp_neg_budget
      proxy (fun t arm => Real.log (scale t arm)) t arm hproxy
  simpa [subGaussianLogBudgetRadius, exp_neg_log_eq_inv hscale] using htail

/--
Single-time upper-confidence failure bound for the logarithmic square-root
budget radius.
-/
theorem measure_upperConfidenceBad_le_subGaussian_logBudgetRadius
    {Omega Arm : Type} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (trueMean : Arm -> Real)
    (empiricalMean : Omega -> Nat -> Arm -> Real)
    (proxy : Nat -> Arm -> NNReal) (scale : Nat -> Arm -> Real)
    (t : Nat) (arm : Arm)
    (hproxy : 0 < ((proxy t arm : NNReal) : Real))
    (hscale : 0 < scale t arm)
    (hsubG :
      ProbabilityTheory.HasSubgaussianMGF
        (fun omega : Omega => empiricalMean omega t arm - trueMean arm)
        (proxy t arm) mu) :
    mu (upperConfidenceBad trueMean
        (fun omega arm => empiricalMean omega t arm)
        (subGaussianLogBudgetRadius proxy scale t) arm) <=
      ENNReal.ofReal ((scale t arm)⁻¹) := by
  have htail :=
    measure_upperConfidenceBad_le_subGaussian_budgetRadius
      mu trueMean empiricalMean proxy
      (fun t arm => Real.log (scale t arm)) t arm hproxy hsubG
  simpa [subGaussianLogBudgetRadius, exp_neg_log_eq_inv hscale] using htail

/--
Single-time lower-confidence failure bound for the logarithmic square-root
budget radius.
-/
theorem measure_lowerConfidenceBad_le_subGaussian_logBudgetRadius
    {Omega Arm : Type} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (trueMean : Arm -> Real)
    (empiricalMean : Omega -> Nat -> Arm -> Real)
    (proxy : Nat -> Arm -> NNReal) (scale : Nat -> Arm -> Real)
    (t : Nat) (arm : Arm)
    (hproxy : 0 < ((proxy t arm : NNReal) : Real))
    (hscale : 0 < scale t arm)
    (hsubG :
      ProbabilityTheory.HasSubgaussianMGF
        (fun omega : Omega => empiricalMean omega t arm - trueMean arm)
        (proxy t arm) mu) :
    mu (lowerConfidenceBad trueMean
        (fun omega arm => empiricalMean omega t arm)
        (subGaussianLogBudgetRadius proxy scale t) arm) <=
      ENNReal.ofReal ((scale t arm)⁻¹) := by
  have htail :=
    measure_lowerConfidenceBad_le_subGaussian_budgetRadius
      mu trueMean empiricalMean proxy
      (fun t arm => Real.log (scale t arm)) t arm hproxy hsubG
  simpa [subGaussianLogBudgetRadius, exp_neg_log_eq_inv hscale] using htail

/--
Finite-horizon confidence bad-event bound for logarithmic square-root budget
radii.

This is the schedule-agnostic log-budget producer. Later UCB leaves can set
`scale t arm` to a concrete positive expression and then simplify the double
sum.
-/
theorem measure_finiteHorizonConfidenceBadEvent_le_subGaussian_logBudgetRadius_inv_scale_sum
    {Omega Arm : Type} [MeasurableSpace Omega] [Fintype Arm]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (trueMean : Arm -> Real)
    (empiricalMean : Omega -> Nat -> Arm -> Real)
    (proxy : Nat -> Arm -> NNReal) (scale : Nat -> Arm -> Real) (T : Nat)
    (hproxy : forall t arm, t < T ->
      0 < ((proxy t arm : NNReal) : Real))
    (hscale : forall t arm, t < T -> 0 < scale t arm)
    (hsubG : forall t arm, t < T ->
      ProbabilityTheory.HasSubgaussianMGF
        (fun omega : Omega => empiricalMean omega t arm - trueMean arm)
        (proxy t arm) mu) :
    mu (finiteHorizonConfidenceBadEvent trueMean empiricalMean
        (subGaussianLogBudgetRadius proxy scale) T) <=
      (Finset.range T).sum
        (fun t =>
          (Finset.univ : Finset Arm).sum
            (fun arm =>
              ENNReal.ofReal ((scale t arm)⁻¹) +
                ENNReal.ofReal ((scale t arm)⁻¹))) := by
  have htail :
      mu (finiteHorizonConfidenceBadEvent trueMean empiricalMean
          (subGaussianLogBudgetRadius proxy scale) T) <=
        (Finset.range T).sum
          (fun t =>
            (Finset.univ : Finset Arm).sum
              (fun arm =>
                ENNReal.ofReal
                    (Real.exp (-(Real.log (scale t arm)))) +
                  ENNReal.ofReal
                    (Real.exp (-(Real.log (scale t arm)))))) := by
    simpa [subGaussianLogBudgetRadius] using
      measure_finiteHorizonConfidenceBadEvent_le_subGaussian_budgetRadius_sum
        mu trueMean empiricalMean proxy
        (fun t arm => Real.log (scale t arm)) T hproxy hsubG
  exact htail.trans
    (Finset.sum_le_sum (fun t ht =>
      Finset.sum_le_sum (fun arm _harm => by
        simp [exp_neg_log_eq_inv (hscale t arm (Finset.mem_range.mp ht))])))

/--
Logarithmic square-root radius with a constant positive scale.

This is the direct finite-horizon shape for later choices such as
`scale = T * |A| / delta`.
-/
noncomputable def subGaussianConstantLogBudgetRadius
    {Arm : Type}
    (proxy : Nat -> Arm -> NNReal) (scale : Real) :
    Nat -> Arm -> Real :=
  subGaussianLogBudgetRadius proxy (fun _ _ => scale)

@[simp] theorem subGaussianConstantLogBudgetRadius_apply
    {Arm : Type}
    (proxy : Nat -> Arm -> NNReal) (scale : Real)
    (t : Nat) (arm : Arm) :
    subGaussianConstantLogBudgetRadius proxy scale t arm =
      Real.sqrt
        (2 * ((proxy t arm : NNReal) : Real) * Real.log scale) := rfl

/-- Constant logarithmic square-root budget radii are nonnegative. -/
theorem subGaussianConstantLogBudgetRadius_nonneg
    {Arm : Type}
    (proxy : Nat -> Arm -> NNReal) (scale : Real)
    (t : Nat) (arm : Arm) :
    0 <= subGaussianConstantLogBudgetRadius proxy scale t arm := by
  simpa [subGaussianConstantLogBudgetRadius] using
    subGaussianLogBudgetRadius_nonneg proxy (fun _ _ => scale) t arm

/--
Constant logarithmic square-root budget radii satisfy the square-domination
contract with budget `log scale`.
-/
theorem subGaussianConstantLogBudgetRadius_sq_domination
    {Arm : Type}
    (proxy : Nat -> Arm -> NNReal) (scale : Real)
    (t : Nat) (arm : Arm) :
    2 * ((proxy t arm : NNReal) : Real) * Real.log scale <=
      (subGaussianConstantLogBudgetRadius proxy scale t arm) ^ 2 := by
  simpa [subGaussianConstantLogBudgetRadius] using
    subGaussianLogBudgetRadius_sq_domination proxy
      (fun _ _ => scale) t arm

/--
Double finite sum of a constant inverse-scale one-sided tail budget.
-/
theorem constant_invScale_double_sum
    {Arm : Type} [Fintype Arm] (T : Nat) (scale : Real) :
    (Finset.range T).sum
        (fun _ =>
          (Finset.univ : Finset Arm).sum
            (fun _ =>
              ENNReal.ofReal scale⁻¹ + ENNReal.ofReal scale⁻¹)) =
      HSMul.hSMul T
        (HSMul.hSMul (Fintype.card Arm)
          (ENNReal.ofReal scale⁻¹ + ENNReal.ofReal scale⁻¹)) := by
  simp [Finset.sum_const]

/--
Finite-horizon confidence bad-event bound for a constant logarithmic scale,
with the time/arm double sum folded into `T` and `Fintype.card Arm`.
-/
theorem measure_finiteHorizonConfidenceBadEvent_le_subGaussian_constantLogBudgetRadius_card
    {Omega Arm : Type} [MeasurableSpace Omega] [Fintype Arm]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (trueMean : Arm -> Real)
    (empiricalMean : Omega -> Nat -> Arm -> Real)
    (proxy : Nat -> Arm -> NNReal) (scale : Real) (T : Nat)
    (hproxy : forall t arm, t < T ->
      0 < ((proxy t arm : NNReal) : Real))
    (hscale : 0 < scale)
    (hsubG : forall t arm, t < T ->
      ProbabilityTheory.HasSubgaussianMGF
        (fun omega : Omega => empiricalMean omega t arm - trueMean arm)
        (proxy t arm) mu) :
    mu (finiteHorizonConfidenceBadEvent trueMean empiricalMean
        (subGaussianConstantLogBudgetRadius proxy scale) T) <=
      HSMul.hSMul T
        (HSMul.hSMul (Fintype.card Arm)
          (ENNReal.ofReal scale⁻¹ + ENNReal.ofReal scale⁻¹)) := by
  have htail :
      mu (finiteHorizonConfidenceBadEvent trueMean empiricalMean
          (subGaussianConstantLogBudgetRadius proxy scale) T) <=
        (Finset.range T).sum
          (fun _ =>
            (Finset.univ : Finset Arm).sum
              (fun _ =>
                ENNReal.ofReal scale⁻¹ + ENNReal.ofReal scale⁻¹)) := by
    simpa [subGaussianConstantLogBudgetRadius] using
      measure_finiteHorizonConfidenceBadEvent_le_subGaussian_logBudgetRadius_inv_scale_sum
        mu trueMean empiricalMean proxy (fun _ _ => scale) T hproxy
        (fun _ _ _ => hscale) hsubG
  exact htail.trans
    (le_of_eq (constant_invScale_double_sum (Arm := Arm) T scale))

/--
Convert a constant inverse-scale finite-horizon ENNReal tail budget back to an
ordinary real budget.
-/
theorem constant_invScale_double_sum_le_of_real
    {Arm : Type} [Fintype Arm] (T : Nat) (scale delta : Real)
    (hscale : 0 < scale)
    (hreal :
      (T : Real) *
        ((Fintype.card Arm : Real) * (scale⁻¹ + scale⁻¹)) <= delta) :
    HSMul.hSMul T
        (HSMul.hSMul (Fintype.card Arm)
          (ENNReal.ofReal scale⁻¹ + ENNReal.ofReal scale⁻¹)) <=
      ENNReal.ofReal delta := by
  have hscale_inv_nonneg : 0 <= scale⁻¹ := inv_nonneg.mpr hscale.le
  have hadd : ENNReal.ofReal (scale⁻¹ + scale⁻¹) =
      ENNReal.ofReal scale⁻¹ + ENNReal.ofReal scale⁻¹ := by
    exact ENNReal.ofReal_add hscale_inv_nonneg hscale_inv_nonneg
  rw [hadd.symm]
  rw [nsmul_eq_mul, nsmul_eq_mul]
  rw [(ENNReal.ofReal_natCast (Fintype.card Arm)).symm]
  rw [(ENNReal.ofReal_natCast T).symm]
  rw [(ENNReal.ofReal_mul (Nat.cast_nonneg (Fintype.card Arm))).symm]
  rw [(ENNReal.ofReal_mul (Nat.cast_nonneg T)).symm]
  exact ENNReal.ofReal_le_ofReal hreal

/--
Textbook UCB finite-horizon scale for allocating two one-sided tails across
`T` times and all arms.

The factor `2` accounts for upper and lower confidence failures.
-/
noncomputable def textbookDeltaScale
    {Arm : Type} [Fintype Arm] (T : Nat) (delta : Real) : Real :=
  (2 * (T : Real) * (Fintype.card Arm : Real)) / delta

/-- The textbook delta scale is positive under the usual horizon/arm/delta contracts. -/
theorem textbookDeltaScale_pos
    {Arm : Type} [Fintype Arm] [Nonempty Arm]
    (T : Nat) (delta : Real) (hT : 0 < T) (hdelta : 0 < delta) :
    0 < textbookDeltaScale (Arm := Arm) T delta := by
  have hcard : 0 < Fintype.card Arm := Fintype.card_pos
  unfold textbookDeltaScale
  positivity

/--
The textbook delta scale makes the folded constant inverse-scale tail budget
equal to `delta` at the real-number level.
-/
theorem textbookDeltaScale_total_inv_budget_eq_delta
    {Arm : Type} [Fintype Arm] [Nonempty Arm]
    (T : Nat) (delta : Real) (hT : 0 < T) (hdelta : 0 < delta) :
    (T : Real) *
        ((Fintype.card Arm : Real) *
          ((textbookDeltaScale (Arm := Arm) T delta)⁻¹ +
            (textbookDeltaScale (Arm := Arm) T delta)⁻¹)) =
      delta := by
  have hcard_nat : 0 < Fintype.card Arm := Fintype.card_pos
  have hTpos : 0 < (T : Real) := by exact_mod_cast hT
  have hcard_pos : 0 < (Fintype.card Arm : Real) := by
    exact_mod_cast hcard_nat
  have hT_ne : Ne (T : Real) 0 := ne_of_gt hTpos
  have hcard_ne : Ne (Fintype.card Arm : Real) 0 := ne_of_gt hcard_pos
  have hdelta_ne : Ne delta 0 := ne_of_gt hdelta
  unfold textbookDeltaScale
  field_simp [hT_ne, hcard_ne, hdelta_ne]
  ring

/--
The folded constant-scale UCB tail budget with textbook delta scale is bounded
by `delta`.
-/
theorem constant_invScale_double_sum_textbookDeltaScale_le_delta
    {Arm : Type} [Fintype Arm] [Nonempty Arm]
    (T : Nat) (delta : Real) (hT : 0 < T) (hdelta : 0 < delta) :
    HSMul.hSMul T
        (HSMul.hSMul (Fintype.card Arm)
          (ENNReal.ofReal (textbookDeltaScale (Arm := Arm) T delta)⁻¹ +
            ENNReal.ofReal (textbookDeltaScale (Arm := Arm) T delta)⁻¹)) <=
      ENNReal.ofReal delta := by
  exact constant_invScale_double_sum_le_of_real
    (Arm := Arm) T (textbookDeltaScale (Arm := Arm) T delta) delta
    (textbookDeltaScale_pos (Arm := Arm) T delta hT hdelta)
    (le_of_eq
      (textbookDeltaScale_total_inv_budget_eq_delta
        (Arm := Arm) T delta hT hdelta))

/-- Textbook delta-scale logarithmic UCB radius. -/
noncomputable def subGaussianTextbookDeltaRadius
    {Arm : Type} [Fintype Arm]
    (proxy : Nat -> Arm -> NNReal) (T : Nat) (delta : Real) :
    Nat -> Arm -> Real :=
  subGaussianConstantLogBudgetRadius proxy
    (textbookDeltaScale (Arm := Arm) T delta)

@[simp] theorem subGaussianTextbookDeltaRadius_apply
    {Arm : Type} [Fintype Arm]
    (proxy : Nat -> Arm -> NNReal) (T : Nat) (delta : Real)
    (t : Nat) (arm : Arm) :
    subGaussianTextbookDeltaRadius proxy T delta t arm =
      Real.sqrt
        (2 * ((proxy t arm : NNReal) : Real) *
          Real.log (textbookDeltaScale (Arm := Arm) T delta)) := rfl

/--
Finite-horizon confidence bad-event bound for the textbook delta-scale
logarithmic UCB radius.
-/
theorem measure_finiteHorizonConfidenceBadEvent_le_subGaussian_textbookDeltaRadius_delta
    {Omega Arm : Type} [MeasurableSpace Omega] [Fintype Arm] [Nonempty Arm]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (trueMean : Arm -> Real)
    (empiricalMean : Omega -> Nat -> Arm -> Real)
    (proxy : Nat -> Arm -> NNReal) (T : Nat) (delta : Real)
    (hT : 0 < T) (hdelta : 0 < delta)
    (hproxy : forall t arm, t < T ->
      0 < ((proxy t arm : NNReal) : Real))
    (hsubG : forall t arm, t < T ->
      ProbabilityTheory.HasSubgaussianMGF
        (fun omega : Omega => empiricalMean omega t arm - trueMean arm)
        (proxy t arm) mu) :
    mu (finiteHorizonConfidenceBadEvent trueMean empiricalMean
        (subGaussianTextbookDeltaRadius proxy T delta) T) <=
      ENNReal.ofReal delta := by
  have htail :=
    measure_finiteHorizonConfidenceBadEvent_le_subGaussian_constantLogBudgetRadius_card
      mu trueMean empiricalMean proxy
      (textbookDeltaScale (Arm := Arm) T delta) T hproxy
      (textbookDeltaScale_pos (Arm := Arm) T delta hT hdelta) hsubG
  exact htail.trans
    (constant_invScale_double_sum_textbookDeltaScale_le_delta
      (Arm := Arm) T delta hT hdelta)

/--
Large-gap score-max events under the textbook delta radius are controlled by
the finite-horizon confidence budget.

This is a probability-facing handoff for later pull-count arguments: once a
chosen arm has gap larger than twice its current radius, selecting it by UCB
score can only happen on the confidence bad event.
-/
theorem measure_scoreMaxEvent_le_subGaussian_textbookDeltaRadius_delta_of_gap
    {Omega Arm : Type} [MeasurableSpace Omega] [Fintype Arm] [Nonempty Arm]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (trueMean : Arm -> Real)
    (empiricalMean : Omega -> Nat -> Arm -> Real)
    (proxy : Nat -> Arm -> NNReal) (T : Nat) (delta : Real)
    (t : Nat) (best chosen : Arm)
    (hT : 0 < T) (hdelta : 0 < delta) (ht : t < T)
    (hgap_large :
      2 * subGaussianTextbookDeltaRadius proxy T delta t chosen <
        meanGap trueMean best chosen)
    (hproxy : forall t arm, t < T ->
      0 < ((proxy t arm : NNReal) : Real))
    (hsubG : forall t arm, t < T ->
      ProbabilityTheory.HasSubgaussianMGF
        (fun omega : Omega => empiricalMean omega t arm - trueMean arm)
        (proxy t arm) mu) :
    mu {omega : Omega |
      confidenceScore (empiricalMean omega t)
          (subGaussianTextbookDeltaRadius proxy T delta t) best <=
        confidenceScore (empiricalMean omega t)
          (subGaussianTextbookDeltaRadius proxy T delta t) chosen} <=
      ENNReal.ofReal delta := by
  have hsubset :
      {omega : Omega |
        confidenceScore (empiricalMean omega t)
            (subGaussianTextbookDeltaRadius proxy T delta t) best <=
          confidenceScore (empiricalMean omega t)
            (subGaussianTextbookDeltaRadius proxy T delta t) chosen} ⊆
        finiteHorizonConfidenceBadEvent trueMean empiricalMean
          (subGaussianTextbookDeltaRadius proxy T delta) T :=
    scoreMaxEvent_subset_finiteHorizonConfidenceBadEvent_of_two_radius_lt_meanGap
      trueMean empiricalMean (subGaussianTextbookDeltaRadius proxy T delta)
      T t best chosen ht hgap_large
  exact (measure_mono hsubset).trans
    (measure_finiteHorizonConfidenceBadEvent_le_subGaussian_textbookDeltaRadius_delta
      mu trueMean empiricalMean proxy T delta hT hdelta hproxy hsubG)

/--
Selecting `chosen` is contained in the corresponding UCB score-max event when
the action trace exposes score maximality against `best`.

This is intentionally abstract: the concrete argmax/tie-breaking policy can
later discharge `hscore_of_selected`.
-/
theorem selectedEvent_subset_scoreMaxEvent_of_action_score_max
    {Omega Arm : Type}
    (empiricalMean : Omega -> Nat -> Arm -> Real)
    (radius : Nat -> Arm -> Real)
    (action : Omega -> Nat -> Arm)
    (t : Nat) (best chosen : Arm)
    (hscore_of_selected : forall omega,
      action omega t = chosen ->
        confidenceScore (empiricalMean omega t) (radius t) best <=
          confidenceScore (empiricalMean omega t) (radius t) chosen) :
    Set.Subset
      {omega : Omega | action omega t = chosen}
      {omega : Omega |
        confidenceScore (empiricalMean omega t) (radius t) best <=
          confidenceScore (empiricalMean omega t) (radius t) chosen} := by
  intro omega hselected
  exact hscore_of_selected omega hselected

/--
Selected large-gap arms inherit the textbook delta probability budget once the
selected-action trace certifies UCB score maximality.

This is the action-trace-facing bridge before a concrete pull-count summation:
selection plus a large-gap radius condition implies that the selected event is
covered by the finite-horizon confidence bad event.
-/
theorem measure_selectedLargeGapEvent_le_subGaussian_textbookDeltaRadius_delta
    {Omega Arm : Type} [MeasurableSpace Omega] [Fintype Arm] [Nonempty Arm]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (trueMean : Arm -> Real)
    (empiricalMean : Omega -> Nat -> Arm -> Real)
    (action : Omega -> Nat -> Arm)
    (proxy : Nat -> Arm -> NNReal) (T : Nat) (delta : Real)
    (t : Nat) (best chosen : Arm)
    (hT : 0 < T) (hdelta : 0 < delta) (ht : t < T)
    (hgap_large :
      2 * subGaussianTextbookDeltaRadius proxy T delta t chosen <
        meanGap trueMean best chosen)
    (hscore_of_selected : forall omega,
      action omega t = chosen ->
        confidenceScore (empiricalMean omega t)
            (subGaussianTextbookDeltaRadius proxy T delta t) best <=
          confidenceScore (empiricalMean omega t)
            (subGaussianTextbookDeltaRadius proxy T delta t) chosen)
    (hproxy : forall t arm, t < T ->
      0 < ((proxy t arm : NNReal) : Real))
    (hsubG : forall t arm, t < T ->
      ProbabilityTheory.HasSubgaussianMGF
        (fun omega : Omega => empiricalMean omega t arm - trueMean arm)
        (proxy t arm) mu) :
    mu {omega : Omega | action omega t = chosen} <= ENNReal.ofReal delta := by
  have hsubset :
      Set.Subset
        {omega : Omega | action omega t = chosen}
        {omega : Omega |
          confidenceScore (empiricalMean omega t)
              (subGaussianTextbookDeltaRadius proxy T delta t) best <=
            confidenceScore (empiricalMean omega t)
              (subGaussianTextbookDeltaRadius proxy T delta t) chosen} :=
    selectedEvent_subset_scoreMaxEvent_of_action_score_max
      empiricalMean (subGaussianTextbookDeltaRadius proxy T delta)
      action t best chosen hscore_of_selected
  exact (measure_mono hsubset).trans
    (measure_scoreMaxEvent_le_subGaussian_textbookDeltaRadius_delta_of_gap
      mu trueMean empiricalMean proxy T delta t best chosen
      hT hdelta ht hgap_large hproxy hsubG)

/--
Finite-time selected-action events are covered by the finite-horizon confidence
bad event when every selected time in the index set has a large enough gap and
certifies UCB score maximality.

This is the event-level bridge needed before turning selected-time collections
into pull-count or suffix-time bounds.
-/
theorem selectedEventOn_subset_finiteHorizonConfidenceBadEvent_of_action_score_max
    {Omega Arm : Type} [Fintype Arm]
    (trueMean : Arm -> Real)
    (empiricalMean : Omega -> Nat -> Arm -> Real)
    (radius : Nat -> Arm -> Real)
    (action : Omega -> Nat -> Arm)
    (T : Nat) (times : Finset Nat)
    (best chosen : Arm)
    (htimes : forall t, t ∈ times -> t < T)
    (hscore_of_selected : forall omega t, t ∈ times ->
      action omega t = chosen ->
        confidenceScore (empiricalMean omega t) (radius t) best <=
          confidenceScore (empiricalMean omega t) (radius t) chosen)
    (hgap_large : forall t, t ∈ times ->
      2 * radius t chosen < meanGap trueMean best chosen) :
    Set.Subset
      {omega : Omega | exists t, t ∈ times /\ action omega t = chosen}
      (finiteHorizonConfidenceBadEvent trueMean empiricalMean radius T) := by
  intro omega hselected
  rcases hselected with ⟨t, ht_mem, hselected_t⟩
  exact
    mem_finiteHorizonConfidenceBadEvent_of_two_radius_lt_meanGap_of_score_max
      trueMean empiricalMean radius T omega t best chosen
      (htimes t ht_mem)
      (hscore_of_selected omega t ht_mem hselected_t)
      (hgap_large t ht_mem)

/--
The textbook delta budget also controls the event that a fixed arm is selected
at any time from a finite index set, provided each such time satisfies the
large-gap radius condition and selected-action score maximality.
-/
theorem measure_selectedLargeGapEventOn_le_subGaussian_textbookDeltaRadius_delta
    {Omega Arm : Type} [MeasurableSpace Omega] [Fintype Arm] [Nonempty Arm]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (trueMean : Arm -> Real)
    (empiricalMean : Omega -> Nat -> Arm -> Real)
    (action : Omega -> Nat -> Arm)
    (proxy : Nat -> Arm -> NNReal) (T : Nat) (delta : Real)
    (times : Finset Nat) (best chosen : Arm)
    (hT : 0 < T) (hdelta : 0 < delta)
    (htimes : forall t, t ∈ times -> t < T)
    (hgap_large : forall t, t ∈ times ->
      2 * subGaussianTextbookDeltaRadius proxy T delta t chosen <
        meanGap trueMean best chosen)
    (hscore_of_selected : forall omega t, t ∈ times ->
      action omega t = chosen ->
        confidenceScore (empiricalMean omega t)
            (subGaussianTextbookDeltaRadius proxy T delta t) best <=
          confidenceScore (empiricalMean omega t)
            (subGaussianTextbookDeltaRadius proxy T delta t) chosen)
    (hproxy : forall t arm, t < T ->
      0 < ((proxy t arm : NNReal) : Real))
    (hsubG : forall t arm, t < T ->
      ProbabilityTheory.HasSubgaussianMGF
        (fun omega : Omega => empiricalMean omega t arm - trueMean arm)
        (proxy t arm) mu) :
    mu {omega : Omega | exists t, t ∈ times /\ action omega t = chosen} <=
      ENNReal.ofReal delta := by
  have hsubset :
      Set.Subset
        {omega : Omega | exists t, t ∈ times /\ action omega t = chosen}
        (finiteHorizonConfidenceBadEvent trueMean empiricalMean
          (subGaussianTextbookDeltaRadius proxy T delta) T) :=
    selectedEventOn_subset_finiteHorizonConfidenceBadEvent_of_action_score_max
      trueMean empiricalMean (subGaussianTextbookDeltaRadius proxy T delta)
      action T times best chosen htimes hscore_of_selected hgap_large
  exact (measure_mono hsubset).trans
    (measure_finiteHorizonConfidenceBadEvent_le_subGaussian_textbookDeltaRadius_delta
      mu trueMean empiricalMean proxy T delta hT hdelta hproxy hsubG)

/--
Concrete confidence-score argmax version of the selected large-gap delta bound.

The score-maximality contract is discharged by `confidenceScoreArgmaxAction`,
so the remaining assumptions are the textbook radius/concentration contracts
and the large-gap condition for the selected arm.
-/
theorem measure_confidenceScoreArgmax_selectedLargeGapEvent_le_subGaussian_textbookDeltaRadius_delta
    {Omega : Type} [MeasurableSpace Omega]
    {K : Nat} (hK : 0 < K)
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (trueMean : Fin K -> Real)
    (empiricalMean : Omega -> Nat -> Fin K -> Real)
    (proxy : Nat -> Fin K -> NNReal) (T : Nat) (delta : Real)
    (t : Nat) (best chosen : Fin K)
    (hT : 0 < T) (hdelta : 0 < delta) (ht : t < T)
    (hgap_large :
      2 * subGaussianTextbookDeltaRadius proxy T delta t chosen <
        meanGap trueMean best chosen)
    (hproxy : forall t arm, t < T ->
      0 < ((proxy t arm : NNReal) : Real))
    (hsubG : forall t arm, t < T ->
      ProbabilityTheory.HasSubgaussianMGF
        (fun omega : Omega => empiricalMean omega t arm - trueMean arm)
        (proxy t arm) mu) :
    mu {omega : Omega |
      confidenceScoreArgmaxAction hK empiricalMean
        (subGaussianTextbookDeltaRadius proxy T delta) omega t = chosen} <=
      ENNReal.ofReal delta := by
  letI : Nonempty (Fin K) := ⟨Fin.mk 0 hK⟩
  exact
    measure_selectedLargeGapEvent_le_subGaussian_textbookDeltaRadius_delta
      mu trueMean empiricalMean
      (confidenceScoreArgmaxAction hK empiricalMean
        (subGaussianTextbookDeltaRadius proxy T delta))
      proxy T delta t best chosen
      hT hdelta ht hgap_large
      (by
        intro omega hselected
        exact
          confidenceScoreArgmaxAction_score_max_of_selected
            hK empiricalMean (subGaussianTextbookDeltaRadius proxy T delta)
            omega t best chosen hselected)
      hproxy hsubG

/--
Finite-time-set concrete confidence-score argmax version of the selected
large-gap delta bound.
-/
theorem measure_confidenceScoreArgmax_selectedLargeGapEventOn_le_subGaussian_textbookDeltaRadius_delta
    {Omega : Type} [MeasurableSpace Omega]
    {K : Nat} (hK : 0 < K)
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (trueMean : Fin K -> Real)
    (empiricalMean : Omega -> Nat -> Fin K -> Real)
    (proxy : Nat -> Fin K -> NNReal) (T : Nat) (delta : Real)
    (times : Finset Nat) (best chosen : Fin K)
    (hT : 0 < T) (hdelta : 0 < delta)
    (htimes : forall t, t ∈ times -> t < T)
    (hgap_large : forall t, t ∈ times ->
      2 * subGaussianTextbookDeltaRadius proxy T delta t chosen <
        meanGap trueMean best chosen)
    (hproxy : forall t arm, t < T ->
      0 < ((proxy t arm : NNReal) : Real))
    (hsubG : forall t arm, t < T ->
      ProbabilityTheory.HasSubgaussianMGF
        (fun omega : Omega => empiricalMean omega t arm - trueMean arm)
        (proxy t arm) mu) :
    mu {omega : Omega |
      exists t, t ∈ times /\
        confidenceScoreArgmaxAction hK empiricalMean
          (subGaussianTextbookDeltaRadius proxy T delta) omega t = chosen} <=
      ENNReal.ofReal delta := by
  letI : Nonempty (Fin K) := ⟨Fin.mk 0 hK⟩
  exact
    measure_selectedLargeGapEventOn_le_subGaussian_textbookDeltaRadius_delta
      mu trueMean empiricalMean
      (confidenceScoreArgmaxAction hK empiricalMean
        (subGaussianTextbookDeltaRadius proxy T delta))
      proxy T delta times best chosen
      hT hdelta htimes hgap_large
      (by
        intro omega t ht_mem hselected
        exact
          confidenceScoreArgmaxAction_score_max_of_selected
            hK empiricalMean (subGaussianTextbookDeltaRadius proxy T delta)
            omega t best chosen hselected)
      hproxy hsubG

/--
Summing the single-time concrete score-argmax selected large-gap bounds over a
finite time set gives a finite-count probability budget.

This is the first counting-facing UCB bridge: it keeps the statement as a sum
of selected-action event probabilities before converting it to a lower
integral of selected-time indicators.
-/
theorem sum_measure_confidenceScoreArgmax_selectedLargeGapEventOn_le_card_mul_delta
    {Omega : Type} [MeasurableSpace Omega]
    {K : Nat} (hK : 0 < K)
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (trueMean : Fin K -> Real)
    (empiricalMean : Omega -> Nat -> Fin K -> Real)
    (proxy : Nat -> Fin K -> NNReal) (T : Nat) (delta : Real)
    (times : Finset Nat) (best chosen : Fin K)
    (hT : 0 < T) (hdelta : 0 < delta)
    (htimes : forall t, t ∈ times -> t < T)
    (hgap_large : forall t, t ∈ times ->
      2 * subGaussianTextbookDeltaRadius proxy T delta t chosen <
        meanGap trueMean best chosen)
    (hproxy : forall t arm, t < T ->
      0 < ((proxy t arm : NNReal) : Real))
    (hsubG : forall t arm, t < T ->
      ProbabilityTheory.HasSubgaussianMGF
        (fun omega : Omega => empiricalMean omega t arm - trueMean arm)
        (proxy t arm) mu) :
    times.sum
        (fun t : Nat =>
          mu {omega : Omega |
            confidenceScoreArgmaxAction hK empiricalMean
              (subGaussianTextbookDeltaRadius proxy T delta) omega t =
                chosen}) <=
      (times.card : ENNReal) * ENNReal.ofReal delta := by
  calc
    times.sum
        (fun t : Nat =>
          mu {omega : Omega |
            confidenceScoreArgmaxAction hK empiricalMean
              (subGaussianTextbookDeltaRadius proxy T delta) omega t =
                chosen})
        <=
      times.sum (fun _t : Nat => ENNReal.ofReal delta) := by
        exact Finset.sum_le_sum
          (by
            intro t ht_mem
            exact
              measure_confidenceScoreArgmax_selectedLargeGapEvent_le_subGaussian_textbookDeltaRadius_delta
                hK mu trueMean empiricalMean proxy T delta t best chosen
                hT hdelta (htimes t ht_mem) (hgap_large t ht_mem)
                hproxy hsubG)
    _ = (times.card : ENNReal) * ENNReal.ofReal delta := by
        simp [Finset.sum_const, nsmul_eq_mul]

/--
Lower-integral selected-count budget for concrete score-argmax UCB over an
explicit finite time set.

The integrand is the finite sum of selected-action indicators over `times`.
This is not yet the recursive `pullCount`, but it is the expectation-facing
finite-count surface needed to bridge the selected-event probability bounds
into pull-count and regret arguments.
-/
theorem lintegral_confidenceScoreArgmax_selectedLargeGapCountOn_le_card_mul_delta
    {Omega : Type} [MeasurableSpace Omega]
    {K : Nat} (hK : 0 < K)
    [MeasurableSpace (Fin K)] [MeasurableSingletonClass (Fin K)]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (trueMean : Fin K -> Real)
    (empiricalMean : Omega -> Nat -> Fin K -> Real)
    (proxy : Nat -> Fin K -> NNReal) (T : Nat) (delta : Real)
    (times : Finset Nat) (best chosen : Fin K)
    (hT : 0 < T) (hdelta : 0 < delta)
    (htimes : forall t, t ∈ times -> t < T)
    (hgap_large : forall t, t ∈ times ->
      2 * subGaussianTextbookDeltaRadius proxy T delta t chosen <
        meanGap trueMean best chosen)
    (haction : forall t : Nat,
      Measurable
        (fun omega : Omega =>
          confidenceScoreArgmaxAction hK empiricalMean
            (subGaussianTextbookDeltaRadius proxy T delta) omega t))
    (hproxy : forall t arm, t < T ->
      0 < ((proxy t arm : NNReal) : Real))
    (hsubG : forall t arm, t < T ->
      ProbabilityTheory.HasSubgaussianMGF
        (fun omega : Omega => empiricalMean omega t arm - trueMean arm)
        (proxy t arm) mu) :
    MeasureTheory.lintegral mu
      (fun omega : Omega =>
        times.sum
          (fun t : Nat =>
            (({omega' : Omega |
              confidenceScoreArgmaxAction hK empiricalMean
                (subGaussianTextbookDeltaRadius proxy T delta) omega' t =
                  chosen} : Set Omega).indicator
              (1 : Omega -> ENNReal)) omega)) <=
      (times.card : ENNReal) * ENNReal.ofReal delta := by
  rw [lintegral_finset_sum_actionTrace_eval_eq_indicator_one
    (mu := mu)
    (action :=
      confidenceScoreArgmaxAction hK empiricalMean
        (subGaussianTextbookDeltaRadius proxy T delta))
    (haction := haction)
    (a := chosen)
    (s := times)]
  exact
    sum_measure_confidenceScoreArgmax_selectedLargeGapEventOn_le_card_mul_delta
      hK mu trueMean empiricalMean proxy T delta times best chosen
      hT hdelta htimes hgap_large hproxy hsubG

/--
Recursive pull-count lower-integral budget for a concrete score-argmax UCB arm
whose large-gap condition holds throughout the horizon.

This specializes the finite-time selected-count bridge to `Finset.range T` and
then uses the existing project-local `pullCount` lower-integral identity. It
does not yet split the horizon into small-radius and large-radius phases.
-/
theorem lintegral_confidenceScoreArgmax_pullCount_le_horizon_mul_delta
    {Omega : Type} [MeasurableSpace Omega]
    {K : Nat} (hK : 0 < K)
    [MeasurableSpace (Fin K)] [MeasurableSingletonClass (Fin K)]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (trueMean : Fin K -> Real)
    (empiricalMean : Omega -> Nat -> Fin K -> Real)
    (proxy : Nat -> Fin K -> NNReal) (T : Nat) (delta : Real)
    (best chosen : Fin K)
    (hT : 0 < T) (hdelta : 0 < delta)
    (hgap_large : forall t, t < T ->
      2 * subGaussianTextbookDeltaRadius proxy T delta t chosen <
        meanGap trueMean best chosen)
    (haction : forall t : Nat,
      Measurable
        (fun omega : Omega =>
          confidenceScoreArgmaxAction hK empiricalMean
            (subGaussianTextbookDeltaRadius proxy T delta) omega t))
    (hproxy : forall t arm, t < T ->
      0 < ((proxy t arm : NNReal) : Real))
    (hsubG : forall t arm, t < T ->
      ProbabilityTheory.HasSubgaussianMGF
        (fun omega : Omega => empiricalMean omega t arm - trueMean arm)
        (proxy t arm) mu) :
    MeasureTheory.lintegral mu
      (fun omega : Omega =>
        ((pullCount
          ((confidenceScoreArgmaxAction hK empiricalMean
            (subGaussianTextbookDeltaRadius proxy T delta)) omega)
          chosen T : Nat) : ENNReal)) <=
      (T : ENNReal) * ENNReal.ofReal delta := by
  rw [lintegral_natCast_pullCount_eq_sum_measure_actionTrace_eval_eq
    (mu := mu)
    (action :=
      confidenceScoreArgmaxAction hK empiricalMean
        (subGaussianTextbookDeltaRadius proxy T delta))
    (haction := haction)
    (a := chosen)
    (n := T)]
  simpa [Finset.card_range] using
    sum_measure_confidenceScoreArgmax_selectedLargeGapEventOn_le_card_mul_delta
      hK mu trueMean empiricalMean proxy T delta (Finset.range T) best chosen
      hT hdelta
      (by
        intro t ht_mem
        simpa using ht_mem)
      (by
        intro t ht_mem
        exact hgap_large t (by simpa using ht_mem))
      hproxy hsubG

/--
Threshold/suffix-shaped pull-count budget for concrete score-argmax UCB.

Times in `freeTimes` are charged by the trivial probability bound `1`; every
other horizon time must be listed in `chargedTimes` and satisfy the large-gap
condition, so those selected events are charged by `delta`.
-/
theorem lintegral_confidenceScoreArgmax_pullCount_le_free_or_delta_sum
    {Omega : Type} [MeasurableSpace Omega]
    {K : Nat} (hK : 0 < K)
    [MeasurableSpace (Fin K)] [MeasurableSingletonClass (Fin K)]
    (mu : Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    (trueMean : Fin K -> Real)
    (empiricalMean : Omega -> Nat -> Fin K -> Real)
    (proxy : Nat -> Fin K -> NNReal) (T : Nat) (delta : Real)
    (freeTimes chargedTimes : Finset Nat) (best chosen : Fin K)
    (hT : 0 < T) (hdelta : 0 < delta)
    (hcharged_of_not_free : forall t, t < T -> t ∉ freeTimes -> t ∈ chargedTimes)
    (hgap_large : forall t, t ∈ chargedTimes ->
      2 * subGaussianTextbookDeltaRadius proxy T delta t chosen <
        meanGap trueMean best chosen)
    (haction : forall t : Nat,
      Measurable
        (fun omega : Omega =>
          confidenceScoreArgmaxAction hK empiricalMean
            (subGaussianTextbookDeltaRadius proxy T delta) omega t))
    (hproxy : forall t arm, t < T ->
      0 < ((proxy t arm : NNReal) : Real))
    (hsubG : forall t arm, t < T ->
      ProbabilityTheory.HasSubgaussianMGF
        (fun omega : Omega => empiricalMean omega t arm - trueMean arm)
        (proxy t arm) mu) :
    MeasureTheory.lintegral mu
      (fun omega : Omega =>
        ((pullCount
          ((confidenceScoreArgmaxAction hK empiricalMean
            (subGaussianTextbookDeltaRadius proxy T delta)) omega)
          chosen T : Nat) : ENNReal)) <=
      (Finset.range T).sum
        (fun t : Nat =>
          if t ∈ freeTimes then (1 : ENNReal) else ENNReal.ofReal delta) := by
  rw [lintegral_natCast_pullCount_eq_sum_measure_actionTrace_eval_eq
    (mu := mu)
    (action :=
      confidenceScoreArgmaxAction hK empiricalMean
        (subGaussianTextbookDeltaRadius proxy T delta))
    (haction := haction)
    (a := chosen)
    (n := T)]
  exact Finset.sum_le_sum
    (by
      intro t ht_mem
      have ht : t < T := by
        simpa using ht_mem
      by_cases hfree : t ∈ freeTimes
      · have hle_univ :
            mu {omega : Omega |
              confidenceScoreArgmaxAction hK empiricalMean
                (subGaussianTextbookDeltaRadius proxy T delta) omega t =
                  chosen} <= mu Set.univ :=
          measure_mono (Set.subset_univ _)
        simpa [hfree, MeasureTheory.IsProbabilityMeasure.measure_univ] using
          hle_univ
      · have hcharged : t ∈ chargedTimes :=
          hcharged_of_not_free t ht hfree
        have hdelta_bound :=
          measure_confidenceScoreArgmax_selectedLargeGapEvent_le_subGaussian_textbookDeltaRadius_delta
            hK mu trueMean empiricalMean proxy T delta t best chosen
            hT hdelta ht (hgap_large t hcharged) hproxy hsubG
        simpa [hfree] using hdelta_bound)

/--
Budgeted form of the threshold/suffix pull-count split.

The only new input is a bound on the free-time indicator sum. Future
radius-threshold leaves can discharge `hfree_budget` by proving a cardinality
bound for the low-radius/small-sample times.
-/
theorem lintegral_confidenceScoreArgmax_pullCount_le_freeBudget_add_horizon_delta
    {Omega : Type} [MeasurableSpace Omega]
    {K : Nat} (hK : 0 < K)
    [MeasurableSpace (Fin K)] [MeasurableSingletonClass (Fin K)]
    (mu : Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    (trueMean : Fin K -> Real)
    (empiricalMean : Omega -> Nat -> Fin K -> Real)
    (proxy : Nat -> Fin K -> NNReal) (T : Nat) (delta : Real)
    (freeTimes chargedTimes : Finset Nat) (freeBudget : ENNReal)
    (best chosen : Fin K)
    (hT : 0 < T) (hdelta : 0 < delta)
    (hfree_budget :
      (Finset.range T).sum
        (fun t : Nat =>
          if t ∈ freeTimes then (1 : ENNReal) else 0) <= freeBudget)
    (hcharged_of_not_free : forall t, t < T -> t ∉ freeTimes -> t ∈ chargedTimes)
    (hgap_large : forall t, t ∈ chargedTimes ->
      2 * subGaussianTextbookDeltaRadius proxy T delta t chosen <
        meanGap trueMean best chosen)
    (haction : forall t : Nat,
      Measurable
        (fun omega : Omega =>
          confidenceScoreArgmaxAction hK empiricalMean
            (subGaussianTextbookDeltaRadius proxy T delta) omega t))
    (hproxy : forall t arm, t < T ->
      0 < ((proxy t arm : NNReal) : Real))
    (hsubG : forall t arm, t < T ->
      ProbabilityTheory.HasSubgaussianMGF
        (fun omega : Omega => empiricalMean omega t arm - trueMean arm)
        (proxy t arm) mu) :
    MeasureTheory.lintegral mu
      (fun omega : Omega =>
        ((pullCount
          ((confidenceScoreArgmaxAction hK empiricalMean
            (subGaussianTextbookDeltaRadius proxy T delta)) omega)
          chosen T : Nat) : ENNReal)) <=
      freeBudget + (T : ENNReal) * ENNReal.ofReal delta := by
  have hsplit :=
    lintegral_confidenceScoreArgmax_pullCount_le_free_or_delta_sum
      hK mu trueMean empiricalMean proxy T delta freeTimes chargedTimes
      best chosen hT hdelta hcharged_of_not_free hgap_large
      haction hproxy hsubG
  have hsum :
      (Finset.range T).sum
        (fun t : Nat =>
          if t ∈ freeTimes then (1 : ENNReal) else ENNReal.ofReal delta)
        <=
      freeBudget + (T : ENNReal) * ENNReal.ofReal delta := by
    calc
      (Finset.range T).sum
          (fun t : Nat =>
            if t ∈ freeTimes then (1 : ENNReal) else ENNReal.ofReal delta)
          <=
        (Finset.range T).sum
          (fun t : Nat =>
            (if t ∈ freeTimes then (1 : ENNReal) else 0) +
              ENNReal.ofReal delta) := by
            exact Finset.sum_le_sum
              (by
                intro t _ht
                by_cases hfree : t ∈ freeTimes
                · simp [hfree]
                · simp [hfree])
      _ =
        (Finset.range T).sum
          (fun t : Nat =>
            if t ∈ freeTimes then (1 : ENNReal) else 0) +
        (Finset.range T).sum (fun _t : Nat => ENNReal.ofReal delta) := by
            rw [Finset.sum_add_distrib]
      _ <=
        freeBudget + (Finset.range T).sum
          (fun _t : Nat => ENNReal.ofReal delta) := by
            exact add_le_add hfree_budget (le_refl _)
      _ = freeBudget + (T : ENNReal) * ENNReal.ofReal delta := by
            simp [Finset.sum_const, nsmul_eq_mul]
  exact hsplit.trans hsum

/--
The ENNReal indicator count of a finite set of free horizon times is bounded by
the total number of declared free times.
-/
theorem freeTimes_indicator_sum_le_card
    (T : Nat) (freeTimes : Finset Nat) :
    (Finset.range T).sum
        (fun t : Nat => if t ∈ freeTimes then (1 : ENNReal) else 0) <=
      (freeTimes.card : ENNReal) := by
  have hfilter_subset :
      (Finset.range T).filter (fun t : Nat => t ∈ freeTimes) ⊆ freeTimes := by
    intro t ht
    exact (Finset.mem_filter.mp ht).2
  calc
    (Finset.range T).sum
        (fun t : Nat => if t ∈ freeTimes then (1 : ENNReal) else 0)
        =
      ((Finset.range T).filter (fun t : Nat => t ∈ freeTimes)).sum
        (fun _t : Nat => (1 : ENNReal)) := by
        rw [Finset.sum_filter]
    _ = (((Finset.range T).filter (fun t : Nat => t ∈ freeTimes)).card : ENNReal) := by
        simp [Finset.sum_const, nsmul_eq_mul]
    _ <= (freeTimes.card : ENNReal) := by
        exact_mod_cast Finset.card_le_card hfilter_subset

/--
Along one concrete action trace, the number of selected times whose previous
pull count is still below threshold `B` is the minimum of the terminal pull
count and `B`.

This is the pathwise source of the usual UCB small-count budget: selected
occurrences with `pullCount < B` can happen at most `B` times, regardless of the
ambient horizon length.
-/
theorem selectedSmallPullCount_sum_eq_min_pullCount
    {Action : Type} [DecidableEq Action]
    (action : ActionTrace Action) (chosen : Action) (T B : Nat) :
    (Finset.range T).sum
        (fun t : Nat =>
          if action t = chosen ∧ pullCount action chosen t < B then
            (1 : Nat)
          else
            0) =
      Nat.min (pullCount action chosen T) B := by
  induction T with
  | zero =>
      simp
  | succ T ih =>
      by_cases hselected : action T = chosen
      · by_cases hsmall : pullCount action chosen T < B
        · have hold :
              Nat.min (pullCount action chosen T) B =
                pullCount action chosen T := by
            exact Nat.min_eq_left (Nat.le_of_lt hsmall)
          have hnew :
              Nat.min (pullCount action chosen (T + 1)) B =
                pullCount action chosen T + 1 := by
            rw [pullCount_succ_of_eq action chosen T hselected]
            exact Nat.min_eq_left (Nat.succ_le_of_lt hsmall)
          rw [Finset.sum_range_succ]
          rw [if_pos ⟨hselected, hsmall⟩]
          rw [ih, hold, hnew]
        · have hnot_small : ¬ pullCount action chosen T < B := hsmall
          have hold :
              Nat.min (pullCount action chosen T) B = B := by
            exact Nat.min_eq_right (Nat.le_of_not_gt hnot_small)
          have hnew :
              Nat.min (pullCount action chosen (T + 1)) B = B := by
            rw [pullCount_succ_of_eq action chosen T hselected]
            exact Nat.min_eq_right
              (Nat.le_trans (Nat.le_of_not_gt hnot_small) (Nat.le_succ _))
          have hnot :
              ¬ (action T = chosen ∧ pullCount action chosen T < B) := by
            intro h
            exact hnot_small h.2
          rw [Finset.sum_range_succ]
          rw [if_neg hnot]
          rw [ih, hold, hnew]
          simp
      · have hnot :
            ¬ (action T = chosen ∧ pullCount action chosen T < B) := by
          intro h
          exact hselected h.1
        have hnew :
            pullCount action chosen (T + 1) = pullCount action chosen T :=
          pullCount_succ_of_ne action chosen T hselected
        rw [Finset.sum_range_succ]
        rw [if_neg hnot]
        rw [ih, hnew]
        simp

/--
Pathwise UCB small-count budget in Nat form.
-/
theorem selectedSmallPullCount_sum_le_threshold
    {Action : Type} [DecidableEq Action]
    (action : ActionTrace Action) (chosen : Action) (T B : Nat) :
    (Finset.range T).sum
        (fun t : Nat =>
          if action t = chosen ∧ pullCount action chosen t < B then
            (1 : Nat)
          else
            0) <= B := by
  rw [selectedSmallPullCount_sum_eq_min_pullCount action chosen T B]
  exact Nat.min_le_right _ _

/--
ENNReal-facing pathwise UCB small-count budget.
-/
theorem selectedSmallPullCount_indicator_sum_le_threshold
    {Action : Type} [DecidableEq Action]
    (action : ActionTrace Action) (chosen : Action) (T B : Nat) :
    (Finset.range T).sum
        (fun t : Nat =>
          if action t = chosen ∧ pullCount action chosen t < B then
            (1 : ENNReal)
          else
            0) <=
      (B : ENNReal) := by
  have hnat :=
    selectedSmallPullCount_sum_le_threshold action chosen T B
  simpa using
    (show
      (((Finset.range T).sum
          (fun t : Nat =>
            if action t = chosen ∧ pullCount action chosen t < B then
              (1 : Nat)
            else
              0) : Nat) : ENNReal) <=
        (B : ENNReal) from by
          exact_mod_cast hnat)

/--
Probability-facing version of the pathwise selected-small budget.

No measurability assumption is needed for this upper bound: the lower integral
is dominated pointwise by the constant `B`, and the measure is a probability
measure.
-/
theorem lintegral_selectedSmallPullCount_indicator_sum_le_threshold
    {Omega Action : Type} [MeasurableSpace Omega] [DecidableEq Action]
    (mu : Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    (action : Omega -> ActionTrace Action) (chosen : Action) (T B : Nat) :
    MeasureTheory.lintegral mu
      (fun omega : Omega =>
        (Finset.range T).sum
          (fun t : Nat =>
            if action omega t = chosen ∧
                pullCount (action omega) chosen t < B then
              (1 : ENNReal)
            else
              0)) <=
      (B : ENNReal) := by
  calc
    MeasureTheory.lintegral mu
      (fun omega : Omega =>
        (Finset.range T).sum
          (fun t : Nat =>
            if action omega t = chosen ∧
                pullCount (action omega) chosen t < B then
              (1 : ENNReal)
            else
              0))
        <=
      MeasureTheory.lintegral mu (fun _omega : Omega => (B : ENNReal)) := by
        exact MeasureTheory.lintegral_mono
          (fun omega =>
            selectedSmallPullCount_indicator_sum_le_threshold
              (action omega) chosen T B)
    _ = (B : ENNReal) := by
        rw [MeasureTheory.lintegral_const]
        simp [MeasureTheory.IsProbabilityMeasure.measure_univ]

/--
The selected-time Nat indicator sum is exactly the recursive pull count.
-/
theorem selectedPullCount_sum_eq_pullCount
    {Action : Type} [DecidableEq Action]
    (action : ActionTrace Action) (chosen : Action) (T : Nat) :
    (Finset.range T).sum
        (fun t : Nat => if action t = chosen then (1 : Nat) else 0) =
      pullCount action chosen T := by
  induction T with
  | zero =>
      simp
  | succ T ih =>
      by_cases hselected : action T = chosen
      · rw [Finset.sum_range_succ]
        rw [if_pos hselected]
        rw [pullCount_succ_of_eq action chosen T hselected]
        rw [ih]
      · rw [Finset.sum_range_succ]
        rw [if_neg hselected]
        rw [pullCount_succ_of_ne action chosen T hselected]
        rw [ih]
        simp

/--
ENNReal-facing selected-time indicator identity for the recursive pull count.
-/
theorem selectedPullCount_indicator_sum_eq_natCast_pullCount
    {Action : Type} [DecidableEq Action]
    (action : ActionTrace Action) (chosen : Action) (T : Nat) :
    (Finset.range T).sum
        (fun t : Nat => if action t = chosen then (1 : ENNReal) else 0) =
      ((pullCount action chosen T : Nat) : ENNReal) := by
  have hnat := selectedPullCount_sum_eq_pullCount action chosen T
  simpa using
    (show
      (((Finset.range T).sum
          (fun t : Nat =>
            if action t = chosen then (1 : Nat) else 0) : Nat) : ENNReal) =
        ((pullCount action chosen T : Nat) : ENNReal) from by
          exact_mod_cast hnat)

/--
Every selected time is either a selected-small time or a selected-large-count
time, split by the threshold `B`.
-/
theorem selectedPullCount_indicator_sum_eq_selectedSmall_add_selectedLargePullCount
    {Action : Type} [DecidableEq Action]
    (action : ActionTrace Action) (chosen : Action) (T B : Nat) :
    (Finset.range T).sum
        (fun t : Nat => if action t = chosen then (1 : ENNReal) else 0) =
      (Finset.range T).sum
          (fun t : Nat =>
            if action t = chosen ∧ pullCount action chosen t < B then
              (1 : ENNReal)
            else
              0) +
        (Finset.range T).sum
          (fun t : Nat =>
            if action t = chosen ∧ B <= pullCount action chosen t then
              (1 : ENNReal)
            else
              0) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _ht
  by_cases hselected : action t = chosen
  · by_cases hsmall : pullCount action chosen t < B
    · have hnot_large :
          ¬ B <= pullCount action chosen t :=
        Nat.not_le_of_gt hsmall
      simp [hselected, hsmall, hnot_large]
    · have hlarge : B <= pullCount action chosen t :=
        Nat.le_of_not_gt hsmall
      have hnot_small :
          ¬ (action t = chosen ∧ pullCount action chosen t < B) := by
        intro h
        exact hsmall h.2
      simp [hselected, hsmall, hlarge]
  ·
    simp [hselected]

/--
Pointwise ENNReal UCB count budget after isolating selected-large-count times.

The selected-small part is charged by `B`; only selected times whose prior
pull count is at least `B` remain for a future large-gap tail bound.
-/
theorem natCast_pullCount_le_threshold_add_selectedLargePullCount_indicator_sum
    {Action : Type} [DecidableEq Action]
    (action : ActionTrace Action) (chosen : Action) (T B : Nat) :
    ((pullCount action chosen T : Nat) : ENNReal) <=
      (B : ENNReal) +
        (Finset.range T).sum
          (fun t : Nat =>
            if action t = chosen ∧ B <= pullCount action chosen t then
              (1 : ENNReal)
            else
              0) := by
  calc
    ((pullCount action chosen T : Nat) : ENNReal) =
        (Finset.range T).sum
          (fun t : Nat =>
            if action t = chosen then (1 : ENNReal) else 0) := by
          exact
            (selectedPullCount_indicator_sum_eq_natCast_pullCount
              action chosen T).symm
    _ =
        (Finset.range T).sum
          (fun t : Nat =>
            if action t = chosen ∧ pullCount action chosen t < B then
              (1 : ENNReal)
            else
              0) +
        (Finset.range T).sum
          (fun t : Nat =>
            if action t = chosen ∧ B <= pullCount action chosen t then
              (1 : ENNReal)
            else
              0) := by
          exact
            selectedPullCount_indicator_sum_eq_selectedSmall_add_selectedLargePullCount
              action chosen T B
    _ <=
        (B : ENNReal) +
        (Finset.range T).sum
          (fun t : Nat =>
            if action t = chosen ∧ B <= pullCount action chosen t then
              (1 : ENNReal)
            else
              0) := by
          exact add_le_add
            (selectedSmallPullCount_indicator_sum_le_threshold
              action chosen T B) (le_refl _)

/--
Measurability of a selected-large-count event for a fixed time.
-/
theorem measurableSet_selectedLargePullCount
    {Omega Action : Type}
    [MeasurableSpace Omega] [MeasurableSpace Action]
    [MeasurableSingletonClass Action]
    [MeasurableSpace Nat] [MeasurableAdd₂ Nat] [OpensMeasurableSpace Nat]
    [DecidableEq Action]
    (action : Omega -> ActionTrace Action)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (chosen : Action) (t B : Nat) :
    MeasurableSet
      {omega : Omega |
        action omega t = chosen ∧ B <= pullCount (action omega) chosen t} := by
  exact
    (measurableSet_actionTrace_eval_eq action haction chosen t).inter
      (measurableSet_le measurable_const
        (measurable_pullCount action haction chosen t))

/--
The lower integral of selected-large-count indicators is the corresponding
finite sum of event measures.
-/
theorem lintegral_selectedLargePullCount_indicator_sum_eq_sum_measure
    {Omega Action : Type}
    [MeasurableSpace Omega] [MeasurableSpace Action]
    [MeasurableSingletonClass Action]
    [MeasurableSpace Nat] [MeasurableAdd₂ Nat] [OpensMeasurableSpace Nat]
    [DecidableEq Action]
    (mu : Measure Omega)
    (action : Omega -> ActionTrace Action)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (chosen : Action) (T B : Nat) :
    MeasureTheory.lintegral mu
      (fun omega : Omega =>
        (Finset.range T).sum
          (fun t : Nat =>
            if action omega t = chosen ∧
                B <= pullCount (action omega) chosen t then
              (1 : ENNReal)
            else
              0))
      =
    (Finset.range T).sum
      (fun t : Nat =>
        mu {omega : Omega |
          action omega t = chosen ∧
            B <= pullCount (action omega) chosen t}) := by
  have hfun :
      (fun omega : Omega =>
        (Finset.range T).sum
          (fun t : Nat =>
            if action omega t = chosen ∧
                B <= pullCount (action omega) chosen t then
              (1 : ENNReal)
            else
              0))
        =
      (fun omega : Omega =>
        (Finset.range T).sum
          (fun t : Nat =>
            (({omega' : Omega |
              action omega' t = chosen ∧
                B <= pullCount (action omega') chosen t} : Set Omega).indicator
              (1 : Omega -> ENNReal)) omega)) := by
    funext omega
    apply Finset.sum_congr rfl
    intro t _ht
    by_cases h :
        action omega t = chosen ∧ B <= pullCount (action omega) chosen t
    · simp [Set.indicator_of_mem, h]
    · simp [Set.indicator_of_notMem, h]
  rw [hfun]
  have hmeas :
      forall t : Nat, t ∈ Finset.range T ->
        Measurable
          (fun omega : Omega =>
            (({omega' : Omega |
              action omega' t = chosen ∧
                B <= pullCount (action omega') chosen t} : Set Omega).indicator
              (1 : Omega -> ENNReal)) omega) := by
    intro t _ht
    exact Measurable.indicator measurable_const
      (measurableSet_selectedLargePullCount action haction chosen t B)
  calc
    MeasureTheory.lintegral mu
      (fun omega : Omega =>
        (Finset.range T).sum
          (fun t : Nat =>
            (({omega' : Omega |
              action omega' t = chosen ∧
                B <= pullCount (action omega') chosen t} : Set Omega).indicator
              (1 : Omega -> ENNReal)) omega))
        =
      (Finset.range T).sum
        (fun t : Nat =>
          MeasureTheory.lintegral mu
            (fun omega : Omega =>
              (({omega' : Omega |
                action omega' t = chosen ∧
                  B <= pullCount (action omega') chosen t} : Set Omega).indicator
                (1 : Omega -> ENNReal)) omega)) := by
          simpa [Finset.sum_apply] using
            (@MeasureTheory.lintegral_finset_sum
              Omega Nat _ mu (Finset.range T)
              (f := fun t omega =>
                (({omega' : Omega |
                  action omega' t = chosen ∧
                    B <= pullCount (action omega') chosen t} : Set Omega).indicator
                  (1 : Omega -> ENNReal)) omega)
              hmeas)
    _ =
      (Finset.range T).sum
        (fun t : Nat =>
          mu {omega : Omega |
            action omega t = chosen ∧
              B <= pullCount (action omega) chosen t}) := by
        apply Finset.sum_congr rfl
        intro t _ht
        simpa using
          (@MeasureTheory.lintegral_indicator_one
            Omega _ mu
            {omega : Omega |
              action omega t = chosen ∧
                B <= pullCount (action omega) chosen t}
            (measurableSet_selectedLargePullCount action haction chosen t B))

/--
Single-time selected-large-count event budget for concrete score-argmax UCB.

If the event is nonempty but the deterministic large-gap inequality fails, the
pointwise large-count-to-large-gap contract gives a contradiction. Otherwise it
reduces to the existing selected-event `delta` bound.
-/
theorem measure_confidenceScoreArgmax_selectedLargePullCountEvent_le_subGaussian_textbookDeltaRadius_delta
    {Omega : Type} [MeasurableSpace Omega]
    {K : Nat} (hK : 0 < K)
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (trueMean : Fin K -> Real)
    (empiricalMean : Omega -> Nat -> Fin K -> Real)
    (proxy : Nat -> Fin K -> NNReal) (T : Nat) (delta : Real)
    (t B : Nat) (best chosen : Fin K)
    (hT : 0 < T) (hdelta : 0 < delta) (ht : t < T)
    (hlarge_count_gap : forall omega : Omega,
      confidenceScoreArgmaxAction hK empiricalMean
          (subGaussianTextbookDeltaRadius proxy T delta) omega t = chosen ->
        B <= pullCount
          ((confidenceScoreArgmaxAction hK empiricalMean
            (subGaussianTextbookDeltaRadius proxy T delta)) omega)
          chosen t ->
        2 * subGaussianTextbookDeltaRadius proxy T delta t chosen <
          meanGap trueMean best chosen)
    (hproxy : forall t arm, t < T ->
      0 < ((proxy t arm : NNReal) : Real))
    (hsubG : forall t arm, t < T ->
      ProbabilityTheory.HasSubgaussianMGF
        (fun omega : Omega => empiricalMean omega t arm - trueMean arm)
        (proxy t arm) mu) :
    mu {omega : Omega |
      confidenceScoreArgmaxAction hK empiricalMean
          (subGaussianTextbookDeltaRadius proxy T delta) omega t = chosen ∧
        B <= pullCount
          ((confidenceScoreArgmaxAction hK empiricalMean
            (subGaussianTextbookDeltaRadius proxy T delta)) omega)
          chosen t} <=
      ENNReal.ofReal delta := by
  by_cases hgap_large :
      2 * subGaussianTextbookDeltaRadius proxy T delta t chosen <
        meanGap trueMean best chosen
  · have hsubset :
      Set.Subset
        {omega : Omega |
          confidenceScoreArgmaxAction hK empiricalMean
              (subGaussianTextbookDeltaRadius proxy T delta) omega t = chosen ∧
            B <= pullCount
              ((confidenceScoreArgmaxAction hK empiricalMean
                (subGaussianTextbookDeltaRadius proxy T delta)) omega)
              chosen t}
        {omega : Omega |
          confidenceScoreArgmaxAction hK empiricalMean
            (subGaussianTextbookDeltaRadius proxy T delta) omega t = chosen} := by
        intro omega h
        exact h.1
    exact (measure_mono hsubset).trans
      (measure_confidenceScoreArgmax_selectedLargeGapEvent_le_subGaussian_textbookDeltaRadius_delta
        hK mu trueMean empiricalMean proxy T delta t best chosen
        hT hdelta ht hgap_large hproxy hsubG)
  · have hempty :
      {omega : Omega |
        confidenceScoreArgmaxAction hK empiricalMean
            (subGaussianTextbookDeltaRadius proxy T delta) omega t = chosen ∧
          B <= pullCount
            ((confidenceScoreArgmaxAction hK empiricalMean
              (subGaussianTextbookDeltaRadius proxy T delta)) omega)
            chosen t} = ∅ := by
      ext omega
      constructor
      · intro h
        exact False.elim (hgap_large (hlarge_count_gap omega h.1 h.2))
      · intro h
        simp at h
    simp [hempty]

/--
Finite-horizon sum budget for selected-large-count concrete score-argmax events.
-/
theorem sum_measure_confidenceScoreArgmax_selectedLargePullCountEvent_le_horizon_mul_delta
    {Omega : Type} [MeasurableSpace Omega]
    {K : Nat} (hK : 0 < K)
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (trueMean : Fin K -> Real)
    (empiricalMean : Omega -> Nat -> Fin K -> Real)
    (proxy : Nat -> Fin K -> NNReal) (T : Nat) (delta : Real)
    (B : Nat) (best chosen : Fin K)
    (hT : 0 < T) (hdelta : 0 < delta)
    (hlarge_count_gap : forall omega t, t < T ->
      confidenceScoreArgmaxAction hK empiricalMean
          (subGaussianTextbookDeltaRadius proxy T delta) omega t = chosen ->
        B <= pullCount
          ((confidenceScoreArgmaxAction hK empiricalMean
            (subGaussianTextbookDeltaRadius proxy T delta)) omega)
          chosen t ->
        2 * subGaussianTextbookDeltaRadius proxy T delta t chosen <
          meanGap trueMean best chosen)
    (hproxy : forall t arm, t < T ->
      0 < ((proxy t arm : NNReal) : Real))
    (hsubG : forall t arm, t < T ->
      ProbabilityTheory.HasSubgaussianMGF
        (fun omega : Omega => empiricalMean omega t arm - trueMean arm)
        (proxy t arm) mu) :
    (Finset.range T).sum
        (fun t : Nat =>
          mu {omega : Omega |
            confidenceScoreArgmaxAction hK empiricalMean
                (subGaussianTextbookDeltaRadius proxy T delta) omega t =
              chosen ∧
            B <= pullCount
              ((confidenceScoreArgmaxAction hK empiricalMean
                (subGaussianTextbookDeltaRadius proxy T delta)) omega)
              chosen t}) <=
      (T : ENNReal) * ENNReal.ofReal delta := by
  calc
    (Finset.range T).sum
        (fun t : Nat =>
          mu {omega : Omega |
            confidenceScoreArgmaxAction hK empiricalMean
                (subGaussianTextbookDeltaRadius proxy T delta) omega t =
              chosen ∧
            B <= pullCount
              ((confidenceScoreArgmaxAction hK empiricalMean
                (subGaussianTextbookDeltaRadius proxy T delta)) omega)
              chosen t})
        <=
      (Finset.range T).sum (fun _t : Nat => ENNReal.ofReal delta) := by
        exact Finset.sum_le_sum
          (by
            intro t ht_mem
            have ht : t < T := by
              simpa using ht_mem
            exact
              measure_confidenceScoreArgmax_selectedLargePullCountEvent_le_subGaussian_textbookDeltaRadius_delta
                hK mu trueMean empiricalMean proxy T delta t B best chosen
                hT hdelta ht
                (by
                  intro omega hselected hcount
                  exact hlarge_count_gap omega t ht hselected hcount)
                hproxy hsubG)
    _ = (T : ENNReal) * ENNReal.ofReal delta := by
        simp [Finset.sum_const, nsmul_eq_mul]

/--
Lower-integral finite-sum budget for selected-large-count concrete score-argmax
events.
-/
theorem lintegral_confidenceScoreArgmax_selectedLargePullCount_indicator_sum_le_horizon_mul_delta
    {Omega : Type} [MeasurableSpace Omega]
    {K : Nat} (hK : 0 < K)
    [MeasurableSpace (Fin K)] [MeasurableSingletonClass (Fin K)]
    [MeasurableSpace Nat] [MeasurableAdd₂ Nat] [OpensMeasurableSpace Nat]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (trueMean : Fin K -> Real)
    (empiricalMean : Omega -> Nat -> Fin K -> Real)
    (proxy : Nat -> Fin K -> NNReal) (T : Nat) (delta : Real)
    (B : Nat) (best chosen : Fin K)
    (hT : 0 < T) (hdelta : 0 < delta)
    (haction : forall t : Nat,
      Measurable
        (fun omega : Omega =>
          confidenceScoreArgmaxAction hK empiricalMean
            (subGaussianTextbookDeltaRadius proxy T delta) omega t))
    (hlarge_count_gap : forall omega t, t < T ->
      confidenceScoreArgmaxAction hK empiricalMean
          (subGaussianTextbookDeltaRadius proxy T delta) omega t = chosen ->
        B <= pullCount
          ((confidenceScoreArgmaxAction hK empiricalMean
            (subGaussianTextbookDeltaRadius proxy T delta)) omega)
          chosen t ->
        2 * subGaussianTextbookDeltaRadius proxy T delta t chosen <
          meanGap trueMean best chosen)
    (hproxy : forall t arm, t < T ->
      0 < ((proxy t arm : NNReal) : Real))
    (hsubG : forall t arm, t < T ->
      ProbabilityTheory.HasSubgaussianMGF
        (fun omega : Omega => empiricalMean omega t arm - trueMean arm)
        (proxy t arm) mu) :
    MeasureTheory.lintegral mu
      (fun omega : Omega =>
        (Finset.range T).sum
          (fun t : Nat =>
            if confidenceScoreArgmaxAction hK empiricalMean
                (subGaussianTextbookDeltaRadius proxy T delta) omega t =
                  chosen ∧
                B <= pullCount
                  ((confidenceScoreArgmaxAction hK empiricalMean
                    (subGaussianTextbookDeltaRadius proxy T delta)) omega)
                  chosen t then
              (1 : ENNReal)
            else
              0)) <=
      (T : ENNReal) * ENNReal.ofReal delta := by
  rw [lintegral_selectedLargePullCount_indicator_sum_eq_sum_measure
    (mu := mu)
    (action :=
      confidenceScoreArgmaxAction hK empiricalMean
        (subGaussianTextbookDeltaRadius proxy T delta))
    (haction := haction)
    (chosen := chosen)
    (T := T)
    (B := B)]
  exact
    sum_measure_confidenceScoreArgmax_selectedLargePullCountEvent_le_horizon_mul_delta
      hK mu trueMean empiricalMean proxy T delta B best chosen
      hT hdelta hlarge_count_gap hproxy hsubG

/--
Integrated UCB pull-count budget from a selected-large-count large-gap source.
-/
theorem lintegral_confidenceScoreArgmax_pullCount_le_threshold_add_horizon_delta_of_selectedLargePullCount
    {Omega : Type} [MeasurableSpace Omega]
    {K : Nat} (hK : 0 < K)
    [MeasurableSpace (Fin K)] [MeasurableSingletonClass (Fin K)]
    [MeasurableSpace Nat] [MeasurableAdd₂ Nat] [OpensMeasurableSpace Nat]
    (mu : Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    (trueMean : Fin K -> Real)
    (empiricalMean : Omega -> Nat -> Fin K -> Real)
    (proxy : Nat -> Fin K -> NNReal) (T : Nat) (delta : Real)
    (B : Nat) (best chosen : Fin K)
    (hT : 0 < T) (hdelta : 0 < delta)
    (haction : forall t : Nat,
      Measurable
        (fun omega : Omega =>
          confidenceScoreArgmaxAction hK empiricalMean
            (subGaussianTextbookDeltaRadius proxy T delta) omega t))
    (hlarge_count_gap : forall omega t, t < T ->
      confidenceScoreArgmaxAction hK empiricalMean
          (subGaussianTextbookDeltaRadius proxy T delta) omega t = chosen ->
        B <= pullCount
          ((confidenceScoreArgmaxAction hK empiricalMean
            (subGaussianTextbookDeltaRadius proxy T delta)) omega)
          chosen t ->
        2 * subGaussianTextbookDeltaRadius proxy T delta t chosen <
          meanGap trueMean best chosen)
    (hproxy : forall t arm, t < T ->
      0 < ((proxy t arm : NNReal) : Real))
    (hsubG : forall t arm, t < T ->
      ProbabilityTheory.HasSubgaussianMGF
        (fun omega : Omega => empiricalMean omega t arm - trueMean arm)
        (proxy t arm) mu) :
    MeasureTheory.lintegral mu
      (fun omega : Omega =>
        ((pullCount
          ((confidenceScoreArgmaxAction hK empiricalMean
            (subGaussianTextbookDeltaRadius proxy T delta)) omega)
          chosen T : Nat) : ENNReal)) <=
      (B : ENNReal) + (T : ENNReal) * ENNReal.ofReal delta := by
  let action : Omega -> ActionTrace (Fin K) :=
    confidenceScoreArgmaxAction hK empiricalMean
      (subGaussianTextbookDeltaRadius proxy T delta)
  let largeCount : Omega -> ENNReal := fun omega =>
    (Finset.range T).sum
      (fun t : Nat =>
        if action omega t = chosen ∧
            B <= pullCount (action omega) chosen t then
          (1 : ENNReal)
        else
          0)
  have hpoint : forall omega : Omega,
      ((pullCount (action omega) chosen T : Nat) : ENNReal) <=
        (B : ENNReal) + largeCount omega := by
    intro omega
    exact
      natCast_pullCount_le_threshold_add_selectedLargePullCount_indicator_sum
        (action omega) chosen T B
  have hlarge_lintegral :
      MeasureTheory.lintegral mu largeCount <=
        (T : ENNReal) * ENNReal.ofReal delta := by
    simpa [action, largeCount] using
      lintegral_confidenceScoreArgmax_selectedLargePullCount_indicator_sum_le_horizon_mul_delta
        hK mu trueMean empiricalMean proxy T delta B best chosen
        hT hdelta haction hlarge_count_gap hproxy hsubG
  calc
    MeasureTheory.lintegral mu
      (fun omega : Omega =>
        ((pullCount (action omega) chosen T : Nat) : ENNReal))
        <=
      MeasureTheory.lintegral mu
        (fun omega : Omega => (B : ENNReal) + largeCount omega) := by
          exact MeasureTheory.lintegral_mono hpoint
    _ =
      MeasureTheory.lintegral mu (fun _omega : Omega => (B : ENNReal)) +
      MeasureTheory.lintegral mu largeCount := by
        rw [MeasureTheory.lintegral_add_left measurable_const]
    _ =
      (B : ENNReal) + MeasureTheory.lintegral mu largeCount := by
        rw [MeasureTheory.lintegral_const]
        simp [MeasureTheory.IsProbabilityMeasure.measure_univ]
    _ <=
      (B : ENNReal) + (T : ENNReal) * ENNReal.ofReal delta := by
        exact add_le_add (le_refl _) hlarge_lintegral

/--
Concrete cardinality-budget version of the threshold/suffix pull-count split.

This discharges the abstract `freeBudget` input with `freeTimes.card`. A later
radius-threshold leaf can instantiate `freeTimes` and prove its cardinality is
the usual logarithmic/gap-dependent budget.
-/
theorem lintegral_confidenceScoreArgmax_pullCount_le_freeCard_add_horizon_delta
    {Omega : Type} [MeasurableSpace Omega]
    {K : Nat} (hK : 0 < K)
    [MeasurableSpace (Fin K)] [MeasurableSingletonClass (Fin K)]
    (mu : Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    (trueMean : Fin K -> Real)
    (empiricalMean : Omega -> Nat -> Fin K -> Real)
    (proxy : Nat -> Fin K -> NNReal) (T : Nat) (delta : Real)
    (freeTimes chargedTimes : Finset Nat) (best chosen : Fin K)
    (hT : 0 < T) (hdelta : 0 < delta)
    (hcharged_of_not_free : forall t, t < T -> t ∉ freeTimes -> t ∈ chargedTimes)
    (hgap_large : forall t, t ∈ chargedTimes ->
      2 * subGaussianTextbookDeltaRadius proxy T delta t chosen <
        meanGap trueMean best chosen)
    (haction : forall t : Nat,
      Measurable
        (fun omega : Omega =>
          confidenceScoreArgmaxAction hK empiricalMean
            (subGaussianTextbookDeltaRadius proxy T delta) omega t))
    (hproxy : forall t arm, t < T ->
      0 < ((proxy t arm : NNReal) : Real))
    (hsubG : forall t arm, t < T ->
      ProbabilityTheory.HasSubgaussianMGF
        (fun omega : Omega => empiricalMean omega t arm - trueMean arm)
        (proxy t arm) mu) :
    MeasureTheory.lintegral mu
      (fun omega : Omega =>
        ((pullCount
          ((confidenceScoreArgmaxAction hK empiricalMean
            (subGaussianTextbookDeltaRadius proxy T delta)) omega)
          chosen T : Nat) : ENNReal)) <=
      (freeTimes.card : ENNReal) + (T : ENNReal) * ENNReal.ofReal delta := by
  exact
    lintegral_confidenceScoreArgmax_pullCount_le_freeBudget_add_horizon_delta
      hK mu trueMean empiricalMean proxy T delta freeTimes chargedTimes
      (freeTimes.card : ENNReal) best chosen hT hdelta
      (freeTimes_indicator_sum_le_card T freeTimes)
      hcharged_of_not_free hgap_large haction hproxy hsubG

/--
Horizon times where the textbook delta radius is already small enough for the
selected arm to satisfy the large-gap condition.
-/
noncomputable def subGaussianTextbookDeltaRadiusChargedTimes
    {K : Nat} (trueMean : Fin K -> Real)
    (proxy : Nat -> Fin K -> NNReal) (T : Nat) (delta : Real)
    (best chosen : Fin K) : Finset Nat :=
  (Finset.range T).filter
    (fun t : Nat =>
      2 * subGaussianTextbookDeltaRadius proxy T delta t chosen <
        meanGap trueMean best chosen)

/--
Horizon times not yet discharged by the textbook large-gap radius condition.

The next cardinality leaf can bound this concrete set by a closed-form
gap/log/sample threshold.
-/
noncomputable def subGaussianTextbookDeltaRadiusFreeTimes
    {K : Nat} (trueMean : Fin K -> Real)
    (proxy : Nat -> Fin K -> NNReal) (T : Nat) (delta : Real)
    (best chosen : Fin K) : Finset Nat :=
  (Finset.range T).filter
    (fun t : Nat =>
      ¬ 2 * subGaussianTextbookDeltaRadius proxy T delta t chosen <
        meanGap trueMean best chosen)

@[simp] theorem mem_subGaussianTextbookDeltaRadiusChargedTimes_iff
    {K : Nat} (trueMean : Fin K -> Real)
    (proxy : Nat -> Fin K -> NNReal) (T : Nat) (delta : Real)
    (best chosen : Fin K) (t : Nat) :
    t ∈ subGaussianTextbookDeltaRadiusChargedTimes
        trueMean proxy T delta best chosen ↔
      t < T ∧
        2 * subGaussianTextbookDeltaRadius proxy T delta t chosen <
          meanGap trueMean best chosen := by
  simp [subGaussianTextbookDeltaRadiusChargedTimes]

@[simp] theorem mem_subGaussianTextbookDeltaRadiusFreeTimes_iff
    {K : Nat} (trueMean : Fin K -> Real)
    (proxy : Nat -> Fin K -> NNReal) (T : Nat) (delta : Real)
    (best chosen : Fin K) (t : Nat) :
    t ∈ subGaussianTextbookDeltaRadiusFreeTimes
        trueMean proxy T delta best chosen ↔
      t < T ∧
        ¬ 2 * subGaussianTextbookDeltaRadius proxy T delta t chosen <
          meanGap trueMean best chosen := by
  simp [subGaussianTextbookDeltaRadiusFreeTimes]

theorem subGaussianTextbookDeltaRadiusChargedTimes_of_not_free
    {K : Nat} (trueMean : Fin K -> Real)
    (proxy : Nat -> Fin K -> NNReal) (T : Nat) (delta : Real)
    (best chosen : Fin K) (t : Nat) :
    t < T ->
    t ∉ subGaussianTextbookDeltaRadiusFreeTimes
        trueMean proxy T delta best chosen ->
    t ∈ subGaussianTextbookDeltaRadiusChargedTimes
        trueMean proxy T delta best chosen := by
  intro ht hnot_free
  rw [mem_subGaussianTextbookDeltaRadiusChargedTimes_iff]
  refine ⟨ht, ?_⟩
  by_contra hnot_gap
  exact hnot_free
    ((mem_subGaussianTextbookDeltaRadiusFreeTimes_iff
      trueMean proxy T delta best chosen t).2 ⟨ht, hnot_gap⟩)

theorem subGaussianTextbookDeltaRadiusChargedTimes_gap_large
    {K : Nat} (trueMean : Fin K -> Real)
    (proxy : Nat -> Fin K -> NNReal) (T : Nat) (delta : Real)
    (best chosen : Fin K) (t : Nat) :
    t ∈ subGaussianTextbookDeltaRadiusChargedTimes
        trueMean proxy T delta best chosen ->
      2 * subGaussianTextbookDeltaRadius proxy T delta t chosen <
        meanGap trueMean best chosen := by
  intro ht
  exact
    ((mem_subGaussianTextbookDeltaRadiusChargedTimes_iff
      trueMean proxy T delta best chosen t).1 ht).2

/--
Concrete radius-threshold split for the textbook delta UCB pull-count budget.

This instantiates the abstract `freeTimes`/`chargedTimes` split with the
large-gap predicate induced by `subGaussianTextbookDeltaRadius`. It leaves the
closed-form cardinality bound for the concrete free-time set to the next leaf.
-/
theorem lintegral_confidenceScoreArgmax_pullCount_le_textbookDeltaRadiusFreeCard_add_horizon_delta
    {Omega : Type} [MeasurableSpace Omega]
    {K : Nat} (hK : 0 < K)
    [MeasurableSpace (Fin K)] [MeasurableSingletonClass (Fin K)]
    (mu : Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    (trueMean : Fin K -> Real)
    (empiricalMean : Omega -> Nat -> Fin K -> Real)
    (proxy : Nat -> Fin K -> NNReal) (T : Nat) (delta : Real)
    (best chosen : Fin K)
    (hT : 0 < T) (hdelta : 0 < delta)
    (haction : forall t : Nat,
      Measurable
        (fun omega : Omega =>
          confidenceScoreArgmaxAction hK empiricalMean
            (subGaussianTextbookDeltaRadius proxy T delta) omega t))
    (hproxy : forall t arm, t < T ->
      0 < ((proxy t arm : NNReal) : Real))
    (hsubG : forall t arm, t < T ->
      ProbabilityTheory.HasSubgaussianMGF
        (fun omega : Omega => empiricalMean omega t arm - trueMean arm)
        (proxy t arm) mu) :
    MeasureTheory.lintegral mu
      (fun omega : Omega =>
        ((pullCount
          ((confidenceScoreArgmaxAction hK empiricalMean
            (subGaussianTextbookDeltaRadius proxy T delta)) omega)
          chosen T : Nat) : ENNReal)) <=
      ((subGaussianTextbookDeltaRadiusFreeTimes
        trueMean proxy T delta best chosen).card : ENNReal) +
        (T : ENNReal) * ENNReal.ofReal delta := by
  exact
    lintegral_confidenceScoreArgmax_pullCount_le_freeCard_add_horizon_delta
      hK mu trueMean empiricalMean proxy T delta
      (subGaussianTextbookDeltaRadiusFreeTimes
        trueMean proxy T delta best chosen)
      (subGaussianTextbookDeltaRadiusChargedTimes
        trueMean proxy T delta best chosen)
      best chosen hT hdelta
      (by
        intro t ht hnot_free
        exact
          subGaussianTextbookDeltaRadiusChargedTimes_of_not_free
            trueMean proxy T delta best chosen t ht hnot_free)
      (by
        intro t ht
        exact
          subGaussianTextbookDeltaRadiusChargedTimes_gap_large
            trueMean proxy T delta best chosen t ht)
      haction hproxy hsubG

/--
If every horizon time at or beyond threshold `B` satisfies the textbook
large-gap radius condition, then the concrete free-time set has cardinality at
most `B`.
-/
theorem subGaussianTextbookDeltaRadiusFreeTimes_card_le_threshold
    {K : Nat} (trueMean : Fin K -> Real)
    (proxy : Nat -> Fin K -> NNReal) (T : Nat) (delta : Real)
    (best chosen : Fin K) (B : Nat)
    (hlarge_after : forall t, t < T -> B <= t ->
      2 * subGaussianTextbookDeltaRadius proxy T delta t chosen <
        meanGap trueMean best chosen) :
    (subGaussianTextbookDeltaRadiusFreeTimes
      trueMean proxy T delta best chosen).card <= B := by
  have hsubset :
      subGaussianTextbookDeltaRadiusFreeTimes
        trueMean proxy T delta best chosen ⊆ Finset.range B := by
    intro t ht_free_mem
    rw [Finset.mem_range]
    by_contra hnot_lt
    have hB_le_t : B <= t := Nat.le_of_not_gt hnot_lt
    have ht_free :=
      (mem_subGaussianTextbookDeltaRadiusFreeTimes_iff
        trueMean proxy T delta best chosen t).1 ht_free_mem
    exact ht_free.2 (hlarge_after t ht_free.1 hB_le_t)
  calc
    (subGaussianTextbookDeltaRadiusFreeTimes
      trueMean proxy T delta best chosen).card <= (Finset.range B).card := by
        exact Finset.card_le_card hsubset
    _ = B := by
        simp

theorem subGaussianTextbookDeltaRadiusFreeTimes_card_le_threshold_ennreal
    {K : Nat} (trueMean : Fin K -> Real)
    (proxy : Nat -> Fin K -> NNReal) (T : Nat) (delta : Real)
    (best chosen : Fin K) (B : Nat)
    (hlarge_after : forall t, t < T -> B <= t ->
      2 * subGaussianTextbookDeltaRadius proxy T delta t chosen <
        meanGap trueMean best chosen) :
    ((subGaussianTextbookDeltaRadiusFreeTimes
      trueMean proxy T delta best chosen).card : ENNReal) <=
      (B : ENNReal) := by
  exact_mod_cast
    subGaussianTextbookDeltaRadiusFreeTimes_card_le_threshold
      trueMean proxy T delta best chosen B hlarge_after

/--
Threshold-budget version of the concrete textbook-radius UCB pull-count split.

The only new deterministic input is that all times `t >= B` in the horizon
satisfy the large-gap radius condition. A later leaf can instantiate `B` with a
closed-form logarithmic/gap-dependent expression.
-/
theorem lintegral_confidenceScoreArgmax_pullCount_le_textbookDeltaRadiusThreshold_add_horizon_delta
    {Omega : Type} [MeasurableSpace Omega]
    {K : Nat} (hK : 0 < K)
    [MeasurableSpace (Fin K)] [MeasurableSingletonClass (Fin K)]
    (mu : Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    (trueMean : Fin K -> Real)
    (empiricalMean : Omega -> Nat -> Fin K -> Real)
    (proxy : Nat -> Fin K -> NNReal) (T : Nat) (delta : Real)
    (best chosen : Fin K) (B : Nat)
    (hT : 0 < T) (hdelta : 0 < delta)
    (hlarge_after : forall t, t < T -> B <= t ->
      2 * subGaussianTextbookDeltaRadius proxy T delta t chosen <
        meanGap trueMean best chosen)
    (haction : forall t : Nat,
      Measurable
        (fun omega : Omega =>
          confidenceScoreArgmaxAction hK empiricalMean
            (subGaussianTextbookDeltaRadius proxy T delta) omega t))
    (hproxy : forall t arm, t < T ->
      0 < ((proxy t arm : NNReal) : Real))
    (hsubG : forall t arm, t < T ->
      ProbabilityTheory.HasSubgaussianMGF
        (fun omega : Omega => empiricalMean omega t arm - trueMean arm)
        (proxy t arm) mu) :
    MeasureTheory.lintegral mu
      (fun omega : Omega =>
        ((pullCount
          ((confidenceScoreArgmaxAction hK empiricalMean
            (subGaussianTextbookDeltaRadius proxy T delta)) omega)
          chosen T : Nat) : ENNReal)) <=
      (B : ENNReal) + (T : ENNReal) * ENNReal.ofReal delta := by
  have hbase :=
    lintegral_confidenceScoreArgmax_pullCount_le_textbookDeltaRadiusFreeCard_add_horizon_delta
      hK mu trueMean empiricalMean proxy T delta best chosen
      hT hdelta haction hproxy hsubG
  have hcard :
      ((subGaussianTextbookDeltaRadiusFreeTimes
        trueMean proxy T delta best chosen).card : ENNReal) <=
        (B : ENNReal) :=
    subGaussianTextbookDeltaRadiusFreeTimes_card_le_threshold_ennreal
      trueMean proxy T delta best chosen B hlarge_after
  exact hbase.trans (add_le_add hcard (le_refl _))

/--
Half-gap radius condition in the textbook form implies the large-gap condition
consumed by the UCB selected-event and pull-count budget wrappers.
-/
theorem subGaussianTextbookDeltaRadius_large_gap_of_lt_half_meanGap
    {K : Nat} (trueMean : Fin K -> Real)
    (proxy : Nat -> Fin K -> NNReal) (T : Nat) (delta : Real)
    (best chosen : Fin K) (t : Nat)
    (hhalf :
      subGaussianTextbookDeltaRadius proxy T delta t chosen <
        meanGap trueMean best chosen / 2) :
    2 * subGaussianTextbookDeltaRadius proxy T delta t chosen <
      meanGap trueMean best chosen := by
  linarith

/--
Half-gap threshold version of the concrete textbook-radius UCB pull-count
budget.

This is the surface normally targeted by the remaining logarithmic/gap algebra:
prove that after threshold `B`, the textbook radius is below half the chosen
arm's gap.
-/
theorem lintegral_confidenceScoreArgmax_pullCount_le_textbookDeltaRadiusHalfGapThreshold_add_horizon_delta
    {Omega : Type} [MeasurableSpace Omega]
    {K : Nat} (hK : 0 < K)
    [MeasurableSpace (Fin K)] [MeasurableSingletonClass (Fin K)]
    (mu : Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    (trueMean : Fin K -> Real)
    (empiricalMean : Omega -> Nat -> Fin K -> Real)
    (proxy : Nat -> Fin K -> NNReal) (T : Nat) (delta : Real)
    (best chosen : Fin K) (B : Nat)
    (hT : 0 < T) (hdelta : 0 < delta)
    (hhalf_after : forall t, t < T -> B <= t ->
      subGaussianTextbookDeltaRadius proxy T delta t chosen <
        meanGap trueMean best chosen / 2)
    (haction : forall t : Nat,
      Measurable
        (fun omega : Omega =>
          confidenceScoreArgmaxAction hK empiricalMean
            (subGaussianTextbookDeltaRadius proxy T delta) omega t))
    (hproxy : forall t arm, t < T ->
      0 < ((proxy t arm : NNReal) : Real))
    (hsubG : forall t arm, t < T ->
      ProbabilityTheory.HasSubgaussianMGF
        (fun omega : Omega => empiricalMean omega t arm - trueMean arm)
        (proxy t arm) mu) :
    MeasureTheory.lintegral mu
      (fun omega : Omega =>
        ((pullCount
          ((confidenceScoreArgmaxAction hK empiricalMean
            (subGaussianTextbookDeltaRadius proxy T delta)) omega)
          chosen T : Nat) : ENNReal)) <=
      (B : ENNReal) + (T : ENNReal) * ENNReal.ofReal delta := by
  exact
    lintegral_confidenceScoreArgmax_pullCount_le_textbookDeltaRadiusThreshold_add_horizon_delta
      hK mu trueMean empiricalMean proxy T delta best chosen B hT hdelta
      (by
        intro t ht hB
        exact
          subGaussianTextbookDeltaRadius_large_gap_of_lt_half_meanGap
            trueMean proxy T delta best chosen t (hhalf_after t ht hB))
      haction hproxy hsubG

/--
Square-form deterministic algebra for the textbook delta radius: if the
quantity under the square root is below `(gap / 2)^2`, the radius is below
half the gap.
-/
theorem subGaussianTextbookDeltaRadius_lt_half_meanGap_of_sq_lt
    {K : Nat} (trueMean : Fin K -> Real)
    (proxy : Nat -> Fin K -> NNReal) (T : Nat) (delta : Real)
    (best chosen : Fin K) (t : Nat)
    (hgap_pos : 0 < meanGap trueMean best chosen)
    (hsq :
      2 * ((proxy t chosen : NNReal) : Real) *
          Real.log (textbookDeltaScale (Arm := Fin K) T delta) <
        (meanGap trueMean best chosen / 2) ^ 2) :
    subGaussianTextbookDeltaRadius proxy T delta t chosen <
      meanGap trueMean best chosen / 2 := by
  have hhalf_pos : 0 < meanGap trueMean best chosen / 2 := by
    linarith
  simpa [subGaussianTextbookDeltaRadius] using
    (Real.sqrt_lt' hhalf_pos).2 hsq

/--
Common UCB algebra form for the textbook delta radius: the sufficient condition
`8 * proxy * log(scale) < gap^2` implies `radius < gap / 2`.
-/
theorem subGaussianTextbookDeltaRadius_lt_half_meanGap_of_eight_mul_lt_sq
    {K : Nat} (trueMean : Fin K -> Real)
    (proxy : Nat -> Fin K -> NNReal) (T : Nat) (delta : Real)
    (best chosen : Fin K) (t : Nat)
    (hgap_pos : 0 < meanGap trueMean best chosen)
    (height :
      8 * ((proxy t chosen : NNReal) : Real) *
          Real.log (textbookDeltaScale (Arm := Fin K) T delta) <
        (meanGap trueMean best chosen) ^ 2) :
    subGaussianTextbookDeltaRadius proxy T delta t chosen <
      meanGap trueMean best chosen / 2 := by
  apply subGaussianTextbookDeltaRadius_lt_half_meanGap_of_sq_lt
    trueMean proxy T delta best chosen t hgap_pos
  have hsq :
      2 * ((proxy t chosen : NNReal) : Real) *
          Real.log (textbookDeltaScale (Arm := Fin K) T delta) <
        (meanGap trueMean best chosen) ^ 2 / 4 := by
    nlinarith [height]
  convert hsq using 1
  ring

/--
Eight-proxy-log threshold version of the concrete textbook-radius UCB
pull-count budget.

The remaining closed-form work is to prove the displayed square inequality
from a concrete choice of `B` and whatever sample-count/proxy monotonicity the
eventual empirical-mean construction provides.
-/
theorem lintegral_confidenceScoreArgmax_pullCount_le_textbookDeltaRadiusEightProxyLogThreshold_add_horizon_delta
    {Omega : Type} [MeasurableSpace Omega]
    {K : Nat} (hK : 0 < K)
    [MeasurableSpace (Fin K)] [MeasurableSingletonClass (Fin K)]
    (mu : Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    (trueMean : Fin K -> Real)
    (empiricalMean : Omega -> Nat -> Fin K -> Real)
    (proxy : Nat -> Fin K -> NNReal) (T : Nat) (delta : Real)
    (best chosen : Fin K) (B : Nat)
    (hT : 0 < T) (hdelta : 0 < delta)
    (hgap_pos : 0 < meanGap trueMean best chosen)
    (height_after : forall t, t < T -> B <= t ->
      8 * ((proxy t chosen : NNReal) : Real) *
          Real.log (textbookDeltaScale (Arm := Fin K) T delta) <
        (meanGap trueMean best chosen) ^ 2)
    (haction : forall t : Nat,
      Measurable
        (fun omega : Omega =>
          confidenceScoreArgmaxAction hK empiricalMean
            (subGaussianTextbookDeltaRadius proxy T delta) omega t))
    (hproxy : forall t arm, t < T ->
      0 < ((proxy t arm : NNReal) : Real))
    (hsubG : forall t arm, t < T ->
      ProbabilityTheory.HasSubgaussianMGF
        (fun omega : Omega => empiricalMean omega t arm - trueMean arm)
        (proxy t arm) mu) :
    MeasureTheory.lintegral mu
      (fun omega : Omega =>
        ((pullCount
          ((confidenceScoreArgmaxAction hK empiricalMean
            (subGaussianTextbookDeltaRadius proxy T delta)) omega)
          chosen T : Nat) : ENNReal)) <=
      (B : ENNReal) + (T : ENNReal) * ENNReal.ofReal delta := by
  exact
    lintegral_confidenceScoreArgmax_pullCount_le_textbookDeltaRadiusHalfGapThreshold_add_horizon_delta
      hK mu trueMean empiricalMean proxy T delta best chosen B hT hdelta
      (by
        intro t ht hB
        exact
          subGaussianTextbookDeltaRadius_lt_half_meanGap_of_eight_mul_lt_sq
            trueMean proxy T delta best chosen t hgap_pos
            (height_after t ht hB))
      haction hproxy hsubG

/--
Proxy-small form of the textbook radius half-gap algebra. Under a positive
logarithmic scale, bounding the selected arm's proxy by
`gap^2 / (8 * log scale)` implies the usual eight-proxy-log condition and hence
`radius < gap / 2`.
-/
theorem subGaussianTextbookDeltaRadius_lt_half_meanGap_of_proxy_lt_gap_sq_div
    {K : Nat} (trueMean : Fin K -> Real)
    (proxy : Nat -> Fin K -> NNReal) (T : Nat) (delta : Real)
    (best chosen : Fin K) (t : Nat)
    (hgap_pos : 0 < meanGap trueMean best chosen)
    (hlog_pos :
      0 < Real.log (textbookDeltaScale (Arm := Fin K) T delta))
    (hproxy_small :
      ((proxy t chosen : NNReal) : Real) <
        (meanGap trueMean best chosen) ^ 2 /
          (8 * Real.log (textbookDeltaScale (Arm := Fin K) T delta))) :
    subGaussianTextbookDeltaRadius proxy T delta t chosen <
      meanGap trueMean best chosen / 2 := by
  apply subGaussianTextbookDeltaRadius_lt_half_meanGap_of_eight_mul_lt_sq
    trueMean proxy T delta best chosen t hgap_pos
  let L : Real := Real.log (textbookDeltaScale (Arm := Fin K) T delta)
  let p : Real := ((proxy t chosen : NNReal) : Real)
  let gap : Real := meanGap trueMean best chosen
  have hL_pos : 0 < L := by
    simpa [L] using hlog_pos
  have hden_pos : 0 < 8 * L := by
    positivity
  have hmul :
      p * (8 * L) < (gap ^ 2 / (8 * L)) * (8 * L) := by
    exact mul_lt_mul_of_pos_right hproxy_small hden_pos
  have hcancel : (gap ^ 2 / (8 * L)) * (8 * L) = gap ^ 2 := by
    field_simp [ne_of_gt hden_pos, ne_of_gt hL_pos]
  calc
    8 * ((proxy t chosen : NNReal) : Real) *
        Real.log (textbookDeltaScale (Arm := Fin K) T delta)
        = p * (8 * L) := by
          simp [p, L]
          ring
    _ < (gap ^ 2 / (8 * L)) * (8 * L) := hmul
    _ = gap ^ 2 := hcancel
    _ = (meanGap trueMean best chosen) ^ 2 := by
          simp [gap]

/--
Proxy-small threshold version of the concrete textbook-radius UCB pull-count
budget.

This is the handoff expected from a later empirical-mean/sample-count leaf:
after threshold `B`, prove the selected arm's sub-Gaussian proxy is below the
displayed gap/log scale.
-/
theorem lintegral_confidenceScoreArgmax_pullCount_le_textbookDeltaRadiusProxyThreshold_add_horizon_delta
    {Omega : Type} [MeasurableSpace Omega]
    {K : Nat} (hK : 0 < K)
    [MeasurableSpace (Fin K)] [MeasurableSingletonClass (Fin K)]
    (mu : Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    (trueMean : Fin K -> Real)
    (empiricalMean : Omega -> Nat -> Fin K -> Real)
    (proxy : Nat -> Fin K -> NNReal) (T : Nat) (delta : Real)
    (best chosen : Fin K) (B : Nat)
    (hT : 0 < T) (hdelta : 0 < delta)
    (hgap_pos : 0 < meanGap trueMean best chosen)
    (hlog_pos :
      0 < Real.log (textbookDeltaScale (Arm := Fin K) T delta))
    (hproxy_small_after : forall t, t < T -> B <= t ->
      ((proxy t chosen : NNReal) : Real) <
        (meanGap trueMean best chosen) ^ 2 /
          (8 * Real.log (textbookDeltaScale (Arm := Fin K) T delta)))
    (haction : forall t : Nat,
      Measurable
        (fun omega : Omega =>
          confidenceScoreArgmaxAction hK empiricalMean
            (subGaussianTextbookDeltaRadius proxy T delta) omega t))
    (hproxy : forall t arm, t < T ->
      0 < ((proxy t arm : NNReal) : Real))
    (hsubG : forall t arm, t < T ->
      ProbabilityTheory.HasSubgaussianMGF
        (fun omega : Omega => empiricalMean omega t arm - trueMean arm)
        (proxy t arm) mu) :
    MeasureTheory.lintegral mu
      (fun omega : Omega =>
        ((pullCount
          ((confidenceScoreArgmaxAction hK empiricalMean
            (subGaussianTextbookDeltaRadius proxy T delta)) omega)
          chosen T : Nat) : ENNReal)) <=
      (B : ENNReal) + (T : ENNReal) * ENNReal.ofReal delta := by
  exact
    lintegral_confidenceScoreArgmax_pullCount_le_textbookDeltaRadiusHalfGapThreshold_add_horizon_delta
      hK mu trueMean empiricalMean proxy T delta best chosen B hT hdelta
      (by
        intro t ht hB
        exact
          subGaussianTextbookDeltaRadius_lt_half_meanGap_of_proxy_lt_gap_sq_div
            trueMean proxy T delta best chosen t hgap_pos hlog_pos
            (hproxy_small_after t ht hB))
      haction hproxy hsubG

/--
Sample-count proxy form of the textbook radius half-gap algebra. If the
selected arm's proxy is bounded by `varianceProxy / count`, then a count
threshold of the form `8 * varianceProxy * log(scale) < gap^2 * count` implies
the proxy-small condition and hence `radius < gap / 2`.
-/
theorem subGaussianTextbookDeltaRadius_lt_half_meanGap_of_proxy_le_variance_div_count
    {K : Nat} (trueMean : Fin K -> Real)
    (proxy : Nat -> Fin K -> NNReal) (T : Nat) (delta : Real)
    (best chosen : Fin K) (t : Nat)
    (varianceProxy : NNReal) (count : Nat)
    (hgap_pos : 0 < meanGap trueMean best chosen)
    (hlog_pos :
      0 < Real.log (textbookDeltaScale (Arm := Fin K) T delta))
    (hcount_pos : 0 < count)
    (hproxy_le :
      ((proxy t chosen : NNReal) : Real) <=
        ((varianceProxy : NNReal) : Real) / (count : Real))
    (hcount_large :
      8 * ((varianceProxy : NNReal) : Real) *
          Real.log (textbookDeltaScale (Arm := Fin K) T delta) <
        (meanGap trueMean best chosen) ^ 2 * (count : Real)) :
    subGaussianTextbookDeltaRadius proxy T delta t chosen <
      meanGap trueMean best chosen / 2 := by
  apply subGaussianTextbookDeltaRadius_lt_half_meanGap_of_proxy_lt_gap_sq_div
    trueMean proxy T delta best chosen t hgap_pos hlog_pos
  let L : Real := Real.log (textbookDeltaScale (Arm := Fin K) T delta)
  let v : Real := ((varianceProxy : NNReal) : Real)
  let c : Real := (count : Real)
  let gap : Real := meanGap trueMean best chosen
  have hc_pos : 0 < c := by
    simpa [c] using (Nat.cast_pos.mpr hcount_pos : (0 : Real) < (count : Real))
  have hL_pos : 0 < L := by
    simpa [L] using hlog_pos
  have hden_pos : 0 < 8 * L := by
    positivity
  have hv_div_lt :
      v / c < gap ^ 2 / (8 * L) := by
    rw [div_lt_div_iff₀ hc_pos hden_pos]
    simpa [v, c, gap, L, mul_assoc, mul_comm, mul_left_comm] using
      hcount_large
  exact lt_of_le_of_lt hproxy_le hv_div_lt

/--
Sample-count threshold version of the concrete textbook-radius UCB pull-count
budget.

This keeps the probabilistic/concentration assumptions abstract, but turns the
remaining radius-threshold algebra into explicit count and proxy contracts.
-/
theorem lintegral_confidenceScoreArgmax_pullCount_le_textbookDeltaRadiusSampleCountThreshold_add_horizon_delta
    {Omega : Type} [MeasurableSpace Omega]
    {K : Nat} (hK : 0 < K)
    [MeasurableSpace (Fin K)] [MeasurableSingletonClass (Fin K)]
    (mu : Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    (trueMean : Fin K -> Real)
    (empiricalMean : Omega -> Nat -> Fin K -> Real)
    (proxy : Nat -> Fin K -> NNReal) (T : Nat) (delta : Real)
    (best chosen : Fin K) (B : Nat)
    (varianceProxy : NNReal) (count : Nat -> Fin K -> Nat)
    (hT : 0 < T) (hdelta : 0 < delta)
    (hgap_pos : 0 < meanGap trueMean best chosen)
    (hlog_pos :
      0 < Real.log (textbookDeltaScale (Arm := Fin K) T delta))
    (hcount_pos_after : forall t, t < T -> B <= t ->
      0 < count t chosen)
    (hproxy_le_after : forall t, t < T -> B <= t ->
      ((proxy t chosen : NNReal) : Real) <=
        ((varianceProxy : NNReal) : Real) / (count t chosen : Real))
    (hcount_large_after : forall t, t < T -> B <= t ->
      8 * ((varianceProxy : NNReal) : Real) *
          Real.log (textbookDeltaScale (Arm := Fin K) T delta) <
        (meanGap trueMean best chosen) ^ 2 * (count t chosen : Real))
    (haction : forall t : Nat,
      Measurable
        (fun omega : Omega =>
          confidenceScoreArgmaxAction hK empiricalMean
            (subGaussianTextbookDeltaRadius proxy T delta) omega t))
    (hproxy : forall t arm, t < T ->
      0 < ((proxy t arm : NNReal) : Real))
    (hsubG : forall t arm, t < T ->
      ProbabilityTheory.HasSubgaussianMGF
        (fun omega : Omega => empiricalMean omega t arm - trueMean arm)
        (proxy t arm) mu) :
    MeasureTheory.lintegral mu
      (fun omega : Omega =>
        ((pullCount
          ((confidenceScoreArgmaxAction hK empiricalMean
            (subGaussianTextbookDeltaRadius proxy T delta)) omega)
          chosen T : Nat) : ENNReal)) <=
      (B : ENNReal) + (T : ENNReal) * ENNReal.ofReal delta := by
  exact
    lintegral_confidenceScoreArgmax_pullCount_le_textbookDeltaRadiusHalfGapThreshold_add_horizon_delta
      hK mu trueMean empiricalMean proxy T delta best chosen B hT hdelta
      (by
        intro t ht hB
        exact
          subGaussianTextbookDeltaRadius_lt_half_meanGap_of_proxy_le_variance_div_count
            trueMean proxy T delta best chosen t varianceProxy
            (count t chosen) hgap_pos hlog_pos
            (hcount_pos_after t ht hB)
            (hproxy_le_after t ht hB)
            (hcount_large_after t ht hB))
      haction hproxy hsubG

/--
Closed threshold-to-count algebra: if the real threshold
`8 * varianceProxy * log(scale) / gap^2` is below `B`, and `B <= count`, then
the count is large enough for the sample-count UCB radius condition.
-/
theorem subGaussianTextbookDeltaRadius_count_large_of_threshold_lt_bound
    {K : Nat} (trueMean : Fin K -> Real) (T : Nat) (delta : Real)
    (best chosen : Fin K) (varianceProxy : NNReal) (B count : Nat)
    (hgap_pos : 0 < meanGap trueMean best chosen)
    (hthreshold_lt_B :
      8 * ((varianceProxy : NNReal) : Real) *
          Real.log (textbookDeltaScale (Arm := Fin K) T delta) /
          (meanGap trueMean best chosen) ^ 2 <
        (B : Real))
    (hB_le_count : B <= count) :
    8 * ((varianceProxy : NNReal) : Real) *
        Real.log (textbookDeltaScale (Arm := Fin K) T delta) <
      (meanGap trueMean best chosen) ^ 2 * (count : Real) := by
  let gap : Real := meanGap trueMean best chosen
  let threshold : Real :=
    8 * ((varianceProxy : NNReal) : Real) *
      Real.log (textbookDeltaScale (Arm := Fin K) T delta)
  have hgap_sq_pos : 0 < gap ^ 2 := sq_pos_of_pos hgap_pos
  have hB_le_count_real : (B : Real) <= (count : Real) := by
    exact_mod_cast hB_le_count
  have hthreshold_lt_count :
      threshold / gap ^ 2 < (count : Real) :=
    lt_of_lt_of_le (by simpa [threshold, gap] using hthreshold_lt_B)
      hB_le_count_real
  have hlarge := (div_lt_iff₀ hgap_sq_pos).1 hthreshold_lt_count
  simpa [threshold, gap, mul_assoc, mul_comm, mul_left_comm] using hlarge

/--
Lower-bound-on-count version of the concrete textbook-radius UCB pull-count
budget.

A later adaptive trace leaf can aim to prove `B <= count t chosen` after the
same threshold `B`; this wrapper then supplies the usual `B + T * delta`
pull-count budget.
-/
theorem lintegral_confidenceScoreArgmax_pullCount_le_textbookDeltaRadiusSampleCountLowerBound_add_horizon_delta
    {Omega : Type} [MeasurableSpace Omega]
    {K : Nat} (hK : 0 < K)
    [MeasurableSpace (Fin K)] [MeasurableSingletonClass (Fin K)]
    (mu : Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    (trueMean : Fin K -> Real)
    (empiricalMean : Omega -> Nat -> Fin K -> Real)
    (proxy : Nat -> Fin K -> NNReal) (T : Nat) (delta : Real)
    (best chosen : Fin K) (B : Nat)
    (varianceProxy : NNReal) (count : Nat -> Fin K -> Nat)
    (hT : 0 < T) (hdelta : 0 < delta)
    (hgap_pos : 0 < meanGap trueMean best chosen)
    (hlog_pos :
      0 < Real.log (textbookDeltaScale (Arm := Fin K) T delta))
    (hB_pos : 0 < B)
    (hthreshold_lt_B :
      8 * ((varianceProxy : NNReal) : Real) *
          Real.log (textbookDeltaScale (Arm := Fin K) T delta) /
          (meanGap trueMean best chosen) ^ 2 <
        (B : Real))
    (hcount_lower_after : forall t, t < T -> B <= t ->
      B <= count t chosen)
    (hproxy_le_after : forall t, t < T -> B <= t ->
      ((proxy t chosen : NNReal) : Real) <=
        ((varianceProxy : NNReal) : Real) / (count t chosen : Real))
    (haction : forall t : Nat,
      Measurable
        (fun omega : Omega =>
          confidenceScoreArgmaxAction hK empiricalMean
            (subGaussianTextbookDeltaRadius proxy T delta) omega t))
    (hproxy : forall t arm, t < T ->
      0 < ((proxy t arm : NNReal) : Real))
    (hsubG : forall t arm, t < T ->
      ProbabilityTheory.HasSubgaussianMGF
        (fun omega : Omega => empiricalMean omega t arm - trueMean arm)
        (proxy t arm) mu) :
    MeasureTheory.lintegral mu
      (fun omega : Omega =>
        ((pullCount
          ((confidenceScoreArgmaxAction hK empiricalMean
            (subGaussianTextbookDeltaRadius proxy T delta)) omega)
          chosen T : Nat) : ENNReal)) <=
      (B : ENNReal) + (T : ENNReal) * ENNReal.ofReal delta := by
  exact
    lintegral_confidenceScoreArgmax_pullCount_le_textbookDeltaRadiusSampleCountThreshold_add_horizon_delta
      hK mu trueMean empiricalMean proxy T delta best chosen B
      varianceProxy count hT hdelta hgap_pos hlog_pos
      (by
        intro t ht hB
        exact Nat.lt_of_lt_of_le hB_pos (hcount_lower_after t ht hB))
      hproxy_le_after
      (by
        intro t ht hB
        exact
          subGaussianTextbookDeltaRadius_count_large_of_threshold_lt_bound
            trueMean T delta best chosen varianceProxy B (count t chosen)
            hgap_pos hthreshold_lt_B (hcount_lower_after t ht hB))
      haction hproxy hsubG

/--
Recursive sample-count adapter for the selected-large-count UCB budget.

For selected times whose previous recursive pull count is at least `B`, a
variance-over-count proxy bound plus the closed real threshold certificate
implies the textbook radius is below half the gap. The selected-large-count
wrapper then yields the usual `B + T * delta` pull-count budget.
-/
theorem lintegral_confidenceScoreArgmax_pullCount_le_textbookDeltaRadiusRecursiveSampleCount_add_horizon_delta
    {Omega : Type} [MeasurableSpace Omega]
    {K : Nat} (hK : 0 < K)
    [MeasurableSpace (Fin K)] [MeasurableSingletonClass (Fin K)]
    [MeasurableSpace Nat] [MeasurableAdd₂ Nat] [OpensMeasurableSpace Nat]
    (mu : Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    (trueMean : Fin K -> Real)
    (empiricalMean : Omega -> Nat -> Fin K -> Real)
    (proxy : Nat -> Fin K -> NNReal) (T : Nat) (delta : Real)
    (B : Nat) (best chosen : Fin K) (varianceProxy : NNReal)
    (hT : 0 < T) (hdelta : 0 < delta)
    (hgap_pos : 0 < meanGap trueMean best chosen)
    (hlog_pos :
      0 < Real.log (textbookDeltaScale (Arm := Fin K) T delta))
    (hB_pos : 0 < B)
    (hthreshold_lt_B :
      8 * ((varianceProxy : NNReal) : Real) *
          Real.log (textbookDeltaScale (Arm := Fin K) T delta) /
          (meanGap trueMean best chosen) ^ 2 <
        (B : Real))
    (haction : forall t : Nat,
      Measurable
        (fun omega : Omega =>
          confidenceScoreArgmaxAction hK empiricalMean
            (subGaussianTextbookDeltaRadius proxy T delta) omega t))
    (hproxy_le_selected_large : forall omega t, t < T ->
      confidenceScoreArgmaxAction hK empiricalMean
          (subGaussianTextbookDeltaRadius proxy T delta) omega t = chosen ->
        B <= pullCount
          ((confidenceScoreArgmaxAction hK empiricalMean
            (subGaussianTextbookDeltaRadius proxy T delta)) omega)
          chosen t ->
        ((proxy t chosen : NNReal) : Real) <=
          ((varianceProxy : NNReal) : Real) /
            (pullCount
              ((confidenceScoreArgmaxAction hK empiricalMean
                (subGaussianTextbookDeltaRadius proxy T delta)) omega)
              chosen t : Real))
    (hproxy : forall t arm, t < T ->
      0 < ((proxy t arm : NNReal) : Real))
    (hsubG : forall t arm, t < T ->
      ProbabilityTheory.HasSubgaussianMGF
        (fun omega : Omega => empiricalMean omega t arm - trueMean arm)
        (proxy t arm) mu) :
    MeasureTheory.lintegral mu
      (fun omega : Omega =>
        ((pullCount
          ((confidenceScoreArgmaxAction hK empiricalMean
            (subGaussianTextbookDeltaRadius proxy T delta)) omega)
          chosen T : Nat) : ENNReal)) <=
      (B : ENNReal) + (T : ENNReal) * ENNReal.ofReal delta := by
  apply
    lintegral_confidenceScoreArgmax_pullCount_le_threshold_add_horizon_delta_of_selectedLargePullCount
      hK mu trueMean empiricalMean proxy T delta B best chosen
      hT hdelta haction
  · intro omega t ht hselected hcount
    let sampleCount : Nat :=
      pullCount
        ((confidenceScoreArgmaxAction hK empiricalMean
          (subGaussianTextbookDeltaRadius proxy T delta)) omega)
        chosen t
    have hcount_pos : 0 < sampleCount := by
      exact Nat.lt_of_lt_of_le hB_pos hcount
    have hcount_large :
        8 * ((varianceProxy : NNReal) : Real) *
            Real.log (textbookDeltaScale (Arm := Fin K) T delta) <
          (meanGap trueMean best chosen) ^ 2 * (sampleCount : Real) := by
      exact
        subGaussianTextbookDeltaRadius_count_large_of_threshold_lt_bound
          trueMean T delta best chosen varianceProxy B sampleCount
          hgap_pos hthreshold_lt_B hcount
    have hhalf :
        subGaussianTextbookDeltaRadius proxy T delta t chosen <
          meanGap trueMean best chosen / 2 := by
      exact
        subGaussianTextbookDeltaRadius_lt_half_meanGap_of_proxy_le_variance_div_count
          trueMean proxy T delta best chosen t varianceProxy sampleCount
          hgap_pos hlog_pos hcount_pos
          (by
            simpa [sampleCount] using
              hproxy_le_selected_large omega t ht hselected hcount)
          hcount_large
    exact
      subGaussianTextbookDeltaRadius_large_gap_of_lt_half_meanGap
        trueMean proxy T delta best chosen t hhalf
  · exact hproxy
  · exact hsubG

/--
Source-count version of the recursive sample-count UCB budget.

This wrapper is meant for later empirical-mean leaves: they can expose their
own history-derived `sampleCount`, prove it agrees with recursive `pullCount`
on selected-large events, and provide the usual variance-over-count proxy bound
for that source count. The existing recursive sample-count adapter then gives
the same `B + T * delta` pull-count budget.
-/
theorem lintegral_confidenceScoreArgmax_pullCount_le_textbookDeltaRadiusSampleCountSource_add_horizon_delta
    {Omega : Type} [MeasurableSpace Omega]
    {K : Nat} (hK : 0 < K)
    [MeasurableSpace (Fin K)] [MeasurableSingletonClass (Fin K)]
    [MeasurableSpace Nat] [MeasurableAdd₂ Nat] [OpensMeasurableSpace Nat]
    (mu : Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    (trueMean : Fin K -> Real)
    (empiricalMean : Omega -> Nat -> Fin K -> Real)
    (proxy : Nat -> Fin K -> NNReal) (T : Nat) (delta : Real)
    (B : Nat) (best chosen : Fin K) (varianceProxy : NNReal)
    (sampleCount : Omega -> Nat -> Fin K -> Nat)
    (hT : 0 < T) (hdelta : 0 < delta)
    (hgap_pos : 0 < meanGap trueMean best chosen)
    (hlog_pos :
      0 < Real.log (textbookDeltaScale (Arm := Fin K) T delta))
    (hB_pos : 0 < B)
    (hthreshold_lt_B :
      8 * ((varianceProxy : NNReal) : Real) *
          Real.log (textbookDeltaScale (Arm := Fin K) T delta) /
          (meanGap trueMean best chosen) ^ 2 <
        (B : Real))
    (haction : forall t : Nat,
      Measurable
        (fun omega : Omega =>
          confidenceScoreArgmaxAction hK empiricalMean
            (subGaussianTextbookDeltaRadius proxy T delta) omega t))
    (hsampleCount_eq_pullCount_selected_large : forall omega t, t < T ->
      confidenceScoreArgmaxAction hK empiricalMean
          (subGaussianTextbookDeltaRadius proxy T delta) omega t = chosen ->
        B <= pullCount
          ((confidenceScoreArgmaxAction hK empiricalMean
            (subGaussianTextbookDeltaRadius proxy T delta)) omega)
          chosen t ->
        sampleCount omega t chosen =
          pullCount
            ((confidenceScoreArgmaxAction hK empiricalMean
              (subGaussianTextbookDeltaRadius proxy T delta)) omega)
            chosen t)
    (hproxy_le_sampleCount_selected_large : forall omega t, t < T ->
      confidenceScoreArgmaxAction hK empiricalMean
          (subGaussianTextbookDeltaRadius proxy T delta) omega t = chosen ->
        B <= pullCount
          ((confidenceScoreArgmaxAction hK empiricalMean
            (subGaussianTextbookDeltaRadius proxy T delta)) omega)
          chosen t ->
        ((proxy t chosen : NNReal) : Real) <=
          ((varianceProxy : NNReal) : Real) /
            (sampleCount omega t chosen : Real))
    (hproxy : forall t arm, t < T ->
      0 < ((proxy t arm : NNReal) : Real))
    (hsubG : forall t arm, t < T ->
      ProbabilityTheory.HasSubgaussianMGF
        (fun omega : Omega => empiricalMean omega t arm - trueMean arm)
        (proxy t arm) mu) :
    MeasureTheory.lintegral mu
      (fun omega : Omega =>
        ((pullCount
          ((confidenceScoreArgmaxAction hK empiricalMean
            (subGaussianTextbookDeltaRadius proxy T delta)) omega)
          chosen T : Nat) : ENNReal)) <=
      (B : ENNReal) + (T : ENNReal) * ENNReal.ofReal delta := by
  exact
    lintegral_confidenceScoreArgmax_pullCount_le_textbookDeltaRadiusRecursiveSampleCount_add_horizon_delta
      hK mu trueMean empiricalMean proxy T delta B best chosen varianceProxy
      hT hdelta hgap_pos hlog_pos hB_pos hthreshold_lt_B haction
      (by
        intro omega t ht hselected hcount
        have hsample :
            sampleCount omega t chosen =
              pullCount
            ((confidenceScoreArgmaxAction hK empiricalMean
              (subGaussianTextbookDeltaRadius proxy T delta)) omega)
            chosen t :=
          hsampleCount_eq_pullCount_selected_large omega t ht hselected hcount
        simpa [hsample] using
          hproxy_le_sampleCount_selected_large omega t ht hselected hcount)
      hproxy hsubG

/--
History-action source-count version of the textbook-radius UCB pull-count
budget.

If an externally generated history trace agrees with the concrete
score-argmax UCB trace throughout the horizon, and its own recursive pull count
supplies the variance-over-count proxy contract on selected-large events, then
that history trace inherits the same `B + T * delta` selected-arm count budget.
-/
theorem lintegral_historyAction_pullCount_le_textbookDeltaRadiusSampleCountSource_add_horizon_delta
    {Omega : Type} [MeasurableSpace Omega]
    {K : Nat} (hK : 0 < K)
    [MeasurableSpace (Fin K)] [MeasurableSingletonClass (Fin K)]
    [MeasurableSpace Nat] [MeasurableAdd₂ Nat] [OpensMeasurableSpace Nat]
    (mu : Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    (trueMean : Fin K -> Real)
    (empiricalMean : Omega -> Nat -> Fin K -> Real)
    (proxy : Nat -> Fin K -> NNReal) (T : Nat) (delta : Real)
    (B : Nat) (best chosen : Fin K) (varianceProxy : NNReal)
    (historyAction : Omega -> ActionTrace (Fin K))
    (hT : 0 < T) (hdelta : 0 < delta)
    (hgap_pos : 0 < meanGap trueMean best chosen)
    (hlog_pos :
      0 < Real.log (textbookDeltaScale (Arm := Fin K) T delta))
    (hB_pos : 0 < B)
    (hthreshold_lt_B :
      8 * ((varianceProxy : NNReal) : Real) *
          Real.log (textbookDeltaScale (Arm := Fin K) T delta) /
          (meanGap trueMean best chosen) ^ 2 <
        (B : Real))
    (haction : forall t : Nat,
      Measurable
        (fun omega : Omega =>
          confidenceScoreArgmaxAction hK empiricalMean
            (subGaussianTextbookDeltaRadius proxy T delta) omega t))
    (hhistoryAction_eq_argmax : forall omega t, t < T ->
      historyAction omega t =
        confidenceScoreArgmaxAction hK empiricalMean
          (subGaussianTextbookDeltaRadius proxy T delta) omega t)
    (hproxy_le_history_selected_large : forall omega t, t < T ->
      historyAction omega t = chosen ->
        B <= pullCount (historyAction omega) chosen t ->
        ((proxy t chosen : NNReal) : Real) <=
          ((varianceProxy : NNReal) : Real) /
            (pullCount (historyAction omega) chosen t : Real))
    (hproxy : forall t arm, t < T ->
      0 < ((proxy t arm : NNReal) : Real))
    (hsubG : forall t arm, t < T ->
      ProbabilityTheory.HasSubgaussianMGF
        (fun omega : Omega => empiricalMean omega t arm - trueMean arm)
        (proxy t arm) mu) :
    MeasureTheory.lintegral mu
      (fun omega : Omega =>
        ((pullCount (historyAction omega) chosen T : Nat) : ENNReal)) <=
      (B : ENNReal) + (T : ENNReal) * ENNReal.ofReal delta := by
  let scoreAction : Omega -> ActionTrace (Fin K) :=
    fun omega t =>
      confidenceScoreArgmaxAction hK empiricalMean
        (subGaussianTextbookDeltaRadius proxy T delta) omega t
  have hscore :
      MeasureTheory.lintegral mu
        (fun omega : Omega =>
          ((pullCount (scoreAction omega) chosen T : Nat) : ENNReal)) <=
        (B : ENNReal) + (T : ENNReal) * ENNReal.ofReal delta := by
    simpa [scoreAction] using
      lintegral_confidenceScoreArgmax_pullCount_le_textbookDeltaRadiusSampleCountSource_add_horizon_delta
        hK mu trueMean empiricalMean proxy T delta B best chosen
        varianceProxy
        (fun omega t arm => pullCount (historyAction omega) arm t)
        hT hdelta hgap_pos hlog_pos hB_pos hthreshold_lt_B haction
        (by
          intro omega t ht _hselected _hcount
          exact
            pullCount_eq_of_forall_lt
              (historyAction omega)
              ((confidenceScoreArgmaxAction hK empiricalMean
                (subGaussianTextbookDeltaRadius proxy T delta)) omega)
              chosen t
              (fun s hs =>
                hhistoryAction_eq_argmax omega s (Nat.lt_trans hs ht)))
        (by
          intro omega t ht hselected hcount
          have hselected_history : historyAction omega t = chosen := by
            simpa [hhistoryAction_eq_argmax omega t ht] using hselected
          have hcount_history :
              B <= pullCount (historyAction omega) chosen t := by
            have hcount_eq :
                pullCount (historyAction omega) chosen t =
                  pullCount
                    ((confidenceScoreArgmaxAction hK empiricalMean
                      (subGaussianTextbookDeltaRadius proxy T delta)) omega)
                    chosen t :=
              pullCount_eq_of_forall_lt
                (historyAction omega)
                ((confidenceScoreArgmaxAction hK empiricalMean
                  (subGaussianTextbookDeltaRadius proxy T delta)) omega)
                chosen t
                (fun s hs =>
                  hhistoryAction_eq_argmax omega s (Nat.lt_trans hs ht))
            simpa [hcount_eq] using hcount
          exact
            hproxy_le_history_selected_large omega t ht
              hselected_history hcount_history)
        hproxy hsubG
  have htarget :
      (fun omega : Omega =>
        ((pullCount (historyAction omega) chosen T : Nat) : ENNReal)) =
      (fun omega : Omega =>
        ((pullCount (scoreAction omega) chosen T : Nat) : ENNReal)) := by
    funext omega
    have hcount_eq :
        pullCount (historyAction omega) chosen T =
          pullCount (scoreAction omega) chosen T :=
      pullCount_eq_of_forall_lt
        (historyAction omega) (scoreAction omega) chosen T
        (fun s hs => by
          simpa [scoreAction] using hhistoryAction_eq_argmax omega s hs)
    simp [hcount_eq]
  simpa [htarget] using hscore

/--
Generated-policy source-count version of the textbook-radius UCB pull-count
budget.

This packages the previous history-action wrapper for a concrete
`Policy.generatedActionTrace`.  Pointwise equality with score argmax over all
time coordinates transfers measurability from the generated policy trace to the
score-argmax trace, and the existing history-action adapter supplies the
`B + T * delta` selected-arm count budget.
-/
theorem lintegral_generatedActionTrace_pullCount_le_textbookDeltaRadiusSampleCountSource_add_horizon_delta
    {Omega State : Type} [MeasurableSpace Omega] [MeasurableSpace State]
    {K : Nat} (hK : 0 < K)
    [MeasurableSpace (Fin K)] [MeasurableSingletonClass (Fin K)]
    [MeasurableSpace Nat] [MeasurableAdd₂ Nat] [OpensMeasurableSpace Nat]
    (mu : Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    (trueMean : Fin K -> Real)
    (empiricalMean : Omega -> Nat -> Fin K -> Real)
    (proxy : Nat -> Fin K -> NNReal) (T : Nat) (delta : Real)
    (B : Nat) (best chosen : Fin K) (varianceProxy : NNReal)
    (policy : Policy.MeasurablePolicy State (Fin K))
    (state : Nat -> Omega -> State)
    (hT : 0 < T) (hdelta : 0 < delta)
    (hgap_pos : 0 < meanGap trueMean best chosen)
    (hlog_pos :
      0 < Real.log (textbookDeltaScale (Arm := Fin K) T delta))
    (hB_pos : 0 < B)
    (hthreshold_lt_B :
      8 * ((varianceProxy : NNReal) : Real) *
          Real.log (textbookDeltaScale (Arm := Fin K) T delta) /
          (meanGap trueMean best chosen) ^ 2 <
        (B : Real))
    (hstate : forall t : Nat, Measurable (state t))
    (hgenerated_eq_argmax : forall omega t,
      (Policy.generatedActionTrace policy state omega) t =
        confidenceScoreArgmaxAction hK empiricalMean
          (subGaussianTextbookDeltaRadius proxy T delta) omega t)
    (hproxy_le_generated_selected_large : forall omega t, t < T ->
      (Policy.generatedActionTrace policy state omega) t = chosen ->
        B <= pullCount
          (Policy.generatedActionTrace policy state omega) chosen t ->
        ((proxy t chosen : NNReal) : Real) <=
          ((varianceProxy : NNReal) : Real) /
            (pullCount
              (Policy.generatedActionTrace policy state omega) chosen t :
              Real))
    (hproxy : forall t arm, t < T ->
      0 < ((proxy t arm : NNReal) : Real))
    (hsubG : forall t arm, t < T ->
      ProbabilityTheory.HasSubgaussianMGF
        (fun omega : Omega => empiricalMean omega t arm - trueMean arm)
        (proxy t arm) mu) :
    MeasureTheory.lintegral mu
      (fun omega : Omega =>
        ((pullCount
          (Policy.generatedActionTrace policy state omega) chosen T : Nat) :
          ENNReal)) <=
      (B : ENNReal) + (T : ENNReal) * ENNReal.ofReal delta := by
  exact
    lintegral_historyAction_pullCount_le_textbookDeltaRadiusSampleCountSource_add_horizon_delta
      hK mu trueMean empiricalMean proxy T delta B best chosen varianceProxy
      (Policy.generatedActionTrace policy state)
      hT hdelta hgap_pos hlog_pos hB_pos hthreshold_lt_B
      (by
        intro t
        have hgen :
            Measurable
              (fun omega : Omega =>
                (Policy.generatedActionTrace policy state omega) t) :=
          Policy.measurable_generatedActionTrace_eval_of_measurable_state
            policy state hstate t
        have heq :
            (fun omega : Omega =>
              confidenceScoreArgmaxAction hK empiricalMean
                (subGaussianTextbookDeltaRadius proxy T delta) omega t) =
            (fun omega : Omega =>
              (Policy.generatedActionTrace policy state omega) t) := by
          funext omega
          exact (hgenerated_eq_argmax omega t).symm
        rw [heq]
        exact hgen)
      (by
        intro omega t _ht
        exact hgenerated_eq_argmax omega t)
      hproxy_le_generated_selected_large hproxy hsubG

/--
Two-sided sub-Gaussian tail budget for a UCB empirical mean at time `t` and
arm `arm`.

The proxy is for the centered variable `empiricalMean t arm - trueMean arm`.
This is still abstract: a later empirical-mean construction must prove the
sub-Gaussian proxy and choose the usual log/sqrt radius.
-/
noncomputable def subGaussianAbsDeviationTail
    {Arm : Type}
    (radius : Nat -> Arm -> Real)
    (proxy : Nat -> Arm -> NNReal) (t : Nat) (arm : Arm) : ENNReal :=
  ENNReal.ofReal
    (2 *
      Real.exp (-(radius t arm) ^ 2 /
        (2 * ((proxy t arm : NNReal) : Real))))

/--
Single-time two-sided sub-Gaussian tail for the UCB absolute-deviation event.
-/
theorem measure_absDeviation_le_subGaussian_tail
    {Omega Arm : Type} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (trueMean : Arm -> Real)
    (empiricalMean : Omega -> Nat -> Arm -> Real)
    (radius : Nat -> Arm -> Real)
    (proxy : Nat -> Arm -> NNReal) (t : Nat) (arm : Arm)
    (hradius : 0 <= radius t arm)
    (hsubG :
      ProbabilityTheory.HasSubgaussianMGF
        (fun omega : Omega => empiricalMean omega t arm - trueMean arm)
        (proxy t arm) mu) :
    mu {omega | radius t arm <=
        |empiricalMean omega t arm - trueMean arm|} <=
      subGaussianAbsDeviationTail radius proxy t arm := by
  let X : Omega -> Real :=
    fun omega => empiricalMean omega t arm - trueMean arm
  let eps := radius t arm
  let tailReal : Real :=
    Real.exp (-(radius t arm) ^ 2 /
      (2 * ((proxy t arm : NNReal) : Real)))
  have htail_nonneg : 0 <= tailReal := (Real.exp_pos _).le
  have hsubGX :
      ProbabilityTheory.HasSubgaussianMGF X (proxy t arm) mu := by
    simpa [X] using hsubG
  have hupperReal :
      mu.real {omega | eps <= X omega} <= tailReal := by
    simpa [X, eps, tailReal] using
      (ProbabilityTheory.HasSubgaussianMGF.measure_ge_le
        (X := X) (c := proxy t arm) (μ := mu) hsubGX hradius)
  have hupper :
      mu {omega | eps <= X omega} <= ENNReal.ofReal tailReal := by
    rw [Measure.real] at hupperReal
    exact (ENNReal.le_ofReal_iff_toReal_le
      (measure_ne_top mu {omega | eps <= X omega}) htail_nonneg).2
      hupperReal
  have hlowerReal :
      mu.real {omega | eps <= (-X) omega} <= tailReal := by
    have hneg : ProbabilityTheory.HasSubgaussianMGF
        (-X) (proxy t arm) mu := hsubGX.neg
    simpa [X, eps, tailReal] using
      (ProbabilityTheory.HasSubgaussianMGF.measure_ge_le
        (X := -X)
        (c := proxy t arm) (μ := mu) hneg hradius)
  have hlower :
      mu {omega | eps <= (-X) omega} <= ENNReal.ofReal tailReal := by
    rw [Measure.real] at hlowerReal
    exact (ENNReal.le_ofReal_iff_toReal_le
      (measure_ne_top mu {omega | eps <= (-X) omega}) htail_nonneg).2
      hlowerReal
  have hsubset :
      {omega | eps <= |X omega|} ⊆
        {omega | eps <= X omega} ∪ {omega | eps <= (-X) omega} := by
    intro omega homega
    by_cases hnonneg : 0 <= X omega
    · exact Or.inl (by simpa [abs_of_nonneg hnonneg] using homega)
    · have hnonpos : X omega <= 0 := le_of_not_ge hnonneg
      exact Or.inr (by simpa [abs_of_nonpos hnonpos] using homega)
  calc
    mu {omega | radius t arm <=
        |empiricalMean omega t arm - trueMean arm|}
        <= mu ({omega | eps <= X omega} ∪
          {omega | eps <= (-X) omega}) := by
          exact measure_mono (by
            intro omega homega
            exact hsubset (by simpa [X, eps] using homega))
    _ <= mu {omega | eps <= X omega} +
        mu {omega | eps <= (-X) omega} := by
          exact measure_union_le
            {omega | eps <= X omega} {omega | eps <= (-X) omega}
    _ <= ENNReal.ofReal tailReal + ENNReal.ofReal tailReal := by
          exact add_le_add hupper hlower
    _ = subGaussianAbsDeviationTail radius proxy t arm := by
          rw [← ENNReal.ofReal_add htail_nonneg htail_nonneg]
          simp [subGaussianAbsDeviationTail, tailReal, two_mul]

/--
Finite-horizon UCB confidence bad-event bound from abstract sub-Gaussian
absolute-deviation tails.

This is the UCB-facing sub-Gaussian producer layer. It still leaves empirical
mean construction, proxy simplification, log/sqrt radius choice, pull-count
bounds, and final regret to later leaves.
-/
theorem measure_finiteHorizonConfidenceBadEvent_le_subGaussian_tail_sum
    {Omega Arm : Type} [MeasurableSpace Omega] [Fintype Arm]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (trueMean : Arm -> Real)
    (empiricalMean : Omega -> Nat -> Arm -> Real)
    (radius : Nat -> Arm -> Real)
    (proxy : Nat -> Arm -> NNReal) (T : Nat)
    (hradius : forall t arm, t < T -> 0 <= radius t arm)
    (hsubG : forall t arm, t < T ->
      ProbabilityTheory.HasSubgaussianMGF
        (fun omega : Omega => empiricalMean omega t arm - trueMean arm)
        (proxy t arm) mu) :
    mu (finiteHorizonConfidenceBadEvent trueMean empiricalMean radius T) <=
      (Finset.range T).sum
        (fun t =>
          (Finset.univ : Finset Arm).sum
            (fun arm =>
              subGaussianAbsDeviationTail radius proxy t arm +
                subGaussianAbsDeviationTail radius proxy t arm)) := by
  exact measure_finiteHorizonConfidenceBadEvent_le_absDeviation_tail_sum
    mu trueMean empiricalMean radius
    (fun t arm => subGaussianAbsDeviationTail radius proxy t arm)
    T
    (fun t arm ht =>
      measure_absDeviation_le_subGaussian_tail
        mu trueMean empiricalMean radius proxy t arm
        (hradius t arm ht) (hsubG t arm ht))

/-- The proof-DAG leaves usually needed for UCB regret formalization. -/
def obligationNames : List String :=
  [ "initial_round_robin_count_positive"
  , "ucb_index_maximality"
  , "good_event_gap_implies_count_bound"
  , "subgaussian_upper_tail"
  , "subgaussian_lower_tail"
  , "expected_pull_count_bound"
  , "regret_from_pull_count_bounds"
  ]

end UCB
end BanditRLProof
