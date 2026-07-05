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
