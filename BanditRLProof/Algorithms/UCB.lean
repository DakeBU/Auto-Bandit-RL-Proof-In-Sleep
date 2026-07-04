import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.Tactic.Linarith
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
