import BanditRLProof.OFULScheduledAllHorizonAllRoundGap

/-!
# Explicit all-horizon high-probability OFUL pseudo-regret rate

This module eliminates the telescoping confidence schedule from the displayed
budget of the one-policy all-horizon pseudo-regret theorem.
-/

namespace BanditRLProof
namespace OFUL

open MeasureTheory Real Matrix Set
open scoped ENNReal

universe u

/--
The explicit confidence logarithm induced at horizon `T` by the telescoping
failure share `delta / ((T+1)(T+2))`.
-/
noncomputable def telescopingHighProbabilityRegretLogBudget
    {Feature : Type u} [Fintype Feature]
    (lambda delta : Real) (horizon : Nat) (L2 : Real) : Real :=
  standardScalarLogDetBudget
      (Feature := Feature) lambda (horizon + 1) L2 +
    2 * Real.log
      ((((horizon + 1 : Nat) : Real) *
          ((horizon + 2 : Nat) : Real)) / delta)

/--
Explicit complete all-round pseudo-regret budget for the telescoping-schedule
policy at a finite horizon.
-/
noncomputable def telescopingHighProbabilityPseudoRegretBound
    {Feature : Type u} [Fintype Feature]
    (R delta lambda S : Real) (horizon : Nat) (L2 : Real) : Real :=
  2 * S * Real.sqrt L2 +
    2 *
      (R * Real.sqrt
          (telescopingHighProbabilityRegretLogBudget
            (Feature := Feature) lambda delta horizon L2) +
        Real.sqrt lambda * S) *
      (Real.sqrt (((horizon + 1 : Nat) : Real)) *
        Real.sqrt
          (2 *
            standardScalarLogDetBudget
              (Feature := Feature) lambda (horizon + 1) L2))

/--
The time-`T` telescoping share is a finite-window confidence parameter with
outer budget `delta / (T+2)`.
-/
theorem allTimeTelescopingDelta_eq_outerBudget_div_succ
    (delta : Real) (horizon : Nat) :
    allTimeTelescopingDelta delta horizon =
      (delta / (((horizon + 2 : Nat) : Real))) /
        (((horizon + 1 : Nat) : Real)) := by
  rw [allTimeTelescopingDelta_eq_div]
  field_simp

/--
The finite-window confidence logarithm at outer budget `delta / (T+2)` is the
explicit telescoping confidence logarithm.
-/
theorem
    standardHighProbabilityRegretLogBudget_outerBudget_eq_telescoping
    {Feature : Type u} [Fintype Feature]
    (lambda delta : Real) (hdelta : 0 < delta)
    (horizon : Nat) (L2 : Real) :
    standardHighProbabilityRegretLogBudget
        (Feature := Feature)
        lambda (delta / (((horizon + 2 : Nat) : Real))) horizon L2 =
      telescopingHighProbabilityRegretLogBudget
        (Feature := Feature) lambda delta horizon L2 := by
  have hscale :
      (((horizon + 1 : Nat) : Real)) /
          (delta / (((horizon + 2 : Nat) : Real))) =
        ((((horizon + 1 : Nat) : Real) *
            ((horizon + 2 : Nat) : Real)) / delta) := by
    field_simp
  unfold standardHighProbabilityRegretLogBudget
    telescopingHighProbabilityRegretLogBudget
  rw [hscale]

/--
The finite-window explicit pseudo-regret budget at outer confidence
`delta / (T+2)` is exactly the explicit telescoping budget.
-/
theorem
    standardHighProbabilityPseudoRegretBound_outerBudget_eq_telescoping
    {Feature : Type u} [Fintype Feature]
    (R delta lambda S : Real) (hdelta : 0 < delta)
    (horizon : Nat) (L2 : Real) :
    standardHighProbabilityPseudoRegretBound
        (Feature := Feature)
        R (delta / (((horizon + 2 : Nat) : Real)))
        lambda S horizon L2 =
      telescopingHighProbabilityPseudoRegretBound
        (Feature := Feature) R delta lambda S horizon L2 := by
  unfold standardHighProbabilityPseudoRegretBound
    telescopingHighProbabilityPseudoRegretBound
  rw [
    standardHighProbabilityRegretLogBudget_outerBudget_eq_telescoping
      (Feature := Feature) lambda delta hdelta horizon L2]

/--
The named scheduled all-round budget is exactly the explicit telescoping
pseudo-regret rate at every finite horizon.
-/
theorem
    telescopingStandardScalarAllRoundGapBound_eq_telescopingHighProbabilityPseudoRegretBound
    {Feature : Type u}
    [Fintype Feature] [Nonempty Feature]
    (R : Real) (hR : 0 < R)
    (delta : Real) (hdelta : 0 < delta) (hdelta_one : delta <= 1)
    (lambda : Real) (hlambda : 0 < lambda)
    (S : Real)
    (horizon : Nat) (L2 : Real) (hL2 : 0 <= L2) :
    telescopingStandardScalarAllRoundGapBound
        (Feature := Feature) R delta lambda S horizon L2 =
      telescopingHighProbabilityPseudoRegretBound
        (Feature := Feature) R delta lambda S horizon L2 := by
  have hden_pos :
      0 < (((horizon + 2 : Nat) : Real)) := by
    positivity
  have hden_one :
      (1 : Real) <= (((horizon + 2 : Nat) : Real)) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le (horizon + 1))
  have houter_pos :
      0 < delta / (((horizon + 2 : Nat) : Real)) :=
    div_pos hdelta hden_pos
  have houter_one :
      delta / (((horizon + 2 : Nat) : Real)) <= 1 :=
    (div_le_one hden_pos).2 (hdelta_one.trans hden_one)
  calc
    telescopingStandardScalarAllRoundGapBound
        (Feature := Feature) R delta lambda S horizon L2 =
      standardScalarAllRoundGapBound
        (Feature := Feature)
        R (delta / (((horizon + 2 : Nat) : Real)))
        lambda S horizon L2 := by
      unfold telescopingStandardScalarAllRoundGapBound
        telescopingStandardScalarRadiusWidthBound
        standardScalarAllRoundGapBound
      rw [allTimeTelescopingDelta_eq_outerBudget_div_succ]
    _ =
      standardHighProbabilityPseudoRegretBound
        (Feature := Feature)
        R (delta / (((horizon + 2 : Nat) : Real)))
        lambda S horizon L2 := by
      exact
        standardScalarAllRoundGapBound_eq_standardHighProbabilityPseudoRegretBound
          (Feature := Feature)
          R hR
          (delta / (((horizon + 2 : Nat) : Real)))
          houter_pos houter_one lambda hlambda S horizon L2 hL2
    _ =
      telescopingHighProbabilityPseudoRegretBound
        (Feature := Feature) R delta lambda S horizon L2 := by
      exact
        standardHighProbabilityPseudoRegretBound_outerBudget_eq_telescoping
          (Feature := Feature) R delta lambda S hdelta horizon L2

/--
Explicit all-horizon violation event for the named fixed-best pseudo-regret
under the one telescoping-schedule policy.
-/
noncomputable def
    telescopingCanonicalExplicitHighProbabilityPseudoRegretAllHorizonViolationSet
    {K : Nat} {Feature : Type u}
    [Fintype Feature]
    (lambda : Real)
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S L2 : Real)
    (best : Fin K) :
    Set (Nat -> Prod (Fin K) Real) :=
  {trajectory | exists horizon,
    telescopingHighProbabilityPseudoRegretBound
        (Feature := Feature) R delta lambda S horizon L2 <
      canonicalStandardHighProbabilityPseudoRegret
        thetaStar actionFeature best horizon trajectory}

/--
The explicit violation event is the compiled abstract scheduled violation
event.
-/
theorem
    telescopingCanonicalExplicitHighProbabilityPseudoRegretAllHorizonViolationSet_eq_standard
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [Nonempty Feature]
    (lambda : Real) (hlambda : 0 < lambda)
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R : Real) (hR : 0 < R)
    (delta : Real) (hdelta : 0 < delta) (hdelta_one : delta <= 1)
    (S L2 : Real) (hL2 : 0 <= L2)
    (best : Fin K) :
    telescopingCanonicalExplicitHighProbabilityPseudoRegretAllHorizonViolationSet
        lambda thetaStar actionFeature R delta S L2 best =
      telescopingCanonicalStandardHighProbabilityPseudoRegretAllHorizonViolationSet
        lambda thetaStar actionFeature R delta S L2 best := by
  ext trajectory
  constructor
  · rintro ⟨horizon, hviolation⟩
    refine ⟨horizon, ?_⟩
    rw [
      telescopingStandardScalarAllRoundGapBound_eq_telescopingHighProbabilityPseudoRegretBound
        (Feature := Feature)
        R hR delta hdelta hdelta_one lambda hlambda S horizon L2 hL2]
    exact hviolation
  · rintro ⟨horizon, hviolation⟩
    refine ⟨horizon, ?_⟩
    rw [←
      telescopingStandardScalarAllRoundGapBound_eq_telescopingHighProbabilityPseudoRegretBound
        (Feature := Feature)
        R hR delta hdelta hdelta_one lambda hlambda S horizon L2 hL2]
    exact hviolation

/--
Complete explicit one-policy all-horizon high-probability pseudo-regret
theorem for telescoping-schedule OFUL.
-/
theorem
    telescopingCanonicalStandardHighProbabilityPseudoRegret_nonneg_and_allHorizon_tail_le_explicitBound_of_linearSubgaussianEnvironment_of_featureBound_le_regularization
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature] [Nonempty Feature]
    (hK : 0 < K)
    (lambda : Real) (hlambda : 0 < lambda)
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R : Real) (hR : 0 < R)
    (delta : Real) (hdelta : 0 < delta) (hdelta_one : delta <= 1)
    (S : Real) (hS : 0 <= S)
    (environment : Thompson.HistoryEnvironment (Fin K) Real)
    (L2 : Real) (hL2 : 0 <= L2)
    (hactionFeatureBound : forall action,
      dotProduct (actionFeature action) (actionFeature action) <= L2)
    (hL2lambda : L2 <= lambda)
    (best : Fin K)
    (hbest : IsOptimalLinearArm thetaStar actionFeature best)
    (source : CanonicalLinearSubgaussianEnvironmentLaw
      hK thetaStar actionFeature R S environment) :
    (forall horizon trajectory,
      0 <= canonicalStandardHighProbabilityPseudoRegret
        thetaStar actionFeature best horizon trajectory) /\
      Thompson.canonicalHistoryTrajectoryMeasure
          (finiteHistoryTelescopingScalarRidgeOptimisticAlgorithm
            hK lambda actionFeature R delta S)
          environment
          (telescopingCanonicalExplicitHighProbabilityPseudoRegretAllHorizonViolationSet
            lambda thetaStar actionFeature R delta S L2 best) <=
        ENNReal.ofReal delta := by
  have hmain :=
    telescopingCanonicalStandardHighProbabilityPseudoRegret_nonneg_and_allHorizon_tail_le_of_linearSubgaussianEnvironment_of_featureBound_le_regularization
      hK lambda hlambda thetaStar actionFeature R hR
      delta hdelta hdelta_one S hS environment L2 hL2
      hactionFeatureBound hL2lambda best hbest source
  constructor
  · exact hmain.1
  · rw [
      telescopingCanonicalExplicitHighProbabilityPseudoRegretAllHorizonViolationSet_eq_standard
        lambda hlambda thetaStar actionFeature R hR
        delta hdelta hdelta_one S L2 hL2 best]
    exact hmain.2

end OFUL
end BanditRLProof
