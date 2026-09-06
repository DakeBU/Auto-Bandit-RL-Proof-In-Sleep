import BanditRLProof.OFULScheduledAllHorizonHighProbabilityRegretRate
import Mathlib.Probability.Process.Stopping

/-!
# Bounded stopping-time high-probability OFUL pseudo-regret rate

This module evaluates the explicit one-policy all-horizon OFUL rate at a
bounded stopping time. The probability argument is pathwise event domination,
not optional stopping and not a new union bound.
-/

namespace BanditRLProof
namespace OFUL

open MeasureTheory Real Matrix Set
open scoped ENNReal

universe u

/--
The canonical trajectory filtration through the current round. At level `T`
it contains exactly the coordinates `0, ..., T`.
-/
def canonicalHistoryTrajectoryAllRoundFiltration
    {K : Nat} :
    Filtration Nat
      (inferInstance : MeasurableSpace (Nat -> Fin K × Real)) :=
  Filtration.piLE (X := fun _ : Nat => Fin K × Real)

@[simp]
theorem canonicalHistoryTrajectoryAllRoundFiltration_apply
    {K : Nat} (horizon : Nat) :
    (canonicalHistoryTrajectoryAllRoundFiltration (K := K) horizon :
      MeasurableSpace (Nat -> Fin K × Real)) =
      Filtration.piLE (X := fun _ : Nat => Fin K × Real) horizon :=
  rfl

/-- Every coordinate `t <= T` is measurable at all-round level `T`. -/
theorem measurable_canonicalHistoryTrajectory_coordinate_allRound
    {K : Nat} {t horizon : Nat} (ht : t <= horizon) :
    @Measurable (Nat -> Fin K × Real) (Fin K × Real)
      (canonicalHistoryTrajectoryAllRoundFiltration (K := K) horizon)
      inferInstance
      (fun trajectory => trajectory t) := by
  have hprefix :
      @Measurable (Nat -> Fin K × Real)
        ((i : Finset.Iic horizon) -> Fin K × Real)
        (canonicalHistoryTrajectoryAllRoundFiltration (K := K) horizon)
        inferInstance
        (Preorder.frestrictLe horizon) := by
    rw [canonicalHistoryTrajectoryAllRoundFiltration_apply,
      Filtration.piLE_eq_comap_frestrictLe]
    exact Measurable.of_comap_le le_rfl
  let index : Finset.Iic horizon := ⟨t, Finset.mem_Iic.mpr ht⟩
  have heval :
      Measurable
        (fun history : (i : Finset.Iic horizon) -> Fin K × Real =>
          history index) :=
    measurable_pi_apply index
  simpa [index, Preorder.frestrictLe] using heval.comp hprefix

/-- A trajectory time below a finite deterministic horizon cannot be `top`. -/
theorem boundedTrajectoryTime_ne_top
    {K : Nat}
    (tau : (Nat -> Fin K × Real) -> WithTop Nat)
    (maxHorizon : Nat)
    (htau_le : forall trajectory,
      tau trajectory <= (maxHorizon : WithTop Nat)) :
    forall trajectory, tau trajectory ≠ (⊤ : WithTop Nat) := by
  intro trajectory
  exact
    ne_top_of_le_ne_top WithTop.coe_ne_top (htau_le trajectory)

/-- Under a finite bound, `untopA` recovers the actual stopping-time value. -/
theorem coe_untopA_boundedTrajectoryTime
    {K : Nat}
    (tau : (Nat -> Fin K × Real) -> WithTop Nat)
    (maxHorizon : Nat)
    (htau_le : forall trajectory,
      tau trajectory <= (maxHorizon : WithTop Nat))
    (trajectory : Nat -> Fin K × Real) :
    ((tau trajectory).untopA : WithTop Nat) = tau trajectory := by
  have hne : tau trajectory ≠ (⊤ : WithTop Nat) :=
    boundedTrajectoryTime_ne_top tau maxHorizon htau_le trajectory
  rw [WithTop.untopA_eq_untop hne]
  exact WithTop.coe_untop _ hne

/--
Complete fixed-best pseudo-regret through horizon `T` is measurable using only
trajectory coordinates `0, ..., T`.
-/
theorem measurable_canonicalStandardHighProbabilityPseudoRegret_allRound
    {K : Nat} {Feature : Type u}
    [Fintype Feature]
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (best : Fin K) (horizon : Nat) :
    @Measurable (Nat -> Fin K × Real) Real
      (canonicalHistoryTrajectoryAllRoundFiltration (K := K) horizon)
      inferInstance
      (canonicalStandardHighProbabilityPseudoRegret
        thetaStar actionFeature best horizon) := by
  have hprefix :
      @Measurable (Nat -> Fin K × Real)
        ((i : Finset.Iic horizon) -> Fin K × Real)
        (canonicalHistoryTrajectoryAllRoundFiltration (K := K) horizon)
        inferInstance
        (Preorder.frestrictLe horizon) := by
    rw [canonicalHistoryTrajectoryAllRoundFiltration_apply,
      Filtration.piLE_eq_comap_frestrictLe]
    exact Measurable.of_comap_le le_rfl
  have hfinite :
      Measurable
        (fun history : (i : Finset.Iic horizon) -> Fin K × Real =>
          (Finset.range (horizon + 1)).sum (fun t =>
            linearValue thetaStar (actionFeature best) -
              linearValue thetaStar
                (actionFeature
                  (if ht : t <= horizon then
                    (history ⟨t, Finset.mem_Iic.mpr ht⟩).1
                  else best)))) := by
    refine Finset.measurable_sum (Finset.range (horizon + 1)) fun t ht => ?_
    have ht_le : t <= horizon :=
      Nat.le_of_lt_succ (Finset.mem_range.mp ht)
    let index : Finset.Iic horizon :=
      ⟨t, Finset.mem_Iic.mpr ht_le⟩
    simp only [dif_pos ht_le]
    exact measurable_const.sub
      ((measurable_of_countable
        (fun action : Fin K =>
          linearValue thetaStar (actionFeature action))).comp
        (measurable_fst.comp (measurable_pi_apply index)))
  have hcomp := hfinite.comp hprefix
  unfold canonicalStandardHighProbabilityPseudoRegret
    canonicalHistoryTrajectorySumRangeAllGap
  convert hcomp using 1
  funext trajectory
  apply Finset.sum_congr rfl
  intro t ht
  have ht_le : t <= horizon :=
    Nat.le_of_lt_succ (Finset.mem_range.mp ht)
  simp only [dif_pos ht_le, Thompson.canonicalHistoryTrajectoryAction,
    Preorder.frestrictLe]
  rfl

/--
The complete fixed-best pseudo-regret process is strongly adapted to the
canonical all-round trajectory filtration.
-/
theorem
    canonicalStandardHighProbabilityPseudoRegret_stronglyAdapted_allRound
    {K : Nat} {Feature : Type u}
    [Fintype Feature]
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (best : Fin K) :
    StronglyAdapted
      (canonicalHistoryTrajectoryAllRoundFiltration (K := K))
      (fun horizon trajectory =>
        canonicalStandardHighProbabilityPseudoRegret
          thetaStar actionFeature best horizon trajectory) := by
  intro horizon
  exact
    (measurable_canonicalStandardHighProbabilityPseudoRegret_allRound
      thetaStar actionFeature best horizon).stronglyMeasurable

/-- The deterministic explicit rate process is strongly adapted. -/
theorem
    telescopingHighProbabilityPseudoRegretBound_stronglyAdapted_allRound
    {K : Nat} {Feature : Type u}
    [Fintype Feature]
    (R delta lambda S L2 : Real) :
    StronglyAdapted
      (canonicalHistoryTrajectoryAllRoundFiltration (K := K))
      (fun horizon (_trajectory : Nat -> Fin K × Real) =>
        telescopingHighProbabilityPseudoRegretBound
          (Feature := Feature) R delta lambda S horizon L2) := by
  intro horizon
  exact stronglyMeasurable_const

/--
Violation of the explicit scheduled pseudo-regret rate after evaluating both
the deterministic budget and pseudo-regret process at a Mathlib stopped value.
-/
noncomputable def
    telescopingCanonicalExplicitHighProbabilityPseudoRegretStoppedViolationSet
    {K : Nat} {Feature : Type u}
    [Fintype Feature]
    (lambda : Real)
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S L2 : Real)
    (best : Fin K)
    (tau : (Nat -> Fin K × Real) -> WithTop Nat) :
    Set (Nat -> Fin K × Real) :=
  {trajectory |
    stoppedValue
        (fun horizon (_trajectory : Nat -> Fin K × Real) =>
          telescopingHighProbabilityPseudoRegretBound
            (Feature := Feature) R delta lambda S horizon L2)
        tau trajectory <
      stoppedValue
        (fun horizon trajectory =>
          canonicalStandardHighProbabilityPseudoRegret
            thetaStar actionFeature best horizon trajectory)
        tau trajectory}

/--
Every stopped-value violation is already an all-horizon violation, with the
same trajectory and witness horizon.
-/
theorem
    telescopingCanonicalExplicitHighProbabilityPseudoRegretStoppedViolationSet_subset_allHorizon
    {K : Nat} {Feature : Type u}
    [Fintype Feature]
    (lambda : Real)
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S L2 : Real)
    (best : Fin K)
    (tau : (Nat -> Fin K × Real) -> WithTop Nat) :
    telescopingCanonicalExplicitHighProbabilityPseudoRegretStoppedViolationSet
        lambda thetaStar actionFeature R delta S L2 best tau ⊆
      telescopingCanonicalExplicitHighProbabilityPseudoRegretAllHorizonViolationSet
        lambda thetaStar actionFeature R delta S L2 best := by
  intro trajectory htrajectory
  refine ⟨(tau trajectory).untopA, ?_⟩
  simpa only [
    telescopingCanonicalExplicitHighProbabilityPseudoRegretStoppedViolationSet,
    stoppedValue, Set.mem_setOf_eq] using htrajectory

/--
For a bounded stopping time, the stopped explicit violation event is
measurable at the deterministic bound.
-/
theorem
    measurableSet_telescopingCanonicalExplicitHighProbabilityPseudoRegretStoppedViolationSet_of_boundedStoppingTime
    {K : Nat} {Feature : Type u}
    [Fintype Feature]
    (lambda : Real)
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S L2 : Real)
    (best : Fin K)
    (tau : (Nat -> Fin K × Real) -> WithTop Nat)
    (htau : IsStoppingTime
      (canonicalHistoryTrajectoryAllRoundFiltration (K := K)) tau)
    (maxHorizon : Nat)
    (htau_le : forall trajectory,
      tau trajectory <= (maxHorizon : WithTop Nat)) :
    MeasurableSet[
      canonicalHistoryTrajectoryAllRoundFiltration (K := K) maxHorizon]
      (telescopingCanonicalExplicitHighProbabilityPseudoRegretStoppedViolationSet
        lambda thetaStar actionFeature R delta S L2 best tau) := by
  have hboundProgressive :
      ProgMeasurable
        (canonicalHistoryTrajectoryAllRoundFiltration (K := K))
        (fun horizon (_trajectory : Nat -> Fin K × Real) =>
          telescopingHighProbabilityPseudoRegretBound
            (Feature := Feature) R delta lambda S horizon L2) :=
    (telescopingHighProbabilityPseudoRegretBound_stronglyAdapted_allRound
      (K := K) (Feature := Feature) R delta lambda S L2).progMeasurable_of_discrete
  have hregretProgressive :
      ProgMeasurable
        (canonicalHistoryTrajectoryAllRoundFiltration (K := K))
        (fun horizon trajectory =>
          canonicalStandardHighProbabilityPseudoRegret
            thetaStar actionFeature best horizon trajectory) :=
    (canonicalStandardHighProbabilityPseudoRegret_stronglyAdapted_allRound
      thetaStar actionFeature best).progMeasurable_of_discrete
  have hboundStopped :
      StronglyMeasurable[
        canonicalHistoryTrajectoryAllRoundFiltration (K := K) maxHorizon]
        (stoppedValue
          (fun horizon (_trajectory : Nat -> Fin K × Real) =>
            telescopingHighProbabilityPseudoRegretBound
              (Feature := Feature) R delta lambda S horizon L2)
          tau) :=
    stronglyMeasurable_stoppedValue_of_le
      hboundProgressive htau htau_le
  have hregretStopped :
      StronglyMeasurable[
        canonicalHistoryTrajectoryAllRoundFiltration (K := K) maxHorizon]
        (stoppedValue
          (fun horizon trajectory =>
            canonicalStandardHighProbabilityPseudoRegret
              thetaStar actionFeature best horizon trajectory)
          tau) :=
    stronglyMeasurable_stoppedValue_of_le
      hregretProgressive htau htau_le
  exact measurableSet_lt hboundStopped.measurable hregretStopped.measurable

/--
The stopped-value violation event inherits the all-horizon `delta` tail. This
pathwise transport does not require the index to be a stopping time.
-/
theorem
    measure_telescopingCanonicalExplicitHighProbabilityPseudoRegretStoppedViolationSet_le_of_linearSubgaussianEnvironment_of_featureBound_le_regularization
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
      hK thetaStar actionFeature R S environment)
    (tau : (Nat -> Fin K × Real) -> WithTop Nat) :
    Thompson.canonicalHistoryTrajectoryMeasure
        (finiteHistoryTelescopingScalarRidgeOptimisticAlgorithm
          hK lambda actionFeature R delta S)
        environment
        (telescopingCanonicalExplicitHighProbabilityPseudoRegretStoppedViolationSet
          lambda thetaStar actionFeature R delta S L2 best tau) <=
      ENNReal.ofReal delta := by
  calc
    Thompson.canonicalHistoryTrajectoryMeasure
        (finiteHistoryTelescopingScalarRidgeOptimisticAlgorithm
          hK lambda actionFeature R delta S)
        environment
        (telescopingCanonicalExplicitHighProbabilityPseudoRegretStoppedViolationSet
          lambda thetaStar actionFeature R delta S L2 best tau) <=
      Thompson.canonicalHistoryTrajectoryMeasure
        (finiteHistoryTelescopingScalarRidgeOptimisticAlgorithm
          hK lambda actionFeature R delta S)
        environment
        (telescopingCanonicalExplicitHighProbabilityPseudoRegretAllHorizonViolationSet
          lambda thetaStar actionFeature R delta S L2 best) := by
      exact measure_mono
        (telescopingCanonicalExplicitHighProbabilityPseudoRegretStoppedViolationSet_subset_allHorizon
          lambda thetaStar actionFeature R delta S L2 best tau)
    _ <= ENNReal.ofReal delta :=
      (telescopingCanonicalStandardHighProbabilityPseudoRegret_nonneg_and_allHorizon_tail_le_explicitBound_of_linearSubgaussianEnvironment_of_featureBound_le_regularization
        hK lambda hlambda thetaStar actionFeature R hR
        delta hdelta hdelta_one S hS environment L2 hL2
        hactionFeatureBound hL2lambda best hbest source).2

/--
Complete bounded-stopping-time high-probability pseudo-regret theorem for the
single telescoping-schedule OFUL policy.
-/
theorem
    telescopingCanonicalStandardHighProbabilityPseudoRegret_nonneg_and_boundedStoppingTime_tail_le_explicitBound_of_linearSubgaussianEnvironment_of_featureBound_le_regularization
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
      hK thetaStar actionFeature R S environment)
    (tau : (Nat -> Fin K × Real) -> WithTop Nat)
    (htau : IsStoppingTime
      (canonicalHistoryTrajectoryAllRoundFiltration (K := K)) tau)
    (maxHorizon : Nat)
    (htau_le : forall trajectory,
      tau trajectory <= (maxHorizon : WithTop Nat)) :
    (forall trajectory,
      0 <= stoppedValue
        (fun horizon trajectory =>
          canonicalStandardHighProbabilityPseudoRegret
            thetaStar actionFeature best horizon trajectory)
        tau trajectory) /\
      MeasurableSet[
        canonicalHistoryTrajectoryAllRoundFiltration (K := K) maxHorizon]
        (telescopingCanonicalExplicitHighProbabilityPseudoRegretStoppedViolationSet
          lambda thetaStar actionFeature R delta S L2 best tau) /\
      Thompson.canonicalHistoryTrajectoryMeasure
          (finiteHistoryTelescopingScalarRidgeOptimisticAlgorithm
            hK lambda actionFeature R delta S)
          environment
          (telescopingCanonicalExplicitHighProbabilityPseudoRegretStoppedViolationSet
            lambda thetaStar actionFeature R delta S L2 best tau) <=
        ENNReal.ofReal delta := by
  have hmain :=
    telescopingCanonicalStandardHighProbabilityPseudoRegret_nonneg_and_allHorizon_tail_le_explicitBound_of_linearSubgaussianEnvironment_of_featureBound_le_regularization
      hK lambda hlambda thetaStar actionFeature R hR
      delta hdelta hdelta_one S hS environment L2 hL2
      hactionFeatureBound hL2lambda best hbest source
  constructor
  · intro trajectory
    exact hmain.1 (tau trajectory).untopA trajectory
  constructor
  · exact
      measurableSet_telescopingCanonicalExplicitHighProbabilityPseudoRegretStoppedViolationSet_of_boundedStoppingTime
        lambda thetaStar actionFeature R delta S L2 best
        tau htau maxHorizon htau_le
  · exact
      measure_telescopingCanonicalExplicitHighProbabilityPseudoRegretStoppedViolationSet_le_of_linearSubgaussianEnvironment_of_featureBound_le_regularization
        hK lambda hlambda thetaStar actionFeature R hR
        delta hdelta hdelta_one S hS environment L2 hL2
        hactionFeatureBound hL2lambda best hbest source tau

end OFUL
end BanditRLProof
