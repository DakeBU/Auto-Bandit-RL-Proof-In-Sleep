import BanditRLProof.OFULScheduledBoundedStoppingTimeExpectedRegret

/-!
# Unbounded stopping-time expected OFUL pseudo-regret decomposition

This module removes the deterministic stopping-horizon bound from the expected
pseudo-regret interface. It retains the exact bad-event random-envelope
integral: controlling that term by `delta` requires an additional moment or
tail contract and is not a consequence of first-moment stopping-time
integrability alone. This is an event decomposition, not optional stopping.
-/

namespace BanditRLProof
namespace OFUL

open MeasureTheory Real Matrix Set
open scoped ENNReal

universe u v

/--
Semantic finiteness and first-moment regularity for a `WithTop Nat` stopping
time. The a.e. finiteness field rules out interpreting `untopA` at `top`; the
integrability field controls the random all-round gap envelope.
-/
structure IntegrableFiniteStoppingTime
    {Omega : Type v} [MeasurableSpace Omega]
    (mu : Measure Omega) (tau : Omega -> WithTop Nat) : Prop where
  finite_ae : ∀ᵐ omega ∂mu, tau omega ≠ ⊤
  integrable_rounds :
    Integrable (fun omega => (((tau omega).untopA + 1 : Nat) : Real)) mu

/-- A stopped pseudo-regret obeys the gap envelope at its random horizon. -/
theorem
    abs_stoppedValue_canonicalStandardHighProbabilityPseudoRegret_le_randomHorizonEnvelope
    {K : Nat} {Feature : Type u}
    [Fintype Feature]
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (S : Real) (hS : 0 <= S)
    (L2 : Real)
    (hactionFeatureBound : forall action,
      dotProduct (actionFeature action) (actionFeature action) <= L2)
    (best : Fin K)
    (htheta : euclideanLength thetaStar <= S)
    (tau : (Nat -> Fin K × Real) -> WithTop Nat)
    (trajectory : Nat -> Fin K × Real) :
    |stoppedValue
        (fun horizon trajectory =>
          canonicalStandardHighProbabilityPseudoRegret
            thetaStar actionFeature best horizon trajectory)
        tau trajectory| <=
      standardScalarAllRoundGapEnvelope S (tau trajectory).untopA L2 := by
  simpa only [stoppedValue, canonicalStandardHighProbabilityPseudoRegret]
    using
      abs_canonicalHistoryTrajectorySumRangeAllGap_le_envelope
        thetaStar actionFeature S hS (tau trajectory).untopA L2
        hactionFeatureBound (fun _t => best) htheta trajectory

/-- A progressively measurable pseudo-regret process remains measurable at an arbitrary stopping time. -/
theorem
    measurable_stoppedValue_canonicalStandardHighProbabilityPseudoRegret_of_stoppingTime
    {K : Nat} {Feature : Type u}
    [Fintype Feature]
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (best : Fin K)
    (tau : (Nat -> Fin K × Real) -> WithTop Nat)
    (htau : IsStoppingTime
      (canonicalHistoryTrajectoryAllRoundFiltration (K := K)) tau) :
    Measurable
      (stoppedValue
        (fun horizon trajectory =>
          canonicalStandardHighProbabilityPseudoRegret
            thetaStar actionFeature best horizon trajectory)
        tau) := by
  exact
    (measurable_stoppedValue
      ((canonicalStandardHighProbabilityPseudoRegret_stronglyAdapted_allRound
        thetaStar actionFeature best).progMeasurable_of_discrete)
      htau).mono htau.measurableSpace_le le_rfl

/-- The explicit deterministic budget process remains measurable at an arbitrary stopping time. -/
theorem
    measurable_stoppedValue_telescopingHighProbabilityPseudoRegretBound_of_stoppingTime
    {K : Nat} {Feature : Type u}
    [Fintype Feature]
    (R delta lambda S L2 : Real)
    (tau : (Nat -> Fin K × Real) -> WithTop Nat)
    (htau : IsStoppingTime
      (canonicalHistoryTrajectoryAllRoundFiltration (K := K)) tau) :
    Measurable
      (stoppedValue
        (fun horizon (_trajectory : Nat -> Fin K × Real) =>
          telescopingHighProbabilityPseudoRegretBound
            (Feature := Feature) R delta lambda S horizon L2)
        tau) := by
  exact
    (measurable_stoppedValue
      ((telescopingHighProbabilityPseudoRegretBound_stronglyAdapted_allRound
        (K := K) (Feature := Feature) R delta lambda S L2).progMeasurable_of_discrete)
      htau).mono htau.measurableSpace_le le_rfl

/-- First-moment stopping-time regularity makes the random gap envelope integrable. -/
theorem integrable_standardScalarAllRoundGapEnvelope_at_stoppingTime
    {K : Nat}
    (mu : Measure (Nat -> Fin K × Real))
    (S L2 : Real)
    (tau : (Nat -> Fin K × Real) -> WithTop Nat)
    (hstop : IntegrableFiniteStoppingTime mu tau) :
    Integrable
      (fun trajectory =>
        standardScalarAllRoundGapEnvelope S (tau trajectory).untopA L2)
      mu := by
  simpa [standardScalarAllRoundGapEnvelope] using
    hstop.integrable_rounds.mul_const (standardScalarInitialGapBound S L2)

/--
The stopped pseudo-regret is integrable under first-moment stopping-time
regularity. No deterministic stopping-horizon bound is used.
-/
theorem
    integrable_stoppedValue_canonicalStandardHighProbabilityPseudoRegret_of_integrableFiniteStoppingTime
    {K : Nat} {Feature : Type u}
    [Fintype Feature]
    (mu : Measure (Nat -> Fin K × Real))
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (S : Real) (hS : 0 <= S)
    (L2 : Real)
    (hactionFeatureBound : forall action,
      dotProduct (actionFeature action) (actionFeature action) <= L2)
    (best : Fin K)
    (htheta : euclideanLength thetaStar <= S)
    (tau : (Nat -> Fin K × Real) -> WithTop Nat)
    (htau : IsStoppingTime
      (canonicalHistoryTrajectoryAllRoundFiltration (K := K)) tau)
    (hstop : IntegrableFiniteStoppingTime mu tau) :
    Integrable
      (stoppedValue
        (fun horizon trajectory =>
          canonicalStandardHighProbabilityPseudoRegret
            thetaStar actionFeature best horizon trajectory)
        tau) mu := by
  apply Integrable.mono'
    (integrable_standardScalarAllRoundGapEnvelope_at_stoppingTime
      mu S L2 tau hstop)
    (measurable_stoppedValue_canonicalStandardHighProbabilityPseudoRegret_of_stoppingTime
      thetaStar actionFeature best tau htau).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun trajectory => by
    simpa [Real.norm_eq_abs] using
      abs_stoppedValue_canonicalStandardHighProbabilityPseudoRegret_le_randomHorizonEnvelope
        thetaStar actionFeature S hS L2 hactionFeatureBound best htheta
        tau trajectory

/-- The stopped explicit violation event is measurable without a deterministic stopping bound. -/
theorem
    measurableSet_telescopingCanonicalExplicitHighProbabilityPseudoRegretStoppedViolationSet_of_stoppingTime
    {K : Nat} {Feature : Type u}
    [Fintype Feature]
    (lambda : Real)
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S L2 : Real)
    (best : Fin K)
    (tau : (Nat -> Fin K × Real) -> WithTop Nat)
    (htau : IsStoppingTime
      (canonicalHistoryTrajectoryAllRoundFiltration (K := K)) tau) :
    MeasurableSet
      (telescopingCanonicalExplicitHighProbabilityPseudoRegretStoppedViolationSet
        lambda thetaStar actionFeature R delta S L2 best tau) := by
  exact measurableSet_lt
    (measurable_stoppedValue_telescopingHighProbabilityPseudoRegretBound_of_stoppingTime
      (K := K) (Feature := Feature) R delta lambda S L2 tau htau)
    (measurable_stoppedValue_canonicalStandardHighProbabilityPseudoRegret_of_stoppingTime
      thetaStar actionFeature best tau htau)

/--
Exact unbounded-stopping expectation decomposition. The bad-event term remains
an integral of the random horizon envelope.
-/
theorem
    integral_stoppedValue_canonicalStandardHighProbabilityPseudoRegret_le_integral_stoppedBudget_add_integral_badIndicator_randomHorizonEnvelope
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [Nonempty Feature]
    (mu : Measure (Nat -> Fin K × Real))
    (lambda : Real) (hlambda : 0 < lambda)
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R : Real) (hR : 0 <= R)
    (delta : Real) (hdelta : 0 < delta) (hdelta_one : delta <= 1)
    (S : Real) (hS : 0 <= S)
    (L2 : Real) (hL2 : 0 <= L2)
    (hactionFeatureBound : forall action,
      dotProduct (actionFeature action) (actionFeature action) <= L2)
    (best : Fin K)
    (htheta : euclideanLength thetaStar <= S)
    (tau : (Nat -> Fin K × Real) -> WithTop Nat)
    (htau : IsStoppingTime
      (canonicalHistoryTrajectoryAllRoundFiltration (K := K)) tau)
    (hstop : IntegrableFiniteStoppingTime mu tau)
    (hbudgetIntegrable :
      Integrable
        (stoppedValue
          (fun horizon (_trajectory : Nat -> Fin K × Real) =>
            telescopingHighProbabilityPseudoRegretBound
              (Feature := Feature) R delta lambda S horizon L2)
          tau) mu) :
    integral mu
        (stoppedValue
          (fun horizon trajectory =>
            canonicalStandardHighProbabilityPseudoRegret
              thetaStar actionFeature best horizon trajectory)
          tau) <=
      integral mu
          (stoppedValue
            (fun horizon (_trajectory : Nat -> Fin K × Real) =>
              telescopingHighProbabilityPseudoRegretBound
                (Feature := Feature) R delta lambda S horizon L2)
            tau) +
        integral mu
          ((telescopingCanonicalExplicitHighProbabilityPseudoRegretStoppedViolationSet
              lambda thetaStar actionFeature R delta S L2 best tau).indicator
            (fun trajectory =>
              standardScalarAllRoundGapEnvelope
                S (tau trajectory).untopA L2)) := by
  let gap :=
    stoppedValue
      (fun horizon trajectory =>
        canonicalStandardHighProbabilityPseudoRegret
          thetaStar actionFeature best horizon trajectory)
      tau
  let budget :=
    stoppedValue
      (fun horizon (_trajectory : Nat -> Fin K × Real) =>
        telescopingHighProbabilityPseudoRegretBound
          (Feature := Feature) R delta lambda S horizon L2)
      tau
  let envelope := fun trajectory =>
    standardScalarAllRoundGapEnvelope S (tau trajectory).untopA L2
  let bad :=
    telescopingCanonicalExplicitHighProbabilityPseudoRegretStoppedViolationSet
      lambda thetaStar actionFeature R delta S L2 best tau
  let overflow := bad.indicator envelope
  have hbad : MeasurableSet bad := by
    exact
      measurableSet_telescopingCanonicalExplicitHighProbabilityPseudoRegretStoppedViolationSet_of_stoppingTime
        lambda thetaStar actionFeature R delta S L2 best tau htau
  have hgap : Integrable gap mu := by
    exact
      integrable_stoppedValue_canonicalStandardHighProbabilityPseudoRegret_of_integrableFiniteStoppingTime
        mu thetaStar actionFeature S hS L2 hactionFeatureBound best htheta
        tau htau hstop
  have henvelope : Integrable envelope mu := by
    exact integrable_standardScalarAllRoundGapEnvelope_at_stoppingTime
      mu S L2 tau hstop
  have hoverflow : Integrable overflow mu := henvelope.indicator hbad
  have hpoint : forall trajectory, gap trajectory <=
      budget trajectory + overflow trajectory := by
    intro trajectory
    by_cases htrajectory : trajectory ∈ bad
    · have hgapEnvelope : gap trajectory <= envelope trajectory := by
        exact (le_abs_self _).trans
          (abs_stoppedValue_canonicalStandardHighProbabilityPseudoRegret_le_randomHorizonEnvelope
            thetaStar actionFeature S hS L2 hactionFeatureBound best htheta
            tau trajectory)
      have hbudgetNonneg : 0 <= budget trajectory := by
        simpa only [budget, stoppedValue] using
          (telescopingHighProbabilityPseudoRegretBound_nonneg
            (Feature := Feature) R hR delta hdelta hdelta_one
            lambda hlambda S hS (tau trajectory).untopA L2 hL2)
      calc
        gap trajectory <= envelope trajectory := hgapEnvelope
        _ <= budget trajectory + envelope trajectory :=
          le_add_of_nonneg_left hbudgetNonneg
        _ = budget trajectory + overflow trajectory := by
          rw [show overflow trajectory = envelope trajectory by
            exact Set.indicator_of_mem htrajectory envelope]
    · have hgapBudget : gap trajectory <= budget trajectory := by
        apply le_of_not_gt
        simpa [bad, gap, budget,
          telescopingCanonicalExplicitHighProbabilityPseudoRegretStoppedViolationSet]
          using htrajectory
      calc
        gap trajectory <= budget trajectory := hgapBudget
        _ = budget trajectory + overflow trajectory := by
          rw [show overflow trajectory = 0 by
            exact Set.indicator_of_notMem htrajectory envelope]
          simp
  calc
    integral mu gap <=
        integral mu (fun trajectory =>
          budget trajectory + overflow trajectory) :=
      integral_mono hgap (hbudgetIntegrable.add hoverflow) hpoint
    _ = integral mu budget + integral mu overflow := by
      rw [integral_add hbudgetIntegrable hoverflow]

/--
Canonical generated-trajectory unbounded-stopping theorem. The same stopped
violation event has the compiled `delta` tail, while its random-envelope
overflow remains explicit in the expectation bound.
-/
theorem
    integral_stoppedValue_canonicalStandardHighProbabilityPseudoRegret_nonneg_and_le_integral_stoppedBudget_add_integral_badIndicator_randomHorizonEnvelope_and_stoppedViolation_measure_le_of_linearSubgaussianEnvironment_of_featureBound_le_regularization
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
    (hstop : IntegrableFiniteStoppingTime
      (Thompson.canonicalHistoryTrajectoryMeasure
        (finiteHistoryTelescopingScalarRidgeOptimisticAlgorithm
          hK lambda actionFeature R delta S)
        environment)
      tau)
    (hbudgetIntegrable :
      Integrable
        (stoppedValue
          (fun horizon (_trajectory : Nat -> Fin K × Real) =>
            telescopingHighProbabilityPseudoRegretBound
              (Feature := Feature) R delta lambda S horizon L2)
          tau)
        (Thompson.canonicalHistoryTrajectoryMeasure
          (finiteHistoryTelescopingScalarRidgeOptimisticAlgorithm
            hK lambda actionFeature R delta S)
          environment)) :
    let mu :=
      Thompson.canonicalHistoryTrajectoryMeasure
        (finiteHistoryTelescopingScalarRidgeOptimisticAlgorithm
          hK lambda actionFeature R delta S)
        environment
    let stoppedRegret :=
      stoppedValue
        (fun horizon trajectory =>
          canonicalStandardHighProbabilityPseudoRegret
            thetaStar actionFeature best horizon trajectory)
        tau
    let stoppedBudget :=
      stoppedValue
        (fun horizon (_trajectory : Nat -> Fin K × Real) =>
          telescopingHighProbabilityPseudoRegretBound
            (Feature := Feature) R delta lambda S horizon L2)
        tau
    let bad :=
      telescopingCanonicalExplicitHighProbabilityPseudoRegretStoppedViolationSet
        lambda thetaStar actionFeature R delta S L2 best tau
    let overflow :=
      bad.indicator
        (fun trajectory =>
          standardScalarAllRoundGapEnvelope S (tau trajectory).untopA L2)
    0 <= integral mu stoppedRegret /\
      integral mu stoppedRegret <=
        integral mu stoppedBudget + integral mu overflow /\
      mu bad <= ENNReal.ofReal delta := by
  dsimp only
  constructor
  · exact integral_nonneg fun trajectory => by
      simp only [stoppedValue, canonicalStandardHighProbabilityPseudoRegret]
      exact
        canonicalHistoryTrajectorySumRangeAllFixedComparatorGap_nonneg
          thetaStar actionFeature (tau trajectory).untopA best hbest trajectory
  constructor
  · exact
      integral_stoppedValue_canonicalStandardHighProbabilityPseudoRegret_le_integral_stoppedBudget_add_integral_badIndicator_randomHorizonEnvelope
        (Thompson.canonicalHistoryTrajectoryMeasure
          (finiteHistoryTelescopingScalarRidgeOptimisticAlgorithm
            hK lambda actionFeature R delta S)
          environment)
        lambda hlambda thetaStar actionFeature R hR.le delta hdelta hdelta_one
        S hS L2 hL2 hactionFeatureBound best source.theta_norm_le
        tau htau hstop hbudgetIntegrable
  · exact
      measure_telescopingCanonicalExplicitHighProbabilityPseudoRegretStoppedViolationSet_le_of_linearSubgaussianEnvironment_of_featureBound_le_regularization
        hK lambda hlambda thetaStar actionFeature R hR
        delta hdelta hdelta_one S hS environment L2 hL2
        hactionFeatureBound hL2lambda best hbest source tau

end OFUL
end BanditRLProof
