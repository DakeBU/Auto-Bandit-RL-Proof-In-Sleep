import BanditRLProof.OFULScheduledUnboundedStoppingTimeExpectedRegret

/-!
# Square-integrable unbounded stopping-time expected OFUL pseudo-regret rate

This module controls the random bad-event overflow from the exact unbounded
stopping-time decomposition by an `L2` Cauchy-Schwarz bound. It yields a valid
`sqrt delta` overflow rate from the compiled stopped-event tail. This remains
an event decomposition and does not invoke optional stopping.
-/

namespace BanditRLProof
namespace OFUL

open MeasureTheory Real Matrix Set
open scoped ENNReal

universe u v

/--
Semantic finiteness and second-moment regularity for a `WithTop Nat` stopping
time. Under a finite measure this contract implies
`IntegrableFiniteStoppingTime`.
-/
structure SquareIntegrableFiniteStoppingTime
    {Omega : Type v} [MeasurableSpace Omega]
    (mu : Measure Omega) (tau : Omega -> WithTop Nat) : Prop where
  finite_ae : ∀ᵐ omega ∂mu, tau omega ≠ ⊤
  memLp_rounds :
    MemLp (fun omega => (((tau omega).untopA + 1 : Nat) : Real)) 2 mu

/-- An `L2` finite stopping-time contract supplies the earlier `L1` contract. -/
theorem SquareIntegrableFiniteStoppingTime.toIntegrableFiniteStoppingTime
    {Omega : Type v} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (tau : Omega -> WithTop Nat)
    (hstop : SquareIntegrableFiniteStoppingTime mu tau) :
    IntegrableFiniteStoppingTime mu tau := by
  refine ⟨hstop.finite_ae, ?_⟩
  exact hstop.memLp_rounds.integrable (by norm_num)

/--
Project-local `L2` indicator bound. This is the nonnegative `2,2` Holder
specialization needed by the random-horizon overflow consumer.
-/
theorem integral_indicator_le_sqrt_secondMoment_mul_sqrt_real_measure
    {Omega : Type v} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (f : Omega -> Real)
    (hf_nonneg : forall omega, 0 <= f omega)
    (hf : MemLp f 2 mu)
    (bad : Set Omega) (hbad : MeasurableSet bad) :
    integral mu (bad.indicator f) <=
      Real.sqrt (integral mu (fun omega => f omega ^ 2)) *
        Real.sqrt (mu.real bad) := by
  let indicatorOne : Omega -> Real := bad.indicator (fun _ => 1)
  have hpq : (2 : Real).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hindicatorOne_nonneg : forall omega, 0 <= indicatorOne omega := by
    intro omega
    by_cases homega : omega ∈ bad <;> simp [indicatorOne, homega]
  have hindicatorOne : MemLp indicatorOne 2 mu := by
    exact memLp_indicator_const 2 hbad 1
      (Or.inr (measure_lt_top mu bad).ne)
  have hf_realTwo : MemLp f (ENNReal.ofReal (2 : Real)) mu := by
    norm_num
    exact hf
  have hindicatorOne_realTwo :
      MemLp indicatorOne (ENNReal.ofReal (2 : Real)) mu := by
    norm_num
    exact hindicatorOne
  have hholder :=
    integral_mul_le_Lp_mul_Lq_of_nonneg hpq
      (Filter.Eventually.of_forall hf_nonneg)
      (Filter.Eventually.of_forall hindicatorOne_nonneg)
      hf_realTwo hindicatorOne_realTwo
  have hmul :
      (fun omega => f omega * indicatorOne omega) = bad.indicator f := by
    funext omega
    by_cases homega : omega ∈ bad <;> simp [indicatorOne, homega]
  have hpow :
      (fun omega => indicatorOne omega ^ (2 : Real)) =
        bad.indicator (fun _ => (1 : Real)) := by
    funext omega
    by_cases homega : omega ∈ bad <;> simp [indicatorOne, homega]
  have hintegralIndicatorOne :
      integral mu (bad.indicator (fun _ => (1 : Real))) = mu.real bad := by
    simpa using (integral_indicator_one (μ := mu) hbad)
  rw [hmul, hpow, hintegralIndicatorOne] at hholder
  simp_rw [Real.rpow_two] at hholder
  simpa only [← Real.sqrt_eq_rpow] using hholder

/--
The bad-event random-horizon gap envelope is controlled by the stopping-time
second moment and the square root of the event probability.
-/
theorem
    integral_badIndicator_standardScalarAllRoundGapEnvelope_at_stoppingTime_le
    {K : Nat}
    (mu : Measure (Nat -> Fin K × Real)) [IsFiniteMeasure mu]
    (S : Real) (hS : 0 <= S)
    (L2 : Real)
    (tau : (Nat -> Fin K × Real) -> WithTop Nat)
    (hstop : SquareIntegrableFiniteStoppingTime mu tau)
    (roundSecondMoment : Real)
    (hroundSecondMoment :
      integral mu
        (fun trajectory =>
          ((((tau trajectory).untopA + 1 : Nat) : Real)) ^ 2) <=
        roundSecondMoment)
    (bad : Set (Nat -> Fin K × Real)) (hbad : MeasurableSet bad) :
    integral mu
        (bad.indicator
          (fun trajectory =>
            standardScalarAllRoundGapEnvelope
              S (tau trajectory).untopA L2)) <=
      standardScalarInitialGapBound S L2 *
        Real.sqrt roundSecondMoment *
          Real.sqrt (mu.real bad) := by
  let rounds : (Nat -> Fin K × Real) -> Real := fun trajectory =>
    (((tau trajectory).untopA + 1 : Nat) : Real)
  let initialGap := standardScalarInitialGapBound S L2
  have hrounds_nonneg : forall trajectory, 0 <= rounds trajectory := by
    intro trajectory
    exact Nat.cast_nonneg _
  have hinitialGap_nonneg : 0 <= initialGap := by
    dsimp only [initialGap, standardScalarInitialGapBound]
    positivity
  have hrestricted :=
    integral_indicator_le_sqrt_secondMoment_mul_sqrt_real_measure
      mu rounds hrounds_nonneg hstop.memLp_rounds bad hbad
  have hsqrtMoment :
      Real.sqrt
          (integral mu (fun trajectory => rounds trajectory ^ 2)) <=
        Real.sqrt roundSecondMoment := by
    apply Real.sqrt_le_sqrt
    simpa only [rounds] using hroundSecondMoment
  have hoverflow :
      (bad.indicator
          (fun trajectory =>
            standardScalarAllRoundGapEnvelope
              S (tau trajectory).untopA L2)) =
        fun trajectory => bad.indicator rounds trajectory * initialGap := by
    funext trajectory
    by_cases htrajectory : trajectory ∈ bad <;>
      simp [rounds, initialGap, standardScalarAllRoundGapEnvelope, htrajectory]
  rw [hoverflow, integral_mul_const]
  calc
    integral mu (bad.indicator rounds) * initialGap <=
        (Real.sqrt
            (integral mu (fun trajectory => rounds trajectory ^ 2)) *
          Real.sqrt (mu.real bad)) * initialGap := by
      exact mul_le_mul_of_nonneg_right hrestricted hinitialGap_nonneg
    _ <=
        (Real.sqrt roundSecondMoment * Real.sqrt (mu.real bad)) *
          initialGap := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hsqrtMoment
          (Real.sqrt_nonneg (mu.real bad)))
        hinitialGap_nonneg
    _ =
        standardScalarInitialGapBound S L2 *
          Real.sqrt roundSecondMoment *
            Real.sqrt (mu.real bad) := by
      simp only [initialGap]
      ring

/--
Canonical generated-trajectory unbounded-stopping expected pseudo-regret rate
under a round-count second-moment bound. The `sqrt delta` term comes from the
compiled stopped-event tail and the `L2` indicator inequality above.
-/
theorem
    integral_stoppedValue_canonicalStandardHighProbabilityPseudoRegret_nonneg_and_le_integral_stoppedBudget_add_initialGap_mul_sqrt_roundSecondMoment_mul_sqrt_delta_and_stoppedViolation_measure_le_of_linearSubgaussianEnvironment_of_featureBound_le_regularization
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
    (hstop : SquareIntegrableFiniteStoppingTime
      (Thompson.canonicalHistoryTrajectoryMeasure
        (finiteHistoryTelescopingScalarRidgeOptimisticAlgorithm
          hK lambda actionFeature R delta S)
        environment)
      tau)
    (roundSecondMoment : Real)
    (hroundSecondMoment :
      integral
        (Thompson.canonicalHistoryTrajectoryMeasure
          (finiteHistoryTelescopingScalarRidgeOptimisticAlgorithm
            hK lambda actionFeature R delta S)
          environment)
        (fun trajectory =>
          ((((tau trajectory).untopA + 1 : Nat) : Real)) ^ 2) <=
        roundSecondMoment)
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
    0 <= integral mu stoppedRegret ∧
      integral mu stoppedRegret <=
        integral mu stoppedBudget +
          standardScalarInitialGapBound S L2 *
            Real.sqrt roundSecondMoment * Real.sqrt delta ∧
      mu bad <= ENNReal.ofReal delta := by
  dsimp only
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
  have htail : mu bad <= ENNReal.ofReal delta := by
    exact
      measure_telescopingCanonicalExplicitHighProbabilityPseudoRegretStoppedViolationSet_le_of_linearSubgaussianEnvironment_of_featureBound_le_regularization
        hK lambda hlambda thetaStar actionFeature R hR
        delta hdelta hdelta_one S hS environment L2 hL2
        hactionFeatureBound hL2lambda best hbest source tau
  have htailReal : mu.real bad <= delta := by
    apply ENNReal.toReal_le_of_le_ofReal hdelta.le
    exact htail
  have hbad : MeasurableSet bad := by
    exact
      measurableSet_telescopingCanonicalExplicitHighProbabilityPseudoRegretStoppedViolationSet_of_stoppingTime
        lambda thetaStar actionFeature R delta S L2 best tau htau
  have hstopIntegrable : IntegrableFiniteStoppingTime mu tau := by
    exact hstop.toIntegrableFiniteStoppingTime mu tau
  have hdecomposition :
      integral mu stoppedRegret <=
        integral mu stoppedBudget + integral mu overflow := by
    exact
      integral_stoppedValue_canonicalStandardHighProbabilityPseudoRegret_le_integral_stoppedBudget_add_integral_badIndicator_randomHorizonEnvelope
        mu lambda hlambda thetaStar actionFeature R hR.le
        delta hdelta hdelta_one S hS L2 hL2 hactionFeatureBound
        best source.theta_norm_le tau htau hstopIntegrable hbudgetIntegrable
  have hoverflow :
      integral mu overflow <=
        standardScalarInitialGapBound S L2 *
          Real.sqrt roundSecondMoment * Real.sqrt (mu.real bad) := by
    exact
      integral_badIndicator_standardScalarAllRoundGapEnvelope_at_stoppingTime_le
        mu S hS L2 tau hstop roundSecondMoment hroundSecondMoment bad hbad
  have hinitialGap_nonneg :
      0 <= standardScalarInitialGapBound S L2 := by
    unfold standardScalarInitialGapBound
    positivity
  have hoverflowDelta :
      integral mu overflow <=
        standardScalarInitialGapBound S L2 *
          Real.sqrt roundSecondMoment * Real.sqrt delta := by
    calc
      integral mu overflow <=
          standardScalarInitialGapBound S L2 *
            Real.sqrt roundSecondMoment * Real.sqrt (mu.real bad) := hoverflow
      _ <=
          standardScalarInitialGapBound S L2 *
            Real.sqrt roundSecondMoment * Real.sqrt delta := by
        exact mul_le_mul_of_nonneg_left
          (Real.sqrt_le_sqrt htailReal)
          (mul_nonneg hinitialGap_nonneg
            (Real.sqrt_nonneg roundSecondMoment))
  constructor
  · exact integral_nonneg fun trajectory => by
      simp only [stoppedValue, canonicalStandardHighProbabilityPseudoRegret]
      exact
        canonicalHistoryTrajectorySumRangeAllFixedComparatorGap_nonneg
          thetaStar actionFeature (tau trajectory).untopA best hbest trajectory
  constructor
  · exact hdecomposition.trans
      (add_le_add_right hoverflowDelta (integral mu stoppedBudget))
  · exact htail

end OFUL
end BanditRLProof
