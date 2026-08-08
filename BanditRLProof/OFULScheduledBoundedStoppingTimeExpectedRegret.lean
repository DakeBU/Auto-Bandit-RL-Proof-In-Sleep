import BanditRLProof.OFULExpectedRegret
import BanditRLProof.OFULScheduledBoundedStoppingTimeHighProbabilityRegretRate

/-!
# Bounded stopping-time expected OFUL pseudo-regret rate

This module integrates the compiled bounded-stopping-time high-probability
pseudo-regret theorem. Horizon monotonicity moves both the explicit scheduled
budget and the deterministic gap envelope to the deterministic stopping-time
bound. The expectation proof is an indicator decomposition, not optional
stopping.
-/

namespace BanditRLProof
namespace OFUL

open MeasureTheory Real Matrix Set
open scoped ENNReal

universe u

/-- The explicit telescoping confidence logarithm is nonnegative. -/
theorem telescopingHighProbabilityRegretLogBudget_nonneg
    {Feature : Type u} [Fintype Feature] [Nonempty Feature]
    (lambda : Real) (hlambda : 0 < lambda)
    (delta : Real) (hdelta : 0 < delta) (hdelta_one : delta <= 1)
    (horizon : Nat) (L2 : Real) (hL2 : 0 <= L2) :
    0 <= telescopingHighProbabilityRegretLogBudget
      (Feature := Feature) lambda delta horizon L2 := by
  have hdet :
      0 <= standardScalarLogDetBudget
        (Feature := Feature) lambda (horizon + 1) L2 :=
    standardScalarLogDetBudget_nonneg
      (Feature := Feature) lambda hlambda (horizon + 1) L2 hL2
  have hprod_one :
      (1 : Real) <=
        (((horizon + 1 : Nat) : Real) *
          ((horizon + 2 : Nat) : Real)) := by
    have hfirst :
        (1 : Real) <= (((horizon + 1 : Nat) : Real)) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le horizon)
    have hsecond :
        (1 : Real) <= (((horizon + 2 : Nat) : Real)) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le (horizon + 1))
    simpa using
      (mul_le_mul hfirst hsecond (by norm_num : (0 : Real) <= 1)
        (by positivity : (0 : Real) <= (((horizon + 1 : Nat) : Real))))
  have hratio_one :
      (1 : Real) <=
        ((((horizon + 1 : Nat) : Real) *
            ((horizon + 2 : Nat) : Real)) / delta) := by
    rw [le_div_iff₀ hdelta]
    simpa using hdelta_one.trans hprod_one
  unfold telescopingHighProbabilityRegretLogBudget
  exact add_nonneg hdet
    (mul_nonneg (by norm_num) (Real.log_nonneg hratio_one))

/-- The explicit telescoping confidence logarithm is monotone in the horizon. -/
theorem telescopingHighProbabilityRegretLogBudget_mono
    {Feature : Type u} [Fintype Feature] [Nonempty Feature]
    (lambda : Real) (hlambda : 0 < lambda)
    (delta : Real) (hdelta : 0 < delta)
    (L2 : Real) (hL2 : 0 <= L2)
    {n horizon : Nat} (hn : n <= horizon) :
    telescopingHighProbabilityRegretLogBudget
        (Feature := Feature) lambda delta n L2 <=
      telescopingHighProbabilityRegretLogBudget
        (Feature := Feature) lambda delta horizon L2 := by
  have hdet :
      standardScalarLogDetBudget
          (Feature := Feature) lambda (n + 1) L2 <=
        standardScalarLogDetBudget
          (Feature := Feature) lambda (horizon + 1) L2 :=
    standardScalarLogDetBudget_mono
      (Feature := Feature) lambda hlambda L2 hL2
      (Nat.add_le_add_right hn 1)
  have hfirst :
      (((n + 1 : Nat) : Real)) <=
        (((horizon + 1 : Nat) : Real)) := by
    exact_mod_cast Nat.add_le_add_right hn 1
  have hsecond :
      (((n + 2 : Nat) : Real)) <=
        (((horizon + 2 : Nat) : Real)) := by
    exact_mod_cast Nat.add_le_add_right hn 2
  have hprod :
      (((n + 1 : Nat) : Real) * ((n + 2 : Nat) : Real)) <=
        (((horizon + 1 : Nat) : Real) *
          ((horizon + 2 : Nat) : Real)) :=
    mul_le_mul hfirst hsecond (by positivity) (by positivity)
  have hratio :
      ((((n + 1 : Nat) : Real) * ((n + 2 : Nat) : Real)) / delta) <=
        ((((horizon + 1 : Nat) : Real) *
            ((horizon + 2 : Nat) : Real)) / delta) :=
    (div_le_div_iff_of_pos_right hdelta).2 hprod
  have hratio_pos :
      0 <
        ((((n + 1 : Nat) : Real) * ((n + 2 : Nat) : Real)) / delta) :=
    div_pos (mul_pos (by positivity) (by positivity)) hdelta
  have hlog :
      Real.log
          ((((n + 1 : Nat) : Real) * ((n + 2 : Nat) : Real)) / delta) <=
        Real.log
          ((((horizon + 1 : Nat) : Real) *
              ((horizon + 2 : Nat) : Real)) / delta) :=
    Real.log_le_log hratio_pos hratio
  unfold telescopingHighProbabilityRegretLogBudget
  exact add_le_add hdet (mul_le_mul_of_nonneg_left hlog (by norm_num))

/-- The explicit telescoping pseudo-regret budget is nonnegative. -/
theorem telescopingHighProbabilityPseudoRegretBound_nonneg
    {Feature : Type u} [Fintype Feature] [Nonempty Feature]
    (R : Real) (hR : 0 <= R)
    (delta : Real) (hdelta : 0 < delta) (hdelta_one : delta <= 1)
    (lambda : Real) (hlambda : 0 < lambda)
    (S : Real) (hS : 0 <= S)
    (horizon : Nat) (L2 : Real) (hL2 : 0 <= L2) :
    0 <= telescopingHighProbabilityPseudoRegretBound
      (Feature := Feature) R delta lambda S horizon L2 := by
  have hlog :=
    telescopingHighProbabilityRegretLogBudget_nonneg
      (Feature := Feature) lambda hlambda delta hdelta hdelta_one
      horizon L2 hL2
  unfold telescopingHighProbabilityPseudoRegretBound
  positivity

/-- The explicit telescoping pseudo-regret budget is monotone in the horizon. -/
theorem telescopingHighProbabilityPseudoRegretBound_mono
    {Feature : Type u} [Fintype Feature] [Nonempty Feature]
    (R : Real) (hR : 0 <= R)
    (delta : Real) (hdelta : 0 < delta) (hdelta_one : delta <= 1)
    (lambda : Real) (hlambda : 0 < lambda)
    (S : Real) (hS : 0 <= S)
    (L2 : Real) (hL2 : 0 <= L2)
    {n horizon : Nat} (hn : n <= horizon) :
    telescopingHighProbabilityPseudoRegretBound
        (Feature := Feature) R delta lambda S n L2 <=
      telescopingHighProbabilityPseudoRegretBound
        (Feature := Feature) R delta lambda S horizon L2 := by
  let logN :=
    telescopingHighProbabilityRegretLogBudget
      (Feature := Feature) lambda delta n L2
  let logT :=
    telescopingHighProbabilityRegretLogBudget
      (Feature := Feature) lambda delta horizon L2
  let detN :=
    standardScalarLogDetBudget (Feature := Feature) lambda (n + 1) L2
  let detT :=
    standardScalarLogDetBudget
      (Feature := Feature) lambda (horizon + 1) L2
  have hlog : logN <= logT := by
    exact telescopingHighProbabilityRegretLogBudget_mono
      (Feature := Feature) lambda hlambda delta hdelta L2 hL2 hn
  have hlogN : 0 <= logN := by
    exact telescopingHighProbabilityRegretLogBudget_nonneg
      (Feature := Feature) lambda hlambda delta hdelta hdelta_one n L2 hL2
  have hlogT : 0 <= logT := hlogN.trans hlog
  have hdet : detN <= detT := by
    exact standardScalarLogDetBudget_mono
      (Feature := Feature) lambda hlambda L2 hL2
      (Nat.add_le_add_right hn 1)
  have hdetN : 0 <= detN := by
    exact standardScalarLogDetBudget_nonneg
      (Feature := Feature) lambda hlambda (n + 1) L2 hL2
  have hdetT : 0 <= detT := hdetN.trans hdet
  have hradius :
      R * Real.sqrt logN + Real.sqrt lambda * S <=
        R * Real.sqrt logT + Real.sqrt lambda * S := by
    exact add_le_add
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hlog) hR) le_rfl
  have hradiusN :
      0 <= R * Real.sqrt logN + Real.sqrt lambda * S := by
    positivity
  have hradiusT :
      0 <= R * Real.sqrt logT + Real.sqrt lambda * S := by
    positivity
  have htime :
      Real.sqrt (((n + 1 : Nat) : Real)) <=
        Real.sqrt (((horizon + 1 : Nat) : Real)) := by
    apply Real.sqrt_le_sqrt
    exact_mod_cast Nat.add_le_add_right hn 1
  have hwidthLog :
      Real.sqrt (2 * detN) <= Real.sqrt (2 * detT) := by
    exact Real.sqrt_le_sqrt
      (mul_le_mul_of_nonneg_left hdet (by norm_num))
  have hwidth :
      Real.sqrt (((n + 1 : Nat) : Real)) * Real.sqrt (2 * detN) <=
        Real.sqrt (((horizon + 1 : Nat) : Real)) *
          Real.sqrt (2 * detT) := by
    exact mul_le_mul htime hwidthLog
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hproduct :
      (R * Real.sqrt logN + Real.sqrt lambda * S) *
          (Real.sqrt (((n + 1 : Nat) : Real)) * Real.sqrt (2 * detN)) <=
        (R * Real.sqrt logT + Real.sqrt lambda * S) *
          (Real.sqrt (((horizon + 1 : Nat) : Real)) *
            Real.sqrt (2 * detT)) :=
    mul_le_mul hradius hwidth
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hradiusT
  unfold telescopingHighProbabilityPseudoRegretBound
  simpa [logN, logT, detN, detT, mul_assoc] using
    (add_le_add_left
      (mul_le_mul_of_nonneg_left hproduct (by norm_num : (0 : Real) <= 2))
      (2 * S * Real.sqrt L2))

/-- The deterministic all-round gap envelope is monotone in the horizon. -/
theorem standardScalarAllRoundGapEnvelope_mono
    (S : Real) (hS : 0 <= S) (L2 : Real)
    {n horizon : Nat} (hn : n <= horizon) :
    standardScalarAllRoundGapEnvelope S n L2 <=
      standardScalarAllRoundGapEnvelope S horizon L2 := by
  have hrounds :
      (((n + 1 : Nat) : Real)) <=
        (((horizon + 1 : Nat) : Real)) := by
    exact_mod_cast Nat.add_le_add_right hn 1
  have hinitial : 0 <= standardScalarInitialGapBound S L2 := by
    unfold standardScalarInitialGapBound
    positivity
  unfold standardScalarAllRoundGapEnvelope
  exact mul_le_mul_of_nonneg_right hrounds hinitial

/-- A bounded stopped pseudo-regret obeys the endpoint gap envelope. -/
theorem
    abs_stoppedValue_canonicalStandardHighProbabilityPseudoRegret_le_envelope
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
    (maxHorizon : Nat)
    (htau_le : forall trajectory,
      tau trajectory <= (maxHorizon : WithTop Nat))
    (trajectory : Nat -> Fin K × Real) :
    |stoppedValue
        (fun horizon trajectory =>
          canonicalStandardHighProbabilityPseudoRegret
            thetaStar actionFeature best horizon trajectory)
        tau trajectory| <=
      standardScalarAllRoundGapEnvelope S maxHorizon L2 := by
  have htau_nat : (tau trajectory).untopA <= maxHorizon := by
    have hcoe :
        ((tau trajectory).untopA : WithTop Nat) <=
          (maxHorizon : WithTop Nat) := by
      rw [coe_untopA_boundedTrajectoryTime tau maxHorizon htau_le trajectory]
      exact htau_le trajectory
    exact_mod_cast hcoe
  calc
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
    _ <= standardScalarAllRoundGapEnvelope S maxHorizon L2 :=
      standardScalarAllRoundGapEnvelope_mono S hS L2 htau_nat

/-- A bounded stopped pseudo-regret is integrable under a finite measure. -/
theorem
    integrable_stoppedValue_canonicalStandardHighProbabilityPseudoRegret_of_boundedStoppingTime
    {K : Nat} {Feature : Type u}
    [Fintype Feature]
    (mu : Measure (Nat -> Fin K × Real)) [IsFiniteMeasure mu]
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
    (maxHorizon : Nat)
    (htau_le : forall trajectory,
      tau trajectory <= (maxHorizon : WithTop Nat)) :
    Integrable
      (stoppedValue
        (fun horizon trajectory =>
          canonicalStandardHighProbabilityPseudoRegret
            thetaStar actionFeature best horizon trajectory)
        tau) mu := by
  have hprogressive :
      ProgMeasurable
        (canonicalHistoryTrajectoryAllRoundFiltration (K := K))
        (fun horizon trajectory =>
          canonicalStandardHighProbabilityPseudoRegret
            thetaStar actionFeature best horizon trajectory) :=
    (canonicalStandardHighProbabilityPseudoRegret_stronglyAdapted_allRound
      thetaStar actionFeature best).progMeasurable_of_discrete
  have hstrong :
      StronglyMeasurable
        (stoppedValue
          (fun horizon trajectory =>
            canonicalStandardHighProbabilityPseudoRegret
              thetaStar actionFeature best horizon trajectory)
          tau) :=
    (stronglyMeasurable_stoppedValue_of_le
      hprogressive htau htau_le).mono
        ((canonicalHistoryTrajectoryAllRoundFiltration (K := K)).le
          maxHorizon)
  refine Integrable.of_bound hstrong.aestronglyMeasurable
    (standardScalarAllRoundGapEnvelope S maxHorizon L2) ?_
  exact Filter.Eventually.of_forall fun trajectory => by
    simpa [Real.norm_eq_abs] using
      abs_stoppedValue_canonicalStandardHighProbabilityPseudoRegret_le_envelope
        thetaStar actionFeature S hS L2 hactionFeatureBound best htheta
        tau maxHorizon htau_le trajectory

/--
Generic stopped expectation assembly: off the stopped violation event, the
stopped regret is below the endpoint explicit budget; on the event it is
charged by the endpoint deterministic envelope.
-/
theorem
    integral_stoppedValue_canonicalStandardHighProbabilityPseudoRegret_le_endpoint_add_envelope_mul_real_measure
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [Nonempty Feature]
    (mu : Measure (Nat -> Fin K × Real)) [IsProbabilityMeasure mu]
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
    (maxHorizon : Nat)
    (htau_le : forall trajectory,
      tau trajectory <= (maxHorizon : WithTop Nat)) :
    integral mu
        (stoppedValue
          (fun horizon trajectory =>
            canonicalStandardHighProbabilityPseudoRegret
              thetaStar actionFeature best horizon trajectory)
          tau) <=
      telescopingHighProbabilityPseudoRegretBound
          (Feature := Feature) R delta lambda S maxHorizon L2 +
        standardScalarAllRoundGapEnvelope S maxHorizon L2 *
          mu.real
            (telescopingCanonicalExplicitHighProbabilityPseudoRegretStoppedViolationSet
              lambda thetaStar actionFeature R delta S L2 best tau) := by
  let gap :=
    stoppedValue
      (fun horizon trajectory =>
        canonicalStandardHighProbabilityPseudoRegret
          thetaStar actionFeature best horizon trajectory)
      tau
  let budget :=
    telescopingHighProbabilityPseudoRegretBound
      (Feature := Feature) R delta lambda S maxHorizon L2
  let envelope := standardScalarAllRoundGapEnvelope S maxHorizon L2
  let bad :=
    telescopingCanonicalExplicitHighProbabilityPseudoRegretStoppedViolationSet
      lambda thetaStar actionFeature R delta S L2 best tau
  let overflow : (Nat -> Fin K × Real) -> Real :=
    bad.indicator (fun _trajectory => envelope)
  have hbad : MeasurableSet bad := by
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
    have hboundStrong :
        StronglyMeasurable
          (stoppedValue
            (fun horizon (_trajectory : Nat -> Fin K × Real) =>
              telescopingHighProbabilityPseudoRegretBound
                (Feature := Feature) R delta lambda S horizon L2)
            tau) :=
      (stronglyMeasurable_stoppedValue_of_le
        hboundProgressive htau htau_le).mono
        ((canonicalHistoryTrajectoryAllRoundFiltration (K := K)).le
          maxHorizon)
    have hregretStrong :
        StronglyMeasurable gap :=
      (stronglyMeasurable_stoppedValue_of_le
        hregretProgressive htau htau_le).mono
        ((canonicalHistoryTrajectoryAllRoundFiltration (K := K)).le
          maxHorizon)
    exact measurableSet_lt hboundStrong.measurable hregretStrong.measurable
  have hgap : Integrable gap mu := by
    exact
      integrable_stoppedValue_canonicalStandardHighProbabilityPseudoRegret_of_boundedStoppingTime
        mu thetaStar actionFeature S hS L2 hactionFeatureBound best htheta
        tau htau maxHorizon htau_le
  have hoverflow : Integrable overflow mu :=
    (integrable_const envelope).indicator hbad
  have hbudget : 0 <= budget := by
    exact
      telescopingHighProbabilityPseudoRegretBound_nonneg
        (Feature := Feature) R hR delta hdelta hdelta_one
        lambda hlambda S hS maxHorizon L2 hL2
  have hpoint : forall trajectory, gap trajectory <=
      budget + overflow trajectory := by
    intro trajectory
    by_cases htrajectory : trajectory ∈ bad
    · have hgapEnvelope : gap trajectory <= envelope := by
        exact (le_abs_self _).trans
          (abs_stoppedValue_canonicalStandardHighProbabilityPseudoRegret_le_envelope
            thetaStar actionFeature S hS L2 hactionFeatureBound best htheta
            tau maxHorizon htau_le trajectory)
      calc
        gap trajectory <= envelope := hgapEnvelope
        _ <= budget + envelope := le_add_of_nonneg_left hbudget
        _ = budget + overflow trajectory := by
          simp [overflow, Set.indicator_of_mem htrajectory]
    · have htau_nat : (tau trajectory).untopA <= maxHorizon := by
        have hcoe :
            ((tau trajectory).untopA : WithTop Nat) <=
              (maxHorizon : WithTop Nat) := by
          rw [coe_untopA_boundedTrajectoryTime tau maxHorizon htau_le trajectory]
          exact htau_le trajectory
        exact_mod_cast hcoe
      have hgapStoppedBudget :
          gap trajectory <=
            stoppedValue
              (fun horizon (_trajectory : Nat -> Fin K × Real) =>
                telescopingHighProbabilityPseudoRegretBound
                  (Feature := Feature) R delta lambda S horizon L2)
              tau trajectory := by
        apply le_of_not_gt
        simpa [bad, gap,
          telescopingCanonicalExplicitHighProbabilityPseudoRegretStoppedViolationSet]
          using htrajectory
      have hstoppedBudget :
          stoppedValue
              (fun horizon (_trajectory : Nat -> Fin K × Real) =>
                telescopingHighProbabilityPseudoRegretBound
                  (Feature := Feature) R delta lambda S horizon L2)
              tau trajectory <= budget := by
        simpa only [stoppedValue, budget] using
          (telescopingHighProbabilityPseudoRegretBound_mono
            (Feature := Feature) R hR delta hdelta hdelta_one
            lambda hlambda S hS L2 hL2 htau_nat)
      calc
        gap trajectory <=
            stoppedValue
              (fun horizon (_trajectory : Nat -> Fin K × Real) =>
                telescopingHighProbabilityPseudoRegretBound
                  (Feature := Feature) R delta lambda S horizon L2)
              tau trajectory := hgapStoppedBudget
        _ <= budget := hstoppedBudget
        _ = budget + overflow trajectory := by
          simp [overflow, Set.indicator_of_notMem htrajectory]
  calc
    integral mu gap <=
        integral mu (fun trajectory => budget + overflow trajectory) :=
      integral_mono hgap ((integrable_const budget).add hoverflow) hpoint
    _ = budget + integral mu overflow := by
      rw [integral_add (integrable_const budget) hoverflow, integral_const]
      simp [MeasureTheory.probReal_univ]
    _ = budget + envelope * mu.real bad := by
      congr 1
      change integral mu (bad.indicator (fun _trajectory => envelope)) =
        envelope * mu.real bad
      rw [integral_indicator hbad, setIntegral_const]
      simp [Measure.real, smul_eq_mul, mul_comm]

/--
Complete bounded-stopping-time expected pseudo-regret theorem for the single
telescoping-schedule OFUL policy.
-/
theorem
    integral_stoppedValue_canonicalStandardHighProbabilityPseudoRegret_nonneg_and_le_endpoint_add_envelope_mul_delta_of_linearSubgaussianEnvironment_of_featureBound_le_regularization
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
    0 <= integral mu stoppedRegret /\
      integral mu stoppedRegret <=
        telescopingHighProbabilityPseudoRegretBound
            (Feature := Feature) R delta lambda S maxHorizon L2 +
          standardScalarAllRoundGapEnvelope S maxHorizon L2 * delta := by
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
  let bad :=
    telescopingCanonicalExplicitHighProbabilityPseudoRegretStoppedViolationSet
      lambda thetaStar actionFeature R delta S L2 best tau
  have htail : mu bad <= ENNReal.ofReal delta := by
    exact
      measure_telescopingCanonicalExplicitHighProbabilityPseudoRegretStoppedViolationSet_le_of_linearSubgaussianEnvironment_of_featureBound_le_regularization
        hK lambda hlambda thetaStar actionFeature R hR
        delta hdelta hdelta_one S hS environment L2 hL2
        hactionFeatureBound hL2lambda best hbest source tau
  have htailReal : mu.real bad <= delta := by
    apply ENNReal.toReal_le_of_le_ofReal hdelta.le
    exact htail
  constructor
  · exact integral_nonneg fun trajectory => by
      simp only [stoppedValue, canonicalStandardHighProbabilityPseudoRegret]
      exact
        canonicalHistoryTrajectorySumRangeAllFixedComparatorGap_nonneg
          thetaStar actionFeature (tau trajectory).untopA best hbest trajectory
  · calc
      integral mu stoppedRegret <=
          telescopingHighProbabilityPseudoRegretBound
              (Feature := Feature) R delta lambda S maxHorizon L2 +
            standardScalarAllRoundGapEnvelope S maxHorizon L2 *
              mu.real bad := by
        exact
          integral_stoppedValue_canonicalStandardHighProbabilityPseudoRegret_le_endpoint_add_envelope_mul_real_measure
            mu lambda hlambda thetaStar actionFeature R hR.le
            delta hdelta hdelta_one S hS L2 hL2 hactionFeatureBound
            best source.theta_norm_le tau htau maxHorizon htau_le
      _ <=
          telescopingHighProbabilityPseudoRegretBound
              (Feature := Feature) R delta lambda S maxHorizon L2 +
            standardScalarAllRoundGapEnvelope S maxHorizon L2 * delta := by
        exact add_le_add_right
          (mul_le_mul_of_nonneg_left htailReal
            (standardScalarAllRoundGapEnvelope_nonneg
              S hS maxHorizon L2)) _

end OFUL
end BanditRLProof
