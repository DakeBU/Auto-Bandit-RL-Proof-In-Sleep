import BanditRLProof.OFULScheduledPowerOfTwoForcedPseudoRegretDecomposition
import BanditRLProof.OFULScheduledBlockStartForcedAllTimeConfidence

/-!
# All-time confidence for power-of-two forced telescoping OFUL

This module specializes the generic deterministic-history-selector confidence
machinery to the horizon-independent power-of-two forced policy. Its terminal
all-horizon pseudo-regret tail keeps the deterministic forced-action charge
explicit; a logarithmic scalar bound for that charge is a separate downstream
obligation.
-/

namespace BanditRLProof

open MeasureTheory Real Matrix Set
open scoped ENNReal ProbabilityTheory

universe u

namespace OFUL

/-- Scheduled radius-width charge over nonforced successor actions. -/
noncomputable def powerOfTwoOptimisticSuccessorRadiusWidthCharge
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (lambda : Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S : Real)
    (horizon : Nat)
    (trajectory : Nat -> Fin K × Real) : Real :=
  ((Finset.range horizon).filter
      (fun n => ¬ isPowerOfTwoForcedIndex n)).sum (fun n =>
    2 *
      finiteHorizonScalarConfidenceRadius
        (canonicalHistoryTrajectoryFeature actionFeature)
        R (allTimeTelescopingDelta delta (n + 1))
        lambda S (n + 1) trajectory *
      confidenceWidth
        (finiteHorizonScalarGram lambda
          (canonicalHistoryTrajectoryFeature actionFeature)
          (n + 1) trajectory)
        (actionFeature
          (Thompson.canonicalHistoryTrajectoryAction trajectory (n + 1))))

/--
On the all-time confidence event, the nonforced successor pseudo-regret is
bounded by its matching scheduled radius-width charge.
-/
theorem
    powerOfTwoOptimisticSuccessorPseudoRegret_le_radiusWidthCharge_ae_of_not_mem_allTimeConfidenceFailure
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature] [Nonempty Feature]
    (hK : 0 < K)
    (lambda : Real) (hlambda : 0 < lambda)
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S : Real)
    (forcedAction : Nat -> Fin K)
    (environment : Thompson.HistoryEnvironment (Fin K) Real)
    (horizon : Nat)
    (best : Fin K) :
    ∀ᵐ trajectory ∂
        Thompson.canonicalHistoryTrajectoryMeasure
          (finiteHistoryPowerOfTwoForcedTelescopingScalarRidgeAlgorithm
            hK lambda actionFeature R delta S forcedAction)
          environment,
      trajectory ∉
          allTimeTelescopingScalarRidgeConfidenceFailureSet
            lambda thetaStar S
            (canonicalHistoryTrajectoryFeature actionFeature)
            canonicalHistoryTrajectoryResponse R delta ->
        powerOfTwoOptimisticSuccessorPseudoRegret
            thetaStar actionFeature best horizon trajectory <=
          powerOfTwoOptimisticSuccessorRadiusWidthCharge
            lambda actionFeature R delta S horizon trajectory := by
  let mu :=
    Thompson.canonicalHistoryTrajectoryMeasure
      (finiteHistoryPowerOfTwoForcedTelescopingScalarRidgeAlgorithm
        hK lambda actionFeature R delta S forcedAction)
      environment
  have hselectors :
      ∀ᵐ trajectory ∂mu, ∀ n,
        n < horizon ->
        ¬ isPowerOfTwoForcedIndex n ->
        Thompson.canonicalHistoryTrajectoryAction trajectory (n + 1) =
          finiteHistoryTelescopingScalarRidgeOptimisticAction
            hK lambda actionFeature R delta S n
            (History.finitePairHistoryOfTrace
              (Thompson.canonicalHistoryTrajectoryAction trajectory)
              (Thompson.canonicalHistoryTrajectoryReward trajectory) n) := by
    rw [ae_all_iff]
    intro n
    by_cases hn : n < horizon
    · by_cases hnonforced : ¬ isPowerOfTwoForcedIndex n
      · filter_upwards [
          canonicalHistoryTrajectory_action_succ_ae_eq_finiteHistoryTelescopingScalarRidgeOptimisticAction_of_not_powerOfTwoForced
            hK lambda actionFeature R delta S forcedAction environment n
            hnonforced] with trajectory htrajectory
        intro _hn _hnonforced
        simpa only [
          Thompson.canonicalHistoryTrajectoryAction,
          Thompson.canonicalHistoryTrajectoryReward] using htrajectory
      · exact Filter.Eventually.of_forall (fun _trajectory _hn hcontra =>
          (hnonforced hcontra).elim)
    · exact Filter.Eventually.of_forall (fun _trajectory hcontra =>
        (hn hcontra).elim)
  filter_upwards [hselectors] with trajectory hselector
  intro hgood
  unfold powerOfTwoOptimisticSuccessorPseudoRegret
    powerOfTwoOptimisticSuccessorRadiusWidthCharge
  apply Finset.sum_le_sum
  intro n hn
  have hn_range : n < horizon :=
    Finset.mem_range.mp (Finset.mem_filter.mp hn).1
  have hnonforced : ¬ isPowerOfTwoForcedIndex n :=
    Finset.mem_filter.mp hn |>.2
  apply
    canonicalHistoryTrajectory_action_succ_gap_le_of_eq_telescopingAction_of_not_mem_confidenceFailure
      hK lambda hlambda thetaStar actionFeature R delta S trajectory n best
      (hselector n hn_range hnonforced)
  intro hfixed
  apply hgood
  unfold allTimeTelescopingScalarRidgeConfidenceFailureSet
  rw [mem_allTimeScheduledScalarRidgeConfidenceFailureSet_iff]
  exact ⟨n + 1, hfixed⟩

/--
On the confidence event, complete pseudo-regret is bounded by the initial gap,
generated forced charge, and nonforced radius-width charge.
-/
theorem
    canonicalStandardHighProbabilityPseudoRegret_le_initial_add_powerOfTwoForced_add_radiusWidthCharge_ae_of_not_mem_allTimeConfidenceFailure
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature] [Nonempty Feature]
    (hK : 0 < K)
    (lambda : Real) (hlambda : 0 < lambda)
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S : Real)
    (forcedAction : Nat -> Fin K)
    (environment : Thompson.HistoryEnvironment (Fin K) Real)
    (horizon : Nat)
    (best : Fin K) :
    ∀ᵐ trajectory ∂
        Thompson.canonicalHistoryTrajectoryMeasure
          (finiteHistoryPowerOfTwoForcedTelescopingScalarRidgeAlgorithm
            hK lambda actionFeature R delta S forcedAction)
          environment,
      trajectory ∉
          allTimeTelescopingScalarRidgeConfidenceFailureSet
            lambda thetaStar S
            (canonicalHistoryTrajectoryFeature actionFeature)
            canonicalHistoryTrajectoryResponse R delta ->
        canonicalStandardHighProbabilityPseudoRegret
            thetaStar actionFeature best horizon trajectory <=
          (linearValue thetaStar (actionFeature best) -
              linearValue thetaStar
                (actionFeature
                  (Thompson.canonicalHistoryTrajectoryAction trajectory 0))) +
            powerOfTwoForcedSuccessorPseudoRegret
              thetaStar actionFeature best horizon trajectory +
            powerOfTwoOptimisticSuccessorRadiusWidthCharge
              lambda actionFeature R delta S horizon trajectory := by
  filter_upwards [
    powerOfTwoOptimisticSuccessorPseudoRegret_le_radiusWidthCharge_ae_of_not_mem_allTimeConfidenceFailure
      hK lambda hlambda thetaStar actionFeature R delta S forcedAction
      environment horizon best] with trajectory htrajectory
  intro hgood
  rw [
    canonicalStandardHighProbabilityPseudoRegret_eq_initial_add_powerOfTwoForced_add_optimistic
      thetaStar actionFeature best horizon trajectory]
  gcongr
  exact htrajectory hgood

/--
The confidence-event finite-horizon bound with the forced charge written
directly in terms of the prescribed actions.
-/
theorem
    canonicalStandardHighProbabilityPseudoRegret_le_initial_add_powerOfTwoForcedActionCharge_add_radiusWidthCharge_ae_of_not_mem_allTimeConfidenceFailure
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature] [Nonempty Feature]
    (hK : 0 < K)
    (lambda : Real) (hlambda : 0 < lambda)
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S : Real)
    (forcedAction : Nat -> Fin K)
    (environment : Thompson.HistoryEnvironment (Fin K) Real)
    (horizon : Nat)
    (best : Fin K) :
    ∀ᵐ trajectory ∂
        Thompson.canonicalHistoryTrajectoryMeasure
          (finiteHistoryPowerOfTwoForcedTelescopingScalarRidgeAlgorithm
            hK lambda actionFeature R delta S forcedAction)
          environment,
      trajectory ∉
          allTimeTelescopingScalarRidgeConfidenceFailureSet
            lambda thetaStar S
            (canonicalHistoryTrajectoryFeature actionFeature)
            canonicalHistoryTrajectoryResponse R delta ->
        canonicalStandardHighProbabilityPseudoRegret
            thetaStar actionFeature best horizon trajectory <=
          (linearValue thetaStar (actionFeature best) -
              linearValue thetaStar
                (actionFeature
                  (Thompson.canonicalHistoryTrajectoryAction trajectory 0))) +
            powerOfTwoForcedActionSuccessorPseudoRegret
              thetaStar actionFeature best forcedAction horizon +
            powerOfTwoOptimisticSuccessorRadiusWidthCharge
              lambda actionFeature R delta S horizon trajectory := by
  filter_upwards [
    canonicalStandardHighProbabilityPseudoRegret_le_initial_add_powerOfTwoForced_add_radiusWidthCharge_ae_of_not_mem_allTimeConfidenceFailure
      hK lambda hlambda thetaStar actionFeature R delta S forcedAction
      environment horizon best,
    powerOfTwoForcedSuccessorPseudoRegret_ae_eq_forcedActionCharge
      hK lambda thetaStar actionFeature R delta S forcedAction
      environment horizon best] with trajectory htrajectory hforced
  intro hgood
  simpa only [hforced] using htrajectory hgood

/-- The linear environment law supplies the residual law for this selector. -/
noncomputable def
    canonicalPowerOfTwoForcedPredictableScalarRidgeResidualLaw_of_linearSubgaussianEnvironment
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (hK : 0 < K)
    (lambda : Real)
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S : Real)
    (forcedAction : Nat -> Fin K)
    (environment : Thompson.HistoryEnvironment (Fin K) Real)
    (source : CanonicalLinearSubgaussianEnvironmentLaw
      hK thetaStar actionFeature R S environment) :
    CanonicalDeterministicHistoryPredictableScalarRidgeResidualLaw
      hK thetaStar actionFeature R S
      (finiteHistoryPowerOfTwoForcedTelescopingScalarRidgeAction
        hK lambda actionFeature R delta S forcedAction)
      (measurable_finiteHistoryPowerOfTwoForcedTelescopingScalarRidgeAction
        hK lambda actionFeature R delta S forcedAction)
      environment :=
  canonicalDeterministicHistoryPredictableScalarRidgeResidualLaw_of_linearSubgaussianEnvironment
    hK thetaStar actionFeature R S
    (finiteHistoryPowerOfTwoForcedTelescopingScalarRidgeAction
      hK lambda actionFeature R delta S forcedAction)
    (measurable_finiteHistoryPowerOfTwoForcedTelescopingScalarRidgeAction
      hK lambda actionFeature R delta S forcedAction)
    environment source

/-- Source-level all-time confidence tail for the power-of-two policy. -/
theorem
    measure_powerOfTwoForcedCanonicalHistoryTrajectory_allTimeConfidenceFailureSet_le
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature] [Nonempty Feature]
    (hK : 0 < K)
    (lambda : Real) (hlambda : 0 < lambda)
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R : Real) (hR : 0 < R)
    (delta : Real) (hdelta : 0 < delta) (hdelta_one : delta <= 1)
    (S : Real)
    (forcedAction : Nat -> Fin K)
    (environment : Thompson.HistoryEnvironment (Fin K) Real)
    (source : CanonicalDeterministicHistoryPredictableScalarRidgeResidualLaw
      hK thetaStar actionFeature R S
      (finiteHistoryPowerOfTwoForcedTelescopingScalarRidgeAction
        hK lambda actionFeature R delta S forcedAction)
      (measurable_finiteHistoryPowerOfTwoForcedTelescopingScalarRidgeAction
        hK lambda actionFeature R delta S forcedAction)
      environment) :
    Thompson.canonicalHistoryTrajectoryMeasure
        (finiteHistoryPowerOfTwoForcedTelescopingScalarRidgeAlgorithm
          hK lambda actionFeature R delta S forcedAction)
        environment
        (allTimeTelescopingScalarRidgeConfidenceFailureSet
          lambda thetaStar S
          (canonicalHistoryTrajectoryFeature actionFeature)
          canonicalHistoryTrajectoryResponse R delta) <=
      ENNReal.ofReal delta := by
  simpa [finiteHistoryPowerOfTwoForcedTelescopingScalarRidgeAlgorithm] using
    (measure_deterministicHistoryCanonical_allTimeTelescopingScalarRidgeConfidenceFailureSet_le
      hK lambda hlambda thetaStar actionFeature R hR
      delta hdelta hdelta_one S
      (finiteHistoryPowerOfTwoForcedTelescopingScalarRidgeAction
        hK lambda actionFeature R delta S forcedAction)
      (measurable_finiteHistoryPowerOfTwoForcedTelescopingScalarRidgeAction
        hK lambda actionFeature R delta S forcedAction)
      environment source)

/-- Environment-backed all-time confidence tail for the power-of-two policy. -/
theorem
    measure_powerOfTwoForcedCanonicalHistoryTrajectory_allTimeConfidenceFailureSet_le_of_linearSubgaussianEnvironment
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature] [Nonempty Feature]
    (hK : 0 < K)
    (lambda : Real) (hlambda : 0 < lambda)
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R : Real) (hR : 0 < R)
    (delta : Real) (hdelta : 0 < delta) (hdelta_one : delta <= 1)
    (S : Real)
    (forcedAction : Nat -> Fin K)
    (environment : Thompson.HistoryEnvironment (Fin K) Real)
    (source : CanonicalLinearSubgaussianEnvironmentLaw
      hK thetaStar actionFeature R S environment) :
    Thompson.canonicalHistoryTrajectoryMeasure
        (finiteHistoryPowerOfTwoForcedTelescopingScalarRidgeAlgorithm
          hK lambda actionFeature R delta S forcedAction)
        environment
        (allTimeTelescopingScalarRidgeConfidenceFailureSet
          lambda thetaStar S
          (canonicalHistoryTrajectoryFeature actionFeature)
          canonicalHistoryTrajectoryResponse R delta) <=
      ENNReal.ofReal delta := by
  exact
    measure_powerOfTwoForcedCanonicalHistoryTrajectory_allTimeConfidenceFailureSet_le
      hK lambda hlambda thetaStar actionFeature R hR
      delta hdelta hdelta_one S forcedAction environment
      (canonicalPowerOfTwoForcedPredictableScalarRidgeResidualLaw_of_linearSubgaussianEnvironment
        hK lambda thetaStar actionFeature R delta S
        forcedAction environment source)

/-- The nonforced charge is bounded by the full pathwise width budget. -/
theorem
    powerOfTwoOptimisticSuccessorRadiusWidthCharge_le_telescopingStandardScalarRadiusWidthBound
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature] [Nonempty Feature]
    (lambda : Real) (hlambda : 0 < lambda)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S : Real) (hdelta : 0 < delta) (hS : 0 <= S)
    (horizon : Nat)
    (L2 : Real) (hL2 : 0 <= L2)
    (hactionFeatureBound : forall action,
      dotProduct (actionFeature action) (actionFeature action) <= L2)
    (hL2lambda : L2 <= lambda)
    (trajectory : Nat -> Fin K × Real) :
    powerOfTwoOptimisticSuccessorRadiusWidthCharge
        lambda actionFeature R delta S horizon trajectory <=
      telescopingStandardScalarRadiusWidthBound
        (Feature := Feature) R delta lambda S horizon L2 := by
  unfold powerOfTwoOptimisticSuccessorRadiusWidthCharge
  calc
    ((Finset.range horizon).filter
        (fun n => ¬ isPowerOfTwoForcedIndex n)).sum
        (fun n =>
          2 *
            finiteHorizonScalarConfidenceRadius
              (canonicalHistoryTrajectoryFeature actionFeature)
              R (allTimeTelescopingDelta delta (n + 1))
              lambda S (n + 1) trajectory *
            confidenceWidth
              (finiteHorizonScalarGram lambda
                (canonicalHistoryTrajectoryFeature actionFeature)
                (n + 1) trajectory)
              (actionFeature
                (Thompson.canonicalHistoryTrajectoryAction
                  trajectory (n + 1)))) <=
      (Finset.range horizon).sum
        (fun n =>
          2 *
            finiteHorizonScalarConfidenceRadius
              (canonicalHistoryTrajectoryFeature actionFeature)
              R (allTimeTelescopingDelta delta (n + 1))
              lambda S (n + 1) trajectory *
            confidenceWidth
              (finiteHorizonScalarGram lambda
                (canonicalHistoryTrajectoryFeature actionFeature)
                (n + 1) trajectory)
              (actionFeature
                (Thompson.canonicalHistoryTrajectoryAction
                  trajectory (n + 1)))) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro n _hn _hnot
        have hradius :
            0 <=
              finiteHorizonScalarConfidenceRadius
                (canonicalHistoryTrajectoryFeature actionFeature)
                R (allTimeTelescopingDelta delta (n + 1))
                lambda S (n + 1) trajectory := by
          unfold finiteHorizonScalarConfidenceRadius
            finiteHorizonConfidenceRadius
          positivity
        have hwidth :
            0 <=
              confidenceWidth
                (finiteHorizonScalarGram lambda
                  (canonicalHistoryTrajectoryFeature actionFeature)
                  (n + 1) trajectory)
                (actionFeature
                  (Thompson.canonicalHistoryTrajectoryAction
                    trajectory (n + 1))) :=
          Real.sqrt_nonneg _
        exact mul_nonneg (mul_nonneg (by norm_num) hradius) hwidth
    _ <=
      telescopingStandardScalarRadiusWidthBound
        (Feature := Feature) R delta lambda S horizon L2 :=
      canonicalHistoryTrajectory_sum_range_succ_telescoping_radius_mul_width_le_standard_of_featureBound_le_regularization
        lambda hlambda actionFeature R delta S hdelta hS
        horizon L2 hL2 hactionFeatureBound hL2lambda trajectory

/-- The fixed initial arm has the standard deterministic gap envelope. -/
theorem powerOfTwoForcedCanonicalHistoryTrajectory_initialGap_le_ae
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature]
    (hK : 0 < K)
    (lambda : Real)
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S : Real) (hS : 0 <= S)
    (forcedAction : Nat -> Fin K)
    (environment : Thompson.HistoryEnvironment (Fin K) Real)
    (L2 : Real)
    (hactionFeatureBound : forall action,
      dotProduct (actionFeature action) (actionFeature action) <= L2)
    (best : Fin K)
    (htheta : euclideanLength thetaStar <= S) :
    ∀ᵐ trajectory ∂
        Thompson.canonicalHistoryTrajectoryMeasure
          (finiteHistoryPowerOfTwoForcedTelescopingScalarRidgeAlgorithm
            hK lambda actionFeature R delta S forcedAction)
          environment,
      linearValue thetaStar (actionFeature best) -
          linearValue thetaStar
            (actionFeature
              (Thompson.canonicalHistoryTrajectoryAction trajectory 0)) <=
        standardScalarInitialGapBound S L2 := by
  filter_upwards [
    deterministicHistoryCanonical_action_zero_ae_eq_initialArm
      hK
      (finiteHistoryPowerOfTwoForcedTelescopingScalarRidgeAction
        hK lambda actionFeature R delta S forcedAction)
      (measurable_finiteHistoryPowerOfTwoForcedTelescopingScalarRidgeAction
        hK lambda actionFeature R delta S forcedAction)
      environment] with trajectory haction
  rw [haction]
  exact
    linearValue_sub_linearValue_le_two_mul_parameterFeatureBound
      thetaStar (actionFeature best) (actionFeature (Fin.mk 0 hK))
      S L2 hS htheta
      (hactionFeatureBound best)
      (hactionFeatureBound (Fin.mk 0 hK))

/--
On one all-time confidence event, every horizon is bounded by the deterministic
forced charge plus the explicit telescoping OFUL rate.
-/
theorem
    powerOfTwoForcedCanonicalStandardHighProbabilityPseudoRegret_le_forcedActionCharge_add_explicitBound_ae
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature] [Nonempty Feature]
    (hK : 0 < K)
    (lambda : Real) (hlambda : 0 < lambda)
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R : Real) (hR : 0 < R)
    (delta : Real) (hdelta : 0 < delta) (hdelta_one : delta <= 1)
    (S : Real) (hS : 0 <= S)
    (forcedAction : Nat -> Fin K)
    (environment : Thompson.HistoryEnvironment (Fin K) Real)
    (L2 : Real) (hL2 : 0 <= L2)
    (hactionFeatureBound : forall action,
      dotProduct (actionFeature action) (actionFeature action) <= L2)
    (hL2lambda : L2 <= lambda)
    (best : Fin K)
    (htheta : euclideanLength thetaStar <= S) :
    ∀ᵐ trajectory ∂
        Thompson.canonicalHistoryTrajectoryMeasure
          (finiteHistoryPowerOfTwoForcedTelescopingScalarRidgeAlgorithm
            hK lambda actionFeature R delta S forcedAction)
          environment,
      forall horizon,
        trajectory ∉
            allTimeTelescopingScalarRidgeConfidenceFailureSet
              lambda thetaStar S
              (canonicalHistoryTrajectoryFeature actionFeature)
              canonicalHistoryTrajectoryResponse R delta ->
          canonicalStandardHighProbabilityPseudoRegret
              thetaStar actionFeature best horizon trajectory <=
            powerOfTwoForcedActionSuccessorPseudoRegret
                thetaStar actionFeature best forcedAction horizon +
              telescopingHighProbabilityPseudoRegretBound
                (Feature := Feature) R delta lambda S horizon L2 := by
  rw [ae_all_iff]
  intro horizon
  filter_upwards [
    canonicalStandardHighProbabilityPseudoRegret_le_initial_add_powerOfTwoForcedActionCharge_add_radiusWidthCharge_ae_of_not_mem_allTimeConfidenceFailure
      hK lambda hlambda thetaStar actionFeature R delta S
      forcedAction environment horizon best,
    powerOfTwoForcedCanonicalHistoryTrajectory_initialGap_le_ae
      hK lambda thetaStar actionFeature R delta S hS
      forcedAction environment L2 hactionFeatureBound best htheta] with
    trajectory hdecomposition hinitial
  intro hgood
  have hregret := hdecomposition hgood
  have hradius :=
    powerOfTwoOptimisticSuccessorRadiusWidthCharge_le_telescopingStandardScalarRadiusWidthBound
      lambda hlambda actionFeature R delta S hdelta hS
      horizon L2 hL2 hactionFeatureBound hL2lambda trajectory
  have hbudget :=
    telescopingStandardScalarAllRoundGapBound_eq_telescopingHighProbabilityPseudoRegretBound
      (Feature := Feature)
      R hR delta hdelta hdelta_one lambda hlambda S horizon L2 hL2
  unfold telescopingStandardScalarAllRoundGapBound at hbudget
  linarith

/-- All-horizon violation event for the power-of-two forced policy. -/
noncomputable def
    powerOfTwoForcedCanonicalStandardHighProbabilityPseudoRegretAllHorizonViolationSet
    {K : Nat} {Feature : Type u}
    [Fintype Feature]
    (lambda : Real)
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R delta S L2 : Real)
    (forcedAction : Nat -> Fin K)
    (best : Fin K) :
    Set (Nat -> Fin K × Real) :=
  {trajectory | exists horizon,
    powerOfTwoForcedActionSuccessorPseudoRegret
        thetaStar actionFeature best forcedAction horizon +
        telescopingHighProbabilityPseudoRegretBound
          (Feature := Feature) R delta lambda S horizon L2 <
      canonicalStandardHighProbabilityPseudoRegret
        thetaStar actionFeature best horizon trajectory}

/-- Every all-horizon violation is a confidence failure almost surely. -/
theorem
    powerOfTwoForcedCanonicalStandardHighProbabilityPseudoRegretAllHorizonViolationSet_subset_confidenceFailure_ae
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature] [Nonempty Feature]
    (hK : 0 < K)
    (lambda : Real) (hlambda : 0 < lambda)
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R : Real) (hR : 0 < R)
    (delta : Real) (hdelta : 0 < delta) (hdelta_one : delta <= 1)
    (S : Real) (hS : 0 <= S)
    (forcedAction : Nat -> Fin K)
    (environment : Thompson.HistoryEnvironment (Fin K) Real)
    (L2 : Real) (hL2 : 0 <= L2)
    (hactionFeatureBound : forall action,
      dotProduct (actionFeature action) (actionFeature action) <= L2)
    (hL2lambda : L2 <= lambda)
    (best : Fin K)
    (htheta : euclideanLength thetaStar <= S) :
    ∀ᵐ trajectory ∂
        Thompson.canonicalHistoryTrajectoryMeasure
          (finiteHistoryPowerOfTwoForcedTelescopingScalarRidgeAlgorithm
            hK lambda actionFeature R delta S forcedAction)
          environment,
      trajectory ∈
          powerOfTwoForcedCanonicalStandardHighProbabilityPseudoRegretAllHorizonViolationSet
            lambda thetaStar actionFeature R delta S L2 forcedAction best ->
        trajectory ∈
          allTimeTelescopingScalarRidgeConfidenceFailureSet
            lambda thetaStar S
            (canonicalHistoryTrajectoryFeature actionFeature)
            canonicalHistoryTrajectoryResponse R delta := by
  filter_upwards [
    powerOfTwoForcedCanonicalStandardHighProbabilityPseudoRegret_le_forcedActionCharge_add_explicitBound_ae
      hK lambda hlambda thetaStar actionFeature R hR
      delta hdelta hdelta_one S hS forcedAction environment
      L2 hL2 hactionFeatureBound hL2lambda best htheta] with
    trajectory htrajectory
  rintro ⟨horizon, hviolation⟩
  by_contra hgood
  exact (not_lt_of_ge (htrajectory horizon hgood)) hviolation

/--
Complete all-horizon high-probability pseudo-regret theorem for the fixed
power-of-two forced policy, with deterministic forced charge explicit.
-/
theorem
    powerOfTwoForcedCanonicalStandardHighProbabilityPseudoRegret_nonneg_and_allHorizon_tail_le_explicitBound_of_linearSubgaussianEnvironment_of_featureBound_le_regularization
    {K : Nat} {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature] [Nonempty Feature]
    (hK : 0 < K)
    (lambda : Real) (hlambda : 0 < lambda)
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R : Real) (hR : 0 < R)
    (delta : Real) (hdelta : 0 < delta) (hdelta_one : delta <= 1)
    (S : Real) (hS : 0 <= S)
    (forcedAction : Nat -> Fin K)
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
        thetaStar actionFeature best horizon trajectory) ∧
      Thompson.canonicalHistoryTrajectoryMeasure
          (finiteHistoryPowerOfTwoForcedTelescopingScalarRidgeAlgorithm
            hK lambda actionFeature R delta S forcedAction)
          environment
          (powerOfTwoForcedCanonicalStandardHighProbabilityPseudoRegretAllHorizonViolationSet
            lambda thetaStar actionFeature R delta S L2 forcedAction best) <=
        ENNReal.ofReal delta := by
  constructor
  · intro horizon trajectory
    exact
      canonicalHistoryTrajectorySumRangeAllFixedComparatorGap_nonneg
        thetaStar actionFeature horizon best hbest trajectory
  · calc
      Thompson.canonicalHistoryTrajectoryMeasure
          (finiteHistoryPowerOfTwoForcedTelescopingScalarRidgeAlgorithm
            hK lambda actionFeature R delta S forcedAction)
          environment
          (powerOfTwoForcedCanonicalStandardHighProbabilityPseudoRegretAllHorizonViolationSet
            lambda thetaStar actionFeature R delta S L2 forcedAction best) <=
        Thompson.canonicalHistoryTrajectoryMeasure
          (finiteHistoryPowerOfTwoForcedTelescopingScalarRidgeAlgorithm
            hK lambda actionFeature R delta S forcedAction)
          environment
          (allTimeTelescopingScalarRidgeConfidenceFailureSet
            lambda thetaStar S
            (canonicalHistoryTrajectoryFeature actionFeature)
            canonicalHistoryTrajectoryResponse R delta) := by
        exact measure_mono_ae
          (powerOfTwoForcedCanonicalStandardHighProbabilityPseudoRegretAllHorizonViolationSet_subset_confidenceFailure_ae
            hK lambda hlambda thetaStar actionFeature R hR
            delta hdelta hdelta_one S hS forcedAction environment
            L2 hL2 hactionFeatureBound hL2lambda best source.theta_norm_le)
      _ <= ENNReal.ofReal delta :=
        measure_powerOfTwoForcedCanonicalHistoryTrajectory_allTimeConfidenceFailureSet_le_of_linearSubgaussianEnvironment
          hK lambda hlambda thetaStar actionFeature R hR
          delta hdelta hdelta_one S forcedAction environment source

end OFUL
end BanditRLProof
