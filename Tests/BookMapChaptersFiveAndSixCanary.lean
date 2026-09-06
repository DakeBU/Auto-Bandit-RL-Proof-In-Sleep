import BanditRLProof.OFULScheduledAllHorizonHighProbabilityRegretRate
import BanditRLProof.OFULExpectedRegretConsistency
import BanditRLProof.OFULScheduledBoundedStoppingTimeExpectedRegret
import BanditRLProof.OFULScheduledUnboundedStoppingTimeExpectedRegretExactMoment
import BanditRLProof.Algorithms.ThompsonStationaryReward
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Book Map Chapters 5--6 canonical route canary

This external module checks the scoped canonical OFUL and stationary Thompson
routes.  The typed applications below keep the generated policy, environment,
trajectory measure, confidence event, regret functional, and stopping-time
contracts in the theorem conclusions.  The Thompson endpoint is additionally
instantiated with a concrete one-arm stationary Gaussian reward kernel.

The pinned LeanMachineLearning cards remain retrieval evidence only: this
module neither imports nor shadows the upstream declarations.
-/

namespace BanditRLProof.BookMapChaptersFiveAndSixCanary

open Filter MeasureTheory ProbabilityTheory

section CH5GeometryConfidence

#check OFUL.sum_range_min_prefix_update_le_two_trace_average_log
#check OFUL.fixedDirectionCompensatedScore_hasMGFUpperBoundAt
#check OFUL.measure_finiteHorizonRidgeEstimate_error_matrixNorm_gt_confidenceRadius_le
#check OFUL.finiteHistoryTelescopingScalarRidgeOptimisticAlgorithm
#check OFUL.CanonicalLinearSubgaussianEnvironmentLaw
#check OFUL.canonicalScheduledPredictableScalarRidgeResidualLaw_of_linearSubgaussianEnvironment
#check OFUL.measure_telescopingCanonicalHistoryTrajectory_allTimeConfidenceFailureSet_le_of_linearSubgaussianEnvironment

example {K : Nat} {Feature : Type*}
    [Fintype Feature] [DecidableEq Feature] [Nonempty Feature]
    (hK : 0 < K)
    (lambda : Real) (hlambda : 0 < lambda)
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R : Real) (hR : 0 < R)
    (delta : Real) (hdelta : 0 < delta) (hdelta_one : delta <= 1)
    (S : Real)
    (environment : Thompson.HistoryEnvironment (Fin K) Real)
    (source : OFUL.CanonicalLinearSubgaussianEnvironmentLaw
      hK thetaStar actionFeature R S environment) :
    Thompson.canonicalHistoryTrajectoryMeasure
        (OFUL.finiteHistoryTelescopingScalarRidgeOptimisticAlgorithm
          hK lambda actionFeature R delta S)
        environment
        (OFUL.allTimeTelescopingScalarRidgeConfidenceFailureSet
          lambda thetaStar S
          (OFUL.canonicalHistoryTrajectoryFeature actionFeature)
          OFUL.canonicalHistoryTrajectoryResponse R delta) <=
      ENNReal.ofReal delta := by
  exact
    OFUL.measure_telescopingCanonicalHistoryTrajectory_allTimeConfidenceFailureSet_le_of_linearSubgaussianEnvironment
      hK lambda hlambda thetaStar actionFeature R hR
      delta hdelta hdelta_one S environment source

end CH5GeometryConfidence

section CH5GeneratedAllHorizon

#check OFUL.telescopingCanonicalStandardHighProbabilityPseudoRegret_nonneg_and_allHorizon_tail_le_explicitBound_of_linearSubgaussianEnvironment_of_featureBound_le_regularization

example {K : Nat} {Feature : Type*}
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
    (hbest : OFUL.IsOptimalLinearArm thetaStar actionFeature best)
    (source : OFUL.CanonicalLinearSubgaussianEnvironmentLaw
      hK thetaStar actionFeature R S environment) :
    (forall horizon trajectory,
      0 <= OFUL.canonicalStandardHighProbabilityPseudoRegret
        thetaStar actionFeature best horizon trajectory) /\
      Thompson.canonicalHistoryTrajectoryMeasure
          (OFUL.finiteHistoryTelescopingScalarRidgeOptimisticAlgorithm
            hK lambda actionFeature R delta S)
          environment
          (OFUL.telescopingCanonicalExplicitHighProbabilityPseudoRegretAllHorizonViolationSet
            lambda thetaStar actionFeature R delta S L2 best) <=
        ENNReal.ofReal delta := by
  exact
    OFUL.telescopingCanonicalStandardHighProbabilityPseudoRegret_nonneg_and_allHorizon_tail_le_explicitBound_of_linearSubgaussianEnvironment_of_featureBound_le_regularization
      hK lambda hlambda thetaStar actionFeature R hR
      delta hdelta hdelta_one S hS environment L2 hL2
      hactionFeatureBound hL2lambda best hbest source

end CH5GeneratedAllHorizon

section CH5ExpectedStopping

#check OFUL.canonicalStandardExpectedAveragePseudoRegret_tendsto_zero
#check OFUL.integral_stoppedValue_canonicalStandardHighProbabilityPseudoRegret_nonneg_and_le_endpoint_add_envelope_mul_delta_of_linearSubgaussianEnvironment_of_featureBound_le_regularization
#check OFUL.SquareIntegrableFiniteStoppingTime
#check OFUL.integral_stoppedValue_canonicalStandardHighProbabilityPseudoRegret_nonneg_and_le_quadraticCoefficient_mul_stoppingTimeRoundSecondMoment_add_initialGap_mul_sqrt_stoppingTimeRoundSecondMoment_mul_sqrt_delta_and_stoppedViolation_measure_le_of_squareIntegrableFiniteStoppingTime

example {K : Nat} {Feature : Type*}
    [Fintype Feature] [DecidableEq Feature] [Nonempty Feature]
    (hK : 0 < K)
    (lambda : Real) (hlambda : 0 < lambda)
    (thetaStar : Feature -> Real)
    (actionFeature : Fin K -> Feature -> Real)
    (R : Real) (hR : 0 < R)
    (S : Real) (hS : 0 <= S)
    (environment : Thompson.HistoryEnvironment (Fin K) Real)
    (L2 : Real) (hL2 : 0 <= L2)
    (hactionFeatureBound : forall action,
      dotProduct (actionFeature action) (actionFeature action) <= L2)
    (hL2lambda : L2 <= lambda)
    (best : Fin K)
    (hbest : OFUL.IsOptimalLinearArm thetaStar actionFeature best)
    (source : OFUL.CanonicalLinearSubgaussianEnvironmentLaw
      hK thetaStar actionFeature R S environment) :
    Tendsto
      (OFUL.canonicalStandardExpectedAveragePseudoRegret
        hK lambda thetaStar actionFeature R S environment best)
      atTop (nhds 0) := by
  exact OFUL.canonicalStandardExpectedAveragePseudoRegret_tendsto_zero
    hK lambda hlambda thetaStar actionFeature R hR S hS environment
    L2 hL2 hactionFeatureBound hL2lambda best hbest source

example {K : Nat} {Feature : Type*}
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
    (hbest : OFUL.IsOptimalLinearArm thetaStar actionFeature best)
    (source : OFUL.CanonicalLinearSubgaussianEnvironmentLaw
      hK thetaStar actionFeature R S environment)
    (tau : (Nat -> Fin K × Real) -> WithTop Nat)
    (htau : IsStoppingTime
      (OFUL.canonicalHistoryTrajectoryAllRoundFiltration (K := K)) tau)
    (maxHorizon : Nat)
    (htau_le : forall trajectory,
      tau trajectory <= (maxHorizon : WithTop Nat)) :
    let mu :=
      Thompson.canonicalHistoryTrajectoryMeasure
        (OFUL.finiteHistoryTelescopingScalarRidgeOptimisticAlgorithm
          hK lambda actionFeature R delta S)
        environment
    let stoppedRegret :=
      stoppedValue
        (fun horizon trajectory =>
          OFUL.canonicalStandardHighProbabilityPseudoRegret
            thetaStar actionFeature best horizon trajectory)
        tau
    0 <= integral mu stoppedRegret /\
      integral mu stoppedRegret <=
        OFUL.telescopingHighProbabilityPseudoRegretBound
            (Feature := Feature) R delta lambda S maxHorizon L2 +
          OFUL.standardScalarAllRoundGapEnvelope S maxHorizon L2 * delta := by
  exact
    OFUL.integral_stoppedValue_canonicalStandardHighProbabilityPseudoRegret_nonneg_and_le_endpoint_add_envelope_mul_delta_of_linearSubgaussianEnvironment_of_featureBound_le_regularization
      hK lambda hlambda thetaStar actionFeature R hR
      delta hdelta hdelta_one S hS environment L2 hL2
      hactionFeatureBound hL2lambda best hbest source
      tau htau maxHorizon htau_le

example {K : Nat} {Feature : Type*}
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
    (hbest : OFUL.IsOptimalLinearArm thetaStar actionFeature best)
    (source : OFUL.CanonicalLinearSubgaussianEnvironmentLaw
      hK thetaStar actionFeature R S environment)
    (tau : (Nat -> Fin K × Real) -> WithTop Nat)
    (htau : IsStoppingTime
      (OFUL.canonicalHistoryTrajectoryAllRoundFiltration (K := K)) tau)
    (hstop : OFUL.SquareIntegrableFiniteStoppingTime
      (Thompson.canonicalHistoryTrajectoryMeasure
        (OFUL.finiteHistoryTelescopingScalarRidgeOptimisticAlgorithm
          hK lambda actionFeature R delta S)
        environment)
      tau) :
    let mu :=
      Thompson.canonicalHistoryTrajectoryMeasure
        (OFUL.finiteHistoryTelescopingScalarRidgeOptimisticAlgorithm
          hK lambda actionFeature R delta S)
        environment
    let stoppedRegret :=
      stoppedValue
        (fun horizon trajectory =>
          OFUL.canonicalStandardHighProbabilityPseudoRegret
            thetaStar actionFeature best horizon trajectory)
        tau
    let bad :=
      OFUL.telescopingCanonicalExplicitHighProbabilityPseudoRegretStoppedViolationSet
        lambda thetaStar actionFeature R delta S L2 best tau
    0 <= integral mu stoppedRegret /\
      integral mu stoppedRegret <=
        OFUL.telescopingHighProbabilityPseudoRegretQuadraticCoefficient
            (Feature := Feature) R delta lambda S L2 *
          OFUL.stoppingTimeRoundSecondMoment mu tau hstop +
        OFUL.standardScalarInitialGapBound S L2 *
          Real.sqrt (OFUL.stoppingTimeRoundSecondMoment mu tau hstop) *
            Real.sqrt delta /\
      mu bad <= ENNReal.ofReal delta := by
  exact
    OFUL.integral_stoppedValue_canonicalStandardHighProbabilityPseudoRegret_nonneg_and_le_quadraticCoefficient_mul_stoppingTimeRoundSecondMoment_add_initialGap_mul_sqrt_stoppingTimeRoundSecondMoment_mul_sqrt_delta_and_stoppedViolation_measure_le_of_squareIntegrableFiniteStoppingTime
      hK lambda hlambda thetaStar actionFeature R hR delta hdelta hdelta_one
      S hS environment L2 hL2 hactionFeatureBound hL2lambda best hbest source
      tau htau hstop

end CH5ExpectedStopping

section CH6PosteriorProbabilityMatching

#check PosteriorKernel.canonicalPosterior_kernel_ae_eq_condDistrib_of_pair_map_eq
#check Thompson.canonicalSampler_condDistrib_action_ae_eq_bestAction
#check Thompson.uniformReferenceThompsonAlgorithm
#check Thompson.uniformReferenceThompsonAlgorithm_trajectory_condDistrib_action_ae_eq_bestAction

example {Env : Type*} {Action : Type*} {Reward : Type*}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [StandardBorelSpace Action]
    [Fintype Action] [Nonempty Action]
    [MeasurableSpace Reward] [StandardBorelSpace Reward] [Nonempty Reward]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (environment : Thompson.MeasurableHistoryEnvironment Env Action Reward)
    (bestAction : Env -> Action) (hbestAction : Measurable bestAction)
    (n : Nat) :
    let algorithm := Thompson.uniformReferenceThompsonAlgorithm
      prior environment bestAction hbestAction
    let trajectoryKernel :=
      Thompson.canonicalMeasurableEnvironmentTrajectoryKernel
        algorithm environment
    let actualMeasure := prior ⊗ₘ trajectoryKernel
    let actualHistory := fun sample =>
      History.finitePairHistoryOfTrace
        (Thompson.environmentTrajectoryAction sample)
        (Thompson.environmentTrajectoryReward sample) n
    let nextAction := fun sample =>
      Thompson.environmentTrajectoryAction sample (n + 1)
    condDistrib nextAction actualHistory actualMeasure =ᵐ[
        actualMeasure.map actualHistory]
      condDistrib (bestAction ∘ Prod.fst) actualHistory actualMeasure := by
  exact
    Thompson.uniformReferenceThompsonAlgorithm_trajectory_condDistrib_action_ae_eq_bestAction
      prior environment bestAction hbestAction n

end CH6PosteriorProbabilityMatching

section CH6DecompositionConcentration

#check Thompson.integral_trajectoryBayesMeanRegret_eq_add_historyScore
#check Thompson.integral_trajectoryBayesMeanRegret_eq_add_clippedUCB
#check Thompson.canonicalLatentArmStreamTrajectory_reward_eq_rewardFromArmStream_ae
#check Thompson.stationaryLatentArmStreamCanonicalTrajectoryMeasure_integral_sum_mean_bestAction_sub_clippedUCB_le
#check Thompson.stationaryLatentArmStreamCanonicalTrajectoryMeasure_integral_sum_clippedUCB_action_sub_mean_le

end CH6DecompositionConcentration

section CH6StationaryFinal

#check Thompson.IsOptimalMeanSelector

noncomputable def oneArmGaussianRewardKernel :
    Kernel (Unit × Fin 1) Real :=
  Kernel.const _ (gaussianReal 0 1)

noncomputable instance : IsMarkovKernel oneArmGaussianRewardKernel := by
  dsimp [oneArmGaussianRewardKernel]
  infer_instance

lemma gaussianZeroOne_hasSubgaussianMGF :
    HasSubgaussianMGF (fun reward : Real => reward) (1 : NNReal)
      (gaussianReal 0 1) := by
  constructor
  · intro t
    simpa using
      (integrable_exp_mul_gaussianReal (μ := 0) (v := (1 : NNReal)) t)
  · intro t
    rw [mgf_fun_id_gaussianReal]
    simp

#check Thompson.stationaryLatentArmStreamCanonicalTrajectoryMeasure_integral_trajectoryBayesMeanRegret_le

noncomputable example (n : Nat) :
    let prior : Measure Unit := Measure.dirac ()
    let rewardKernel : Kernel (Unit × Fin 1) Real :=
      oneArmGaussianRewardKernel
    let bestAction : Unit -> Fin 1 := fun _ => 0
    let mean : Unit -> Fin 1 -> Real := fun _ _ => 0
    let augmentedPrior :=
      Thompson.stationaryLatentArmStreamPrior prior rewardKernel
    let feedbackEnvironment :=
      Thompson.latentArmStreamMeasurableHistoryEnvironment
        (Env := Unit) (K := 1)
    let augmentedBestAction :=
      fun envStream : Unit × UCB.ArmRewardStream 1 => bestAction envStream.1
    let augmentedMean :=
      fun envStream : Unit × UCB.ArmRewardStream 1 =>
        fun arm => mean envStream.1 arm
    let algorithm := Thompson.uniformReferenceThompsonAlgorithm
      augmentedPrior feedbackEnvironment augmentedBestAction measurable_const
    integral
        (Thompson.stationaryLatentArmStreamCanonicalTrajectoryMeasure
          prior rewardKernel algorithm)
        (fun sample =>
          Thompson.trajectoryBayesMeanRegret
            augmentedMean augmentedBestAction sample n) <=
      (2 * 1 + 1) * (0 - 0) +
        8 * Real.sqrt (((1 : NNReal) : Real) * 1 * n * Real.log n) := by
  dsimp only
  simpa only [Nat.cast_one, NNReal.coe_one] using
    Thompson.stationaryLatentArmStreamCanonicalTrajectoryMeasure_integral_trajectoryBayesMeanRegret_le
      (Measure.dirac ()) oneArmGaussianRewardKernel (fun _ => 0)
      measurable_const (fun _ _ => 0) (by intro env arm; simp)
      measurable_const 0 0 (by rfl)
      (by intro env arm; simp) (1 : NNReal)
      (by
        intro env arm
        simpa [oneArmGaussianRewardKernel] using
          gaussianZeroOne_hasSubgaussianMGF)
      (by norm_num) n

end CH6StationaryFinal

#print axioms OFUL.measure_telescopingCanonicalHistoryTrajectory_allTimeConfidenceFailureSet_le_of_linearSubgaussianEnvironment
#print axioms OFUL.telescopingCanonicalStandardHighProbabilityPseudoRegret_nonneg_and_allHorizon_tail_le_explicitBound_of_linearSubgaussianEnvironment_of_featureBound_le_regularization
#print axioms OFUL.canonicalStandardExpectedAveragePseudoRegret_tendsto_zero
#print axioms OFUL.integral_stoppedValue_canonicalStandardHighProbabilityPseudoRegret_nonneg_and_le_endpoint_add_envelope_mul_delta_of_linearSubgaussianEnvironment_of_featureBound_le_regularization
#print axioms OFUL.integral_stoppedValue_canonicalStandardHighProbabilityPseudoRegret_nonneg_and_le_quadraticCoefficient_mul_stoppingTimeRoundSecondMoment_add_initialGap_mul_sqrt_stoppingTimeRoundSecondMoment_mul_sqrt_delta_and_stoppedViolation_measure_le_of_squareIntegrableFiniteStoppingTime
#print axioms Thompson.uniformReferenceThompsonAlgorithm_trajectory_condDistrib_action_ae_eq_bestAction
#print axioms Thompson.stationaryLatentArmStreamCanonicalTrajectoryMeasure_integral_trajectoryBayesMeanRegret_le

end BanditRLProof.BookMapChaptersFiveAndSixCanary
