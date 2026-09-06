import BanditRLProof.Exp3ExpectedRegret
import BanditRLProof.Exp3MixedSquareBernsteinRealizedBestArmAllHorizon
import BanditRLProof.Exp3RealizedRegretAllTime
import BanditRLProof.Exp3MixedSquarePredictableVarianceSparseLossRealizedDoublePathwiseVarianceProbabilisticSparsityBestArmAllHorizon
import BanditRLProof.TsallisScheduledFixedGapSelfBounding
import BanditRLProof.TsallisFiniteArmIIDRewardLaw

/-!
# Book Map Chapters 7--8 canonical route canary

This external module checks the scoped canonical EXP3 and half-Tsallis FTRL
routes.  Full-conclusion applications keep the generated kernels and measures
visible.  In particular, the horizon-tuned EXP3 endpoints are not conflated
with the fixed-process all-positive-prefix endpoint.  The Tsallis terminal is
also instantiated with two nondegenerate IID bounded rational Dirac reward laws.

Paper cards and proof weapons remain retrieval evidence only.
-/

namespace BanditRLProof.BookMapChaptersSevenAndEightCanary

open MeasureTheory ProbabilityTheory

section CH7PotentialMoments

#check Exp3.exp_neg_mul_le_one_sub_add_sq_of_nonneg
#check Exp3.log_totalWeight_succ_sub_le_of_nonneg
#check Exp3.hedge_regret_le_log_card_div_add_eta_mul_mixedSquaredLoss_of_nonneg
#check Exp3.sum_prob_mul_importanceWeightedLoss_eq_loss
#check Exp3.sum_prob_mul_mixedSquaredImportanceWeightedLoss_eq_sum_loss_sq
#check Exp3.exploredHistoryAlgorithm
#check Exp3.sampledImportanceWeightedTrajectoryMeasure_condDistrib_action_given_environment
#check Exp3.sampledPredictableObserved_finiteHorizon_first_second_moment
#check Exp3.sampledTrajectory_finiteHorizon_explorationBias_secondMoment

end CH7PotentialMoments

section CH7TunedFixedWindow

example {Env : Type*} {Action : Type*}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (hcard_two : 2 <= arms.card)
    (loss : Exp3.PredictableLossVector Env Action)
    (horizon : Nat) (hhorizon_pos : 0 < horizon)
    (hscale : 4 * (arms.card : Real) * Real.log arms.card <= (horizon : Real))
    (comparator : Action) (hcomparator : comparator ∈ arms) :
    let K := (arms.card : Real)
    let T := (horizon : Real)
    let gamma := Exp3.tunedExplorationRate K T
    let eta := Exp3.tunedLearningRate K T
    let mu := prior ⊗ₘ Exp3.tunedPredictableTrajectoryKernel
      arms harms hcard_two loss horizon hhorizon_pos hscale
    integral mu (fun sample =>
        (Finset.range horizon).sum (fun t =>
          Exp3.sampledTrajectoryExploredPredictableLossAt
            arms eta gamma loss t sample) -
        (Finset.range horizon).sum (fun t =>
          Exp3.predictableLossAt loss t sample comparator)) <=
      4 * Real.sqrt (K * T * Real.log K) := by
  exact Exp3.sampledPredictable_expectedRegret_le_four_mul_sqrt
    prior arms harms hcard_two loss horizon hhorizon_pos hscale
    comparator hcomparator

example {Env : Type*} {Action : Type*}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (hcard_two : 2 <= arms.card)
    (loss : Exp3.PredictableLossVector Env Action)
    (horizon : Nat) (hhorizon : 0 < horizon)
    (delta : Real) (hdelta : 0 < delta) (hdelta_le_one : delta <= 1) :
    let deltaArm := delta / (arms.card : Real)
    let gamma := Exp3.bernsteinSquareClippedExplorationRate
      (arms.card : Real) (horizon : Real) deltaArm
    let eta := Exp3.bernsteinSquareHighProbabilityLearningRate
      arms gamma horizon deltaArm
    let mu := prior ⊗ₘ Exp3.sampledImportanceWeightedTrajectoryKernel
      arms harms eta gamma
      (Exp3.bernsteinSquareClippedExplorationRate_pos
        (arms.card : Real) (horizon : Real) deltaArm
        (by exact_mod_cast hcard_two) (by exact_mod_cast hhorizon)).le
      (by exact (Exp3.bernsteinSquareClippedExplorationRate_le_half
        (arms.card : Real) (horizon : Real) deltaArm).trans (by norm_num))
      loss.environment
    mu {sample |
      Exp3.bernsteinSquareBestArmAllHorizonRegretThreshold
          arms horizon delta <=
        (Finset.range horizon).sum (fun t =>
          Exp3.sampledTrajectoryRealizedLossAt t sample) -
        Exp3.sampledPredictableBestArmCumulativeLoss
          arms harms loss horizon sample} <= ENNReal.ofReal delta := by
  exact
    Exp3.sampledPredictable_allHorizonBernsteinSquareBestArmRealizedRegret_tail
      prior arms harms hcard_two loss horizon hhorizon delta hdelta hdelta_le_one

end CH7TunedFixedWindow

section CH7SameProcessSparse

#check Exp3.measure_sampledPredictableRegretGeometricAllTimeFailureSet_le
#check Exp3.measure_sampledRealizedDeviationGeometricAllTimeFailureSet_le
#check Exp3.sampledTrajectoryRealizedRegret_eq_predictableRegret_add_realizedDeviation

example {Env : Type*} {Action : Type*}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (heta : 0 < eta)
    (hgamma_pos : 0 < gamma) (hgamma_lt_one : gamma < 1)
    (loss : Exp3.PredictableLossVector Env Action)
    (comparator : Action) (hcomparator : comparator ∈ arms)
    (delta : Real) (hdelta : 0 < delta) :
    let mu := prior ⊗ₘ Exp3.sampledImportanceWeightedTrajectoryKernel
      arms harms eta gamma hgamma_pos.le hgamma_lt_one.le loss.environment
    mu (Exp3.sampledRealizedRegretGeometricAllTimeFailureSet
      arms eta gamma loss comparator delta) <= ENNReal.ofReal delta := by
  exact Exp3.measure_sampledRealizedRegretGeometricAllTimeFailureSet_le
    prior arms harms eta gamma heta hgamma_pos hgamma_lt_one loss
    comparator hcomparator delta hdelta

example {Env : Type*} {Action : Type*}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (hcard_two : 2 <= arms.card)
    (loss : Exp3.PredictableLossVector Env Action)
    (horizon sparsity : Nat) (hhorizon : 0 < horizon)
    (hsparsity : 0 < sparsity)
    (delta epsilon : Real) (hdelta : 0 < delta) (hdelta_le_one : delta <= 1) :
    let deltaArm := delta / (arms.card : Real)
    let gamma := Exp3.doubleVarianceProbabilisticSparseLossClippedExplorationRate
      (arms.card : Real) (sparsity : Real) (horizon : Real) deltaArm
    let eta := Exp3.pathwiseVarianceProbabilisticSparseLossHighProbabilityLearningRate
      arms gamma horizon sparsity deltaArm
    let mu := prior ⊗ₘ Exp3.sampledImportanceWeightedTrajectoryKernel
      arms harms eta gamma
      (Exp3.doubleVarianceProbabilisticSparseLossClippedExplorationRate_pos
        (arms.card : Real) (sparsity : Real) (horizon : Real) deltaArm
        (by exact_mod_cast hcard_two) (by exact_mod_cast hsparsity)
        (by exact_mod_cast hhorizon)).le
      (by exact
        (Exp3.doubleVarianceProbabilisticSparseLossClippedExplorationRate_le_half
          (arms.card : Real) (sparsity : Real) (horizon : Real) deltaArm).trans
            (by norm_num))
      loss.environment
    mu (Exp3.sampledPredictableSparsityFailure arms loss horizon sparsity) <=
        ENNReal.ofReal epsilon ->
      mu {sample |
        Exp3.doubleVarianceProbabilisticSparseLossBestArmAllHorizonRegretThreshold
            arms horizon sparsity delta <=
          (Finset.range horizon).sum (fun t =>
            Exp3.sampledTrajectoryRealizedLossAt t sample) -
          Exp3.sampledPredictableBestArmCumulativeLoss
            arms harms loss horizon sample} <=
        ENNReal.ofReal delta + ENNReal.ofReal epsilon := by
  exact
    Exp3.sampledPredictable_allHorizonDoubleVarianceProbabilisticSparseLossBestArmRealizedRegret_tail_of_sparsityFailure_le
      prior arms harms hcard_two loss horizon sparsity hhorizon hsparsity
      delta epsilon hdelta hdelta_le_one

end CH7SameProcessSparse

section CH8FTRLRegularity

#check Tsallis.negEntropyRegularizer
#check Tsallis.halfTsallisMinimizer
#check Tsallis.halfTsallisMinimizer_isRegularizedMinimizer
#check Tsallis.isRegularizedMinimizer_pos
#check Tsallis.halfTsallisMinimizer_eq_on_arms
#check Tsallis.measurable_halfTsallisMinimizer_comp
#check Tsallis.sum_prob_mul_linearLoss_sub_next_importanceWeightedLoss_le_powerSum_half_of_minimizers

end CH8FTRLRegularity

section CH8GeneratedStability

#check Tsallis.canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
#check Tsallis.sampledScheduledHalfTsallisTrajectoryMeasure_condDistrib_action_given_environment
#check Tsallis.halfTsallisScheduledMinimizer_observedEstimatedLoss_eq_probabilityAtTime
#check Tsallis.sampledScheduledHalfTsallisEstimatedRegret_pointMass_le_stability_add_penalty
#check Tsallis.integral_sum_sampledScheduledHalfTsallisPotentialStabilityAtTime_le_allRateBound
#check Tsallis.integral_sampledScheduledHalfTsallisPredictableEnvironmentRegret_pointMass_le_allRateBound
#check Tsallis.integral_sampledScheduledHalfTsallisPredictableEnvironmentRegret_hasSelfBounding_of_fixedGap
#check Tsallis.iidLossStateMeanGap_finiteArmIIDRewardVectorLoss_eq_gap

end CH8GeneratedStability

section CH8IIDFinal

noncomputable def twoArmIIDModel : FiniteBanditModel 2 where
  hK := by norm_num
  mean := fun arm => if arm = 0 then 3 / 4 else 1 / 4

theorem twoArmIIDModel_bestArm : twoArmIIDModel.bestArm = 0 := by
  norm_num [FiniteBanditModel.bestArm, twoArmIIDModel, List.finRange]

noncomputable def twoArmIIDLaw : Fin 2 -> Measure Rat :=
  fun arm => Measure.dirac (if arm = 0 then (3 / 4 : Rat) else (1 / 4 : Rat))

noncomputable example (horizon : Nat) :
    let model := twoArmIIDModel
    let armLaw := twoArmIIDLaw
    letI : Nonempty (Fin 2) := ⟨model.bestArm⟩
    let law := Tsallis.finiteArmIIDRewardVectorLaw armLaw
    let loss := Tsallis.iidLossStatePredictableLossVector
      Tsallis.finiteArmIIDRewardVectorLoss
      Tsallis.measurable_finiteArmIIDRewardVectorLoss
      Tsallis.finiteArmIIDRewardVectorLoss_nonneg
      Tsallis.finiteArmIIDRewardVectorLoss_le_one
    let selector :=
      Tsallis.canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
        (Finset.univ : Finset (Fin 2)) Finset.univ_nonempty
        Tsallis.sampledScheduledHalfTsallisSqrtSchedule loss
    let prior := Measure.infinitePi (fun _ : Nat => law)
    let mu := prior ⊗ₘ Tsallis.sampledScheduledHalfTsallisTrajectoryKernel
      (Finset.univ : Finset (Fin 2)) Finset.univ_nonempty
      Tsallis.sampledScheduledHalfTsallisSqrtSchedule
      selector.finiteHistory loss.environment
    integral mu
        (Tsallis.sampledScheduledHalfTsallisPredictableEnvironmentRegret
          (Finset.univ : Finset (Fin 2)) Finset.univ_nonempty
          Tsallis.sampledScheduledHalfTsallisSqrtSchedule loss
          (Tsallis.pointMass model.bestArm) horizon) <=
      (1 + Real.log (((horizon + 1 : Nat) : Real))) *
        (1 + 25 * ((Finset.univ : Finset (Fin 2)).erase model.bestArm).sum
          (fun arm => 1 / ((model.gap arm : Rat) : Real))) + 0 := by
  dsimp only
  exact
    Tsallis.integral_sampledScheduledHalfTsallisFiniteArmIIDRewardLawRegret_le_log
      twoArmIIDModel twoArmIIDLaw
      (by
        intro arm
        change IsProbabilityMeasure
          (Measure.dirac (if arm = 0 then (3 / 4 : Rat) else (1 / 4 : Rat)))
        infer_instance)
      (by intro arm; simp [twoArmIIDLaw]; split_ifs <;> norm_num)
      (by intro arm; simp [twoArmIIDLaw, twoArmIIDModel])
      (by
        intro arm hne
        rw [FiniteBanditModel.gap, if_neg hne,
          FiniteBanditModel.bestMean, twoArmIIDModel_bestArm]
        fin_cases arm
        · exact (hne (by simpa using twoArmIIDModel_bestArm.symm)).elim
        · norm_num [twoArmIIDModel])
      horizon 0 (by norm_num)

end CH8IIDFinal

#print axioms Exp3.sampledPredictable_expectedRegret_le_four_mul_sqrt
#print axioms Exp3.sampledPredictable_allHorizonBernsteinSquareBestArmRealizedRegret_tail
#print axioms Exp3.measure_sampledRealizedRegretGeometricAllTimeFailureSet_le
#print axioms Exp3.sampledPredictable_allHorizonDoubleVarianceProbabilisticSparseLossBestArmRealizedRegret_tail_of_sparsityFailure_le
#print axioms Tsallis.integral_sum_sampledScheduledHalfTsallisPotentialStabilityAtTime_le_allRateBound
#print axioms Tsallis.integral_sampledScheduledHalfTsallisFiniteArmIIDRewardLawRegret_le_log

end BanditRLProof.BookMapChaptersSevenAndEightCanary
