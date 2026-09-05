import BanditRLProof.Algorithms.MOSSConditionalReward
import BanditRLProof.LowerBounds.BanditHistoryKL

noncomputable section
open MeasureTheory ProbabilityTheory
namespace BanditRLProof.MOSS

theorem canonical_initialPair_map {k : ℕ} (hk : 0 < k) (n : ℕ)
    (mean : Fin k → ℝ) (ν : Kernel (Fin k) ℝ) [IsMarkovKernel ν] :
    (UCB.armStreamMeasure ν).map (fun table =>
      (canonicalAction hk n mean table 0, canonicalReward hk n mean table 0)) =
      (historyAlgorithm hk n).initialAction.compProd ν := by
  have he : (fun table => (canonicalAction hk n mean table 0, canonicalReward hk n mean table 0)) =
      (fun r : ℝ => ((⟨0,hk⟩ : Fin k),r)) ∘ (fun table : UCB.ArmRewardStream k => table 1 ⟨0,hk⟩) := by
    funext table
    simp [canonicalReward, UCB.rewardFromArmStream, canonicalAction_zero, Function.comp_def]
  have hm : Measurable (fun table : UCB.ArmRewardStream k => table 1 ⟨0,hk⟩) :=
    (measurable_pi_apply (⟨0,hk⟩ : Fin k)).comp (measurable_pi_apply 1)
  rw [he, ← Measure.map_map measurable_prodMk_left hm,
    UCB.armStreamMeasure_map_coord]
  change (ν ⟨0,hk⟩).map (fun r => ((⟨0,hk⟩ : Fin k),r)) = (Measure.dirac ⟨0,hk⟩).compProd ν
  ext s hs
  rw [Measure.map_apply measurable_prodMk_left hs, Measure.dirac_compProd_apply hs]

theorem canonical_action_condDistrib {k : ℕ} [NeZero k] (hk : 0 < k) (n : ℕ)
    (mean : Fin k → ℝ) (t : ℕ) (ν : Kernel (Fin k) ℝ) [IsMarkovKernel ν] :
    Filter.EventuallyEq (ae ((UCB.armStreamMeasure ν).map (fun table => canonicalHistory hk n mean table t)))
      (condDistrib (fun table => canonicalAction hk n mean table (t+1))
        (fun table => canonicalHistory hk n mean table t) (UCB.armStreamMeasure ν))
      ((historyAlgorithm hk n).policy t) := by
  have h := condDistrib_comp_self (μ := UCB.armStreamMeasure ν)
    (fun table => canonicalHistory hk n mean table t) (measurable_historyAction hk n t)
  have he : (historyAction hk n t ∘ fun table => canonicalHistory hk n mean table t) =
      (fun table => canonicalAction hk n mean table (t+1)) := by
    funext table
    exact (canonicalAction_succ_eq_historyAction hk n mean table t).symm
  rw [he] at h
  exact h

theorem canonical_historySequence {k : ℕ} [NeZero k] (hk : 0 < k) (n : ℕ)
    (mean : Fin k → ℝ) (ν : Kernel (Fin k) ℝ) [IsMarkovKernel ν] :
    Thompson.IsHistoryAlgorithmEnvironmentSequence (UCB.armStreamMeasure ν)
      (canonicalAction hk n mean) (canonicalReward hk n mean) (historyAlgorithm hk n)
      (LowerBounds.stationaryBanditHistoryEnvironment ν) where
  measurable_action := measurable_canonicalAction hk n mean
  measurable_reward := measurable_canonicalReward hk n mean
  initialPair_map_eq := canonical_initialPair_map hk n mean ν
  step_condDistrib t := by
    apply RewardKernel.condDistrib_pair_ae_eq_compProd_of_split
      (UCB.armStreamMeasure ν) _ (measurable_canonicalHistory hk n mean t)
      _ (measurable_canonicalAction hk n mean (t+1))
      _ (measurable_canonicalReward hk n mean (t+1))
    · exact canonical_action_condDistrib hk n mean t ν
    · have he : (fun table => (canonicalHistory hk n mean table t,
          canonicalAction hk n mean table (t+1))) = canonicalCondition hk n mean t := by
        funext table
        exact Prod.ext rfl (canonicalAction_succ_eq_historyAction hk n mean table t)
      rw [he]
      exact canonicalReward_condDistrib hk n mean t ν

/-- Canonical reward-table histories have exactly the common bandit history law. -/
theorem map_canonicalHistory_eq {k : ℕ} [NeZero k] (hk : 0 < k) (n : ℕ)
    (mean : Fin k → ℝ) (ν : Kernel (Fin k) ℝ) [IsMarkovKernel ν] (t : ℕ) :
    (UCB.armStreamMeasure ν).map (fun table => canonicalHistory hk n mean table t) =
      LowerBounds.canonicalBanditHistoryMeasure (historyAlgorithm hk n) ν t := by
  induction t with
  | zero =>
      rw [LowerBounds.canonicalBanditHistoryMeasure_zero]
      have he : (fun table => canonicalHistory hk n mean table 0) =
          (LowerBounds.pairHistoryZeroMeasurableEquiv (Fin k) ℝ) ∘
            (fun table => (canonicalAction hk n mean table 0, canonicalReward hk n mean table 0)) := by
        funext table i
        have hi : i.val = 0 := by have := Finset.mem_Iic.mp i.property; omega
        simp [canonicalHistory, History.finitePairHistoryOfTrace,
          LowerBounds.pairHistoryZeroMeasurableEquiv, Thompson.singletonPairHistory, hi]
      rw [he, ← Measure.map_map (LowerBounds.pairHistoryZeroMeasurableEquiv (Fin k) ℝ).measurable
        ((measurable_canonicalAction hk n mean 0).prodMk (measurable_canonicalReward hk n mean 0)),
        canonical_initialPair_map]
  | succ t ih =>
      rw [LowerBounds.canonicalBanditHistoryMeasure_succ]
      let J := fun table => (canonicalHistory hk n mean table t,
        (canonicalAction hk n mean table (t+1), canonicalReward hk n mean table (t+1)))
      have hJ : Measurable J := (measurable_canonicalHistory hk n mean t).prodMk
        ((measurable_canonicalAction hk n mean (t+1)).prodMk (measurable_canonicalReward hk n mean (t+1)))
      have he : (fun table => canonicalHistory hk n mean table (t+1)) =
          (LowerBounds.pairHistorySuccMeasurableEquiv (Fin k) ℝ t) ∘ J := by
        funext table
        rw [Function.comp_apply, LowerBounds.pairHistorySuccMeasurableEquiv_apply]
        exact History.finitePairHistoryOfTrace_succ _ _ t
      have hj := Thompson.nextPairJointLaw_eq_compProd (UCB.armStreamMeasure ν)
        (canonicalAction hk n mean) (canonicalReward hk n mean) (historyAlgorithm hk n)
        (LowerBounds.stationaryBanditHistoryEnvironment ν) (canonical_historySequence hk n mean ν) t
      change (UCB.armStreamMeasure ν).map J =
        ((UCB.armStreamMeasure ν).map (fun table => canonicalHistory hk n mean table t)).compProd
          (Thompson.historyStepKernel (historyAlgorithm hk n) (LowerBounds.stationaryBanditHistoryEnvironment ν) t) at hj
      rw [he, ← Measure.map_map (LowerBounds.pairHistorySuccMeasurableEquiv (Fin k) ℝ t).measurable hJ,
        hj, ih]

end BanditRLProof.MOSS
