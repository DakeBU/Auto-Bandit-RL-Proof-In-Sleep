import BanditRLProof.Algorithms.CUCBRewardKernel

/-! Actual reward and true-score expectations on every horizon of the same
CUCB trajectory. The joint action/feedback distribution is retained. -/
namespace BanditRLProof.CUCB.SourceModel
open MeasureTheory ProbabilityTheory
set_option autoImplicit false
variable {A : Type*} [Fintype A] [Nonempty A] [MeasurableSpace A]
  [MeasurableSingletonClass A] {m : ℕ} {M : FeedbackModel A m} (S : SourceModel M)

theorem integrable_actual_reward (n : ℕ) :
    Integrable (fun Y : ℕ → Round A m => (Y n).2.2.2) (cucbTrajectory S.oracle M.environment) := by
  cases n with
  | zero =>
    have hi : Integrable (fun z : Round A m => z.2.2.2)
        ((cucbTrajectory S.oracle M.environment).map (fun Y => Y 0)) := by
      rw [cucbTrajectory_initial_law]
      exact S.integrable_round_reward _
    exact (integrable_map_measure
      (show Measurable (fun z : Round A m => z.2.2.2) by fun_prop).aestronglyMeasurable
      (measurable_pi_apply 0).aemeasurable).1 hi
  | succ n =>
    let μ := (cucbTrajectory S.oracle M.environment).map (Preorder.frestrictLe n)
    letI : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map
      (Preorder.measurable_frestrictLe n).aemeasurable
    have hi := S.integrable_joint_reward μ
      (fun h => oracleInput (feedbackExtension n h) (n+1))
      ((measurable_oracleInput (n+1)).comp (measurable_feedbackExtension n))
    change Integrable (fun p => p.2.2.2.2) (μ ⊗ₘ cucbStepKernel S.oracle M.environment n) at hi
    dsimp only [μ] at hi
    rw [cucbTrajectory_prefix_compProd] at hi
    exact (integrable_map_measure
      (show Measurable (fun p : ((i : Finset.Iic n) → Round A m) × Round A m => p.2.2.2.2)
        by fun_prop).aestronglyMeasurable
      ((Preorder.measurable_frestrictLe n).prodMk (measurable_pi_apply (n+1))).aemeasurable).1 hi

theorem actual_reward_expectation (n : ℕ) :
    (∫Y : ℕ → Round A m, (Y n).2.2.2 ∂cucbTrajectory S.oracle M.environment)=
      ∫Y : ℕ → Round A m, S.score M.trueInput (Y n).1 ∂cucbTrajectory S.oracle M.environment := by
  cases n with
  | zero =>
    have hr := integral_map (μ:=cucbTrajectory S.oracle M.environment)
      (measurable_pi_apply 0).aemeasurable
      (show Measurable (fun z : Round A m => z.2.2.2) by fun_prop).aestronglyMeasurable
    have hs := integral_map (μ:=cucbTrajectory S.oracle M.environment)
      (measurable_pi_apply 0).aemeasurable
      ((measurable_of_countable (f:=S.score M.trueInput)).comp measurable_fst).aestronglyMeasurable
    rw [cucbTrajectory_initial_law] at hr hs
    exact hr.symm.trans ((S.integral_round_reward_eq_score _).trans hs)
  | succ n =>
    let μ := (cucbTrajectory S.oracle M.environment).map (Preorder.frestrictLe n)
    letI : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map
      (Preorder.measurable_frestrictLe n).aemeasurable
    have hP := (Preorder.measurable_frestrictLe (X:=fun _ : ℕ => Round A m) n).prodMk
      (measurable_pi_apply (n+1))
    have hr := integral_map (μ:=cucbTrajectory S.oracle M.environment) hP.aemeasurable
      (show Measurable (fun p : ((i : Finset.Iic n) → Round A m) × Round A m => p.2.2.2.2)
        by fun_prop).aestronglyMeasurable
    have hs := integral_map (μ:=cucbTrajectory S.oracle M.environment) hP.aemeasurable
      ((measurable_of_countable (f:=S.score M.trueInput)).comp
        (show Measurable (fun p : ((i : Finset.Iic n) → Round A m) × Round A m => p.2.1)
          by fun_prop)).aestronglyMeasurable
    rw [← cucbTrajectory_prefix_compProd] at hr hs
    exact hr.symm.trans ((S.integral_joint_reward_eq_score μ
      (fun h => oracleInput (feedbackExtension n h) (n+1))
      ((measurable_oracleInput (n+1)).comp (measurable_feedbackExtension n))).trans hs)

theorem cumulative_actual_reward_expectation (n : ℕ) :
    (∫Y : ℕ → Round A m, ∑t∈Finset.range n, (Y t).2.2.2 ∂cucbTrajectory S.oracle M.environment)=
      ∫Y : ℕ → Round A m, ∑t∈Finset.range n, S.score M.trueInput (Y t).1
        ∂cucbTrajectory S.oracle M.environment := by
  rw [integral_finset_sum _ (fun t _ => S.integrable_actual_reward t),
    integral_finset_sum _ (fun t _ => S.integrable_trueScore_comp
      (cucbTrajectory S.oracle M.environment) (fun Y => (Y t).1) (by fun_prop))]
  exact Finset.sum_congr rfl (fun t _ => S.actual_reward_expectation t)

noncomputable def approximationRegret (n : ℕ) : ℝ :=
  (n:ℝ)*S.alpha*S.beta*scoreOptimum S.score M.trueInput-
    ∫Y : ℕ → Round A m, ∑t∈Finset.range n, (Y t).2.2.2 ∂cucbTrajectory S.oracle M.environment

omit [MeasurableSingletonClass A] in
theorem approximationRegret_zero : S.approximationRegret 0=0 := by
  simp [approximationRegret]

theorem approximationRegret_eq_mean (n : ℕ) :
    S.approximationRegret n=(n:ℝ)*S.alpha*S.beta*scoreOptimum S.score M.trueInput-
      ∫Y : ℕ → Round A m, ∑t∈Finset.range n, S.score M.trueInput (Y t).1
        ∂cucbTrajectory S.oracle M.environment := by
  rw [approximationRegret, S.cumulative_actual_reward_expectation]

theorem integrable_actual_gap (t : ℕ) :
    Integrable (fun Y : ℕ → Round A m => S.gap (Y t).1) (cucbTrajectory S.oracle M.environment) :=
  (integrable_const (S.alpha*scoreOptimum S.score M.trueInput)).sub
    (S.integrable_trueScore_comp (cucbTrajectory S.oracle M.environment)
      (fun Y => (Y t).1) (by fun_prop))

theorem approximationRegret_eq_gap_sum (n : ℕ) :
    S.approximationRegret n =
      (∫Y : ℕ → Round A m, ∑t∈Finset.range n, S.gap (Y t).1
        ∂cucbTrajectory S.oracle M.environment)-
      (n:ℝ)*S.alpha*(1-S.beta)*scoreOptimum S.score M.trueInput := by
  have hg (t : ℕ) :
      (∫Y : ℕ → Round A m, S.gap (Y t).1 ∂cucbTrajectory S.oracle M.environment)=
        S.alpha*scoreOptimum S.score M.trueInput-
        ∫Y : ℕ → Round A m, S.score M.trueInput (Y t).1 ∂cucbTrajectory S.oracle M.environment := by
    simp only [gap, sourceGap]
    rw [integral_sub (integrable_const _)
      (S.integrable_trueScore_comp (cucbTrajectory S.oracle M.environment)
        (fun Y => (Y t).1) (by fun_prop))]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  rw [S.approximationRegret_eq_mean,
    integral_finset_sum _ (fun t _ => S.integrable_actual_gap t),
    integral_finset_sum _ (fun t _ => S.integrable_trueScore_comp
      (cucbTrajectory S.oracle M.environment) (fun Y => (Y t).1) (by fun_prop))]
  simp only [hg, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

end BanditRLProof.CUCB.SourceModel



