import BanditRLProof.Algorithms.MOSSUnusedCoordinate

noncomputable section
open MeasureTheory ProbabilityTheory
namespace BanditRLProof.MOSS

def conditionCoordinate {k : ℕ} (t : ℕ)
    (c : History.FinitePairHistory (Fin k) ℝ t × Fin k) : ℕ × Fin k :=
  (ETC.realHistoryPullCount t c.1 c.2+1, c.2)

def conditionBranch {k : ℕ} (t : ℕ) (target : ℕ × Fin k) :=
  {c : History.FinitePairHistory (Fin k) ℝ t × Fin k | conditionCoordinate t c = target}

theorem measurable_conditionCoordinate {k : ℕ} (t : ℕ) : Measurable (conditionCoordinate (k := k) t) := by
  have hc : Measurable (fun c : History.FinitePairHistory (Fin k) ℝ t × Fin k =>
      ETC.realHistoryPullCount t c.1 c.2) := by
    apply measurable_from_prod_countable_left
    intro a
    exact UCB.measurable_realHistoryPullCount t a
  exact (hc.add_const 1).prodMk measurable_snd

theorem measurableSet_conditionBranch {k : ℕ} (t : ℕ) (target : ℕ × Fin k) :
    MeasurableSet (conditionBranch t target) :=
  (measurable_conditionCoordinate t) (measurableSet_singleton target)

theorem measurable_canonicalNextCoordinate {k : ℕ} (hk : 0 < k) (n : ℕ) (mean : Fin k → ℝ) (t : ℕ) :
    Measurable (canonicalNextCoordinate hk n mean t) :=
  (measurable_conditionCoordinate t).comp (measurable_canonicalCondition hk n mean t)

theorem canonicalReward_succ_eq_coordinate {k : ℕ} (hk : 0 < k) (n : ℕ)
    (mean : Fin k → ℝ) (t : ℕ) (table : UCB.ArmRewardStream k) :
    canonicalReward hk n mean table (t+1) =
      UCB.armStreamCoordinate (canonicalNextCoordinate hk n mean t table) table := by
  unfold canonicalReward UCB.rewardFromArmStream UCB.armStreamCoordinate canonicalNextCoordinate canonicalCondition
  dsimp only
  rw [canonicalHistory_pullCount, ← canonicalAction_succ_eq_historyAction]

theorem rebuilt_mem_conditionBranch_iff {k : ℕ} (hk : 0 < k) (n : ℕ)
    (mean : Fin k → ℝ) (t : ℕ) (target : ℕ × Fin k) (v : ℝ) (table : UCB.ArmRewardStream k) :
    canonicalConditionWithout hk n mean t target v (UCB.armStreamWithoutCoordinate target table) ∈
      conditionBranch t target ↔ canonicalNextCoordinate hk n mean t table = target :=
  (canonicalNextCoordinate_eq_iff_insert hk n mean t target v table).symm

theorem map_rebuilt_restrict_conditionBranch {k : ℕ} (hk : 0 < k) (n : ℕ)
    (mean : Fin k → ℝ) (t : ℕ) (target : ℕ × Fin k) (v : ℝ) (μ : Measure (UCB.ArmRewardStream k)) :
    (Measure.map (fun table => canonicalConditionWithout hk n mean t target v
      (UCB.armStreamWithoutCoordinate target table)) μ).restrict (conditionBranch t target) =
    (Measure.map (canonicalCondition hk n mean t) μ).restrict (conditionBranch t target) := by
  have hr := (measurable_canonicalConditionWithout hk n mean t target v).comp
    (UCB.measurable_armStreamWithoutCoordinate target)
  have hc := measurable_canonicalCondition hk n mean t
  simp only [Function.comp_def] at hr
  have hb := measurableSet_conditionBranch t target
  rw [Measure.restrict_map hr hb, Measure.restrict_map hc hb]
  have he : (fun table => canonicalConditionWithout hk n mean t target v
      (UCB.armStreamWithoutCoordinate target table)) ⁻¹' conditionBranch t target =
      {table | canonicalNextCoordinate hk n mean t table = target} := by
    ext table
    exact rebuilt_mem_conditionBranch_iff hk n mean t target v table
  rw [he]
  apply Measure.map_congr
  filter_upwards [ae_restrict_mem ((measurable_canonicalNextCoordinate hk n mean t)
    (measurableSet_singleton target))] with table hnext
  exact (canonicalCondition_eq_without hk n mean t target v table hnext).symm

theorem map_condition_reward_restrict_branch {k : ℕ} (hk : 0 < k) (n : ℕ)
    (mean : Fin k → ℝ) (t : ℕ) (ν : Kernel (Fin k) ℝ) [IsMarkovKernel ν]
    (target : ℕ × Fin k) (v : ℝ) :
    Measure.map (fun table => (canonicalCondition hk n mean t table, canonicalReward hk n mean table (t+1)))
      ((UCB.armStreamMeasure ν).restrict {table | canonicalNextCoordinate hk n mean t table = target}) =
    ((Measure.map (canonicalCondition hk n mean t) (UCB.armStreamMeasure ν)).restrict
      (conditionBranch t target)).prod (ν target.2) := by
  let R := fun table => canonicalConditionWithout hk n mean t target v (UCB.armStreamWithoutCoordinate target table)
  let P := fun table => (R table, UCB.armStreamCoordinate target table)
  let B := {table | canonicalNextCoordinate hk n mean t table = target}
  have hB : MeasurableSet B := (measurable_canonicalNextCoordinate hk n mean t) (measurableSet_singleton target)
  have hC := measurableSet_conditionBranch t target
  have hR : Measurable R := (measurable_canonicalConditionWithout hk n mean t target v).comp
    (UCB.measurable_armStreamWithoutCoordinate target)
  have hP : Measurable P := hR.prodMk (UCB.measurable_armStreamCoordinate target)
  have he : P ⁻¹' (conditionBranch t target ×ˢ Set.univ) = B := by
    ext table
    change (R table ∈ conditionBranch t target ∧ UCB.armStreamCoordinate target table ∈ Set.univ) ↔ _
    simp only [Set.mem_univ, and_true]
    exact rebuilt_mem_conditionBranch_iff hk n mean t target v table
  calc
    _ = Measure.map P ((UCB.armStreamMeasure ν).restrict B) := by
      apply Measure.map_congr
      filter_upwards [ae_restrict_mem hB] with table hnext
      apply Prod.ext
      · exact canonicalCondition_eq_without hk n mean t target v table hnext
      · rw [canonicalReward_succ_eq_coordinate, hnext]
    _ = (Measure.map P (UCB.armStreamMeasure ν)).restrict (conditionBranch t target ×ˢ Set.univ) := by
      rw [Measure.restrict_map hP (hC.prod MeasurableSet.univ), he]
    _ = ((Measure.map R (UCB.armStreamMeasure ν)).prod (ν target.2)).restrict
        (conditionBranch t target ×ˢ Set.univ) := by
      rw [map_canonicalConditionWithout_coordinate hk n mean t ν target v]
    _ = ((Measure.map R (UCB.armStreamMeasure ν)).restrict (conditionBranch t target)).prod (ν target.2) := by
      rw [Measure.restrict_prod_eq_prod_univ]
    _ = _ := by rw [map_rebuilt_restrict_conditionBranch hk n mean t target v]

end BanditRLProof.MOSS
