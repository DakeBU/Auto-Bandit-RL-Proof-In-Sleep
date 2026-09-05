import BanditRLProof.Algorithms.MOSSRewardBranch

noncomputable section
open MeasureTheory ProbabilityTheory
namespace BanditRLProof.MOSS

theorem map_condition_reward_eq_compProd {k : ℕ} (hk : 0 < k) (n : ℕ)
    (mean : Fin k → ℝ) (t : ℕ) (ν : Kernel (Fin k) ℝ) [IsMarkovKernel ν] :
    Measure.map (fun table => (canonicalCondition hk n mean t table, canonicalReward hk n mean table (t+1)))
      (UCB.armStreamMeasure ν) =
      (Measure.map (canonicalCondition hk n mean t) (UCB.armStreamMeasure ν)).compProd
        (UCB.armStreamSelectedRewardKernel t ν) := by
  let μ := UCB.armStreamMeasure ν
  let C := Measure.map (canonicalCondition hk n mean t) μ
  let P := fun table => (canonicalCondition hk n mean t table, canonicalReward hk n mean table (t+1))
  let B := fun target : ℕ × Fin k => {table | canonicalNextCoordinate hk n mean t table = target}
  have hB (q : ℕ × Fin k) : MeasurableSet (B q) :=
    (measurable_canonicalNextCoordinate hk n mean t) (measurableSet_singleton q)
  have hdB : Pairwise (Function.onFun Disjoint B) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hi hj
    exact hij (hi.symm.trans hj)
  have huB : (⋃ q, B q) = Set.univ := by
    ext x
    simp [B]
  have hpB : μ = Measure.sum (fun q => μ.restrict (B q)) := by
    rw [← Measure.restrict_iUnion hdB hB, huB, Measure.restrict_univ]
  have hdC : Pairwise (Function.onFun Disjoint (conditionBranch (k := k) t)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hi hj
    exact hij (hi.symm.trans hj)
  have huC : (⋃ q, conditionBranch (k := k) t q) = Set.univ := by
    ext x
    simp [conditionBranch]
  have hpC : C = Measure.sum (fun q => C.restrict (conditionBranch t q)) := by
    rw [← Measure.restrict_iUnion hdC (measurableSet_conditionBranch t), huC, Measure.restrict_univ]
  have hP : Measurable P := (measurable_canonicalCondition hk n mean t).prodMk
    (measurable_canonicalReward hk n mean (t+1))
  have hl : Measure.map P μ = Measure.sum (fun q => (C.restrict (conditionBranch t q)).prod (ν q.2)) := by
    calc
      _ = Measure.map P (Measure.sum (fun q => μ.restrict (B q))) := by rw [← hpB]
      _ = Measure.sum (fun q => Measure.map P (μ.restrict (B q))) := by
        apply Measure.map_sum
        rw [← hpB]
        exact hP.aemeasurable
      _ = _ := by
        congr 1
        funext q
        exact map_condition_reward_restrict_branch hk n mean t ν q 0
  have hr : C.compProd (UCB.armStreamSelectedRewardKernel t ν) =
      Measure.sum (fun q => (C.restrict (conditionBranch t q)).prod (ν q.2)) := by
    calc
      _ = (Measure.sum (fun q => C.restrict (conditionBranch t q))).compProd
          (UCB.armStreamSelectedRewardKernel t ν) := by rw [← hpC]
      _ = Measure.sum (fun q => (C.restrict (conditionBranch t q)).compProd
          (UCB.armStreamSelectedRewardKernel t ν)) := by rw [Measure.compProd_sum_left]
      _ = _ := by
        congr 1
        funext q
        have he : Filter.EventuallyEq (ae (C.restrict (conditionBranch t q)))
            (UCB.armStreamSelectedRewardKernel t ν) (Kernel.const _ (ν q.2)) := by
          filter_upwards [ae_restrict_mem (measurableSet_conditionBranch t q)] with c hc
          have hs : c.2 = q.2 := congrArg Prod.snd hc
          rw [Kernel.comap_apply, Kernel.const_apply, hs]
        rw [Measure.compProd_congr he, Measure.compProd_const]
  exact hl.trans hr.symm

/-- The actual successor reward has the selected arm law conditionally on history/action. -/
theorem canonicalReward_condDistrib {k : ℕ} (hk : 0 < k) (n : ℕ)
    (mean : Fin k → ℝ) (t : ℕ) (ν : Kernel (Fin k) ℝ) [IsMarkovKernel ν] :
    Filter.EventuallyEq (ae ((UCB.armStreamMeasure ν).map (canonicalCondition hk n mean t)))
      (condDistrib (fun table => canonicalReward hk n mean table (t+1))
        (canonicalCondition hk n mean t) (UCB.armStreamMeasure ν))
      (UCB.armStreamSelectedRewardKernel t ν) := by
  apply (condDistrib_ae_eq_iff_measure_eq_compProd (canonicalCondition hk n mean t)
    (measurable_canonicalReward hk n mean (t+1)).aemeasurable _).mpr
  exact map_condition_reward_eq_compProd hk n mean t ν

end BanditRLProof.MOSS
