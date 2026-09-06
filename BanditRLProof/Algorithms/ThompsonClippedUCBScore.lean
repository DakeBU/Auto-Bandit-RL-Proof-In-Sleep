import BanditRLProof.Algorithms.ThompsonBayesRegretDecomposition
import BanditRLProof.Algorithms.UCBRealHistoryIndex
import BanditRLProof.PullCountDecomposition

/-!
# Clipped UCB score for the Thompson Bayesian-regret route

This module instantiates `HistoryActionScore` with the clipped upper-confidence
score used by the pinned LML Thompson regret proof.  The finite-history score
is measurable and lies in `[l, u]`; those bounds discharge every score
integrability premise in the compiled Bayesian-regret decomposition.
-/

open MeasureTheory ProbabilityTheory Finset

noncomputable section

namespace BanditRLProof
namespace Thompson

universe u

/-- The clipped UCB score on a complete action/reward trace. -/
def clippedUCB
    {K : Nat} (l u sigma2 delta : Real)
    (action : ActionTrace (Fin K)) (reward : RewardTrace Real)
    (arm : Fin K) (t : Nat) : Real :=
  if pullCount action arm t = 0 then u
  else
    max l (min u
      (UCB.realEmpiricalMean action reward arm t +
        Real.sqrt
          (2 * sigma2 * Real.log (1 / delta) /
            (pullCount action arm t : Real))))

/-- The same clipped score on the inclusive history through time `n`. -/
def clippedUCBHistory
    {K : Nat} (l u sigma2 delta : Real) (n : Nat)
    (history : History.FinitePairHistory (Fin K) Real n)
    (arm : Fin K) : Real :=
  if ETC.realHistoryPullCount n history arm = 0 then u
  else
    max l (min u
      (ETC.realHistoryEmpMean n history arm +
        Real.sqrt
          (2 * sigma2 * Real.log (1 / delta) /
            (ETC.realHistoryPullCount n history arm : Real))))

@[simp]
theorem clippedUCB_zero
    {K : Nat} (l u sigma2 delta : Real)
    (action : ActionTrace (Fin K)) (reward : RewardTrace Real)
    (arm : Fin K) :
    clippedUCB l u sigma2 delta action reward arm 0 = u := by
  simp [clippedUCB]

theorem clippedUCB_mem_Icc
    {K : Nat} (l u sigma2 delta : Real) (hlu : l <= u)
    (action : ActionTrace (Fin K)) (reward : RewardTrace Real)
    (arm : Fin K) (t : Nat) :
    clippedUCB l u sigma2 delta action reward arm t ∈ Set.Icc l u := by
  unfold clippedUCB
  split_ifs
  · exact ⟨hlu, le_rfl⟩
  · constructor <;> simp only [le_max_iff, max_le_iff, min_le_iff,
      le_min_iff] <;> grind

private theorem finset_sum_sqrt_le
    {ι : Type*} (s : Finset ι) (c : ι -> Real)
    (hc : forall i, 0 <= c i) :
    ∑ i ∈ s, Real.sqrt (c i) <=
      Real.sqrt (s.card * ∑ i ∈ s, c i) := by
  have h := Real.sum_sqrt_mul_sqrt_le s hc (fun _ => zero_le_one)
  simp only [Real.sqrt_one, mul_one, Finset.sum_const, nsmul_eq_mul] at h
  rwa [Real.sqrt_mul (by positivity), mul_comm]

private theorem finset_sum_one_div_sqrt_le
    {n : Nat} (hn : 0 < n) :
    ∑ k ∈ Finset.range (n + 1), 1 / Real.sqrt k <=
      2 * Real.sqrt n - 1 := by
  induction n with
  | zero => simp at hn
  | succ n ih =>
      rw [Finset.sum_range_succ]
      by_cases hzero : n = 0
      · rw [hzero]
        simp
        norm_num
      · have hih := ih (Nat.pos_of_ne_zero hzero)
        suffices 1 / Real.sqrt (n + 1) <=
            2 * (Real.sqrt (n + 1) - Real.sqrt n) by
          norm_num [Nat.cast_add, Nat.cast_one] at *
          linarith
        field_simp
        have hsqrtSucc : Real.sqrt (n + 1) * Real.sqrt (n + 1) = n + 1 :=
          Real.mul_self_sqrt (by positivity)
        have hsqrt : Real.sqrt n * Real.sqrt n = n :=
          Real.mul_self_sqrt (by positivity)
        nlinarith

/--
Pathwise selected-action clipped-UCB excess bound from the pinned LML
Thompson route. The only hypothesis is that every positive-count empirical
mean is strictly below its arm mean plus the confidence width.
-/
theorem sum_clippedUCB_action_sub_mean_le
    {K : Nat} [NeZero K]
    (action : ActionTrace (Fin K)) (reward : RewardTrace Real)
    (mean : Fin K -> Real) (l u sigma2 delta : Real)
    (hmeanMem : forall arm, mean arm ∈ Set.Icc l u) (hlu : l <= u)
    (hgood : forall s, s < n ->
      pullCount action (action s) s ≠ 0 ->
        UCB.realEmpiricalMean action reward (action s) s - mean (action s) <
          Real.sqrt
            (2 * sigma2 * Real.log (1 / delta) /
              (pullCount action (action s) s : Real))) :
    ∑ s ∈ Finset.range n,
        (clippedUCB l u sigma2 delta action reward (action s) s -
          mean (action s)) <=
      (u - l) * K +
        4 * Real.sqrt (2 * sigma2 * Real.log (1 / delta) * K * n) := by
  classical
  let S0 := (Finset.range n).filter
    (fun s => pullCount action (action s) s = 0)
  let S1 := (Finset.range n).filter
    (fun s => pullCount action (action s) s ≠ 0)
  have hunion : S0 ∪ S1 = Finset.range n := by
    exact Finset.filter_union_filter_not_eq _ _
  have hdisjoint : Disjoint S0 S1 :=
    Finset.disjoint_filter_filter_not _ _ _
  rw [← hunion, Finset.sum_union hdisjoint]
  gcongr
  · calc
      ∑ s ∈ S0,
          (clippedUCB l u sigma2 delta action reward (action s) s -
            mean (action s)) <=
          ∑ _s ∈ S0, (u - l) := by
            apply Finset.sum_le_sum
            intro s hs
            have hscore := clippedUCB_mem_Icc
              l u sigma2 delta hlu action reward (action s) s
            have hmean := hmeanMem (action s)
            nlinarith [hscore.2, hmean.1]
      _ = ∑ s ∈ Finset.range n,
          if pullCount action (action s) s = 0 then (u - l) else 0 := by
            dsimp only [S0]
            rw [Finset.sum_filter]
      _ = ∑ arm : Fin K,
          ∑ j ∈ Finset.range (pullCount action arm n),
            if j = 0 then (u - l) else 0 := by
            exact finset_sum_comp_pullCount action n
              (fun j => if j = 0 then (u - l) else 0)
      _ <= ∑ _arm : Fin K, (u - l) := by
            apply Finset.sum_le_sum
            intro arm _harm
            rw [Finset.sum_ite_eq']
            split_ifs
            · rfl
            · exact sub_nonneg.mpr hlu
      _ = (u - l) * K := by
            rw [Fin.sum_const, nsmul_eq_mul, mul_comm]
  · calc
      ∑ s ∈ S1,
          (clippedUCB l u sigma2 delta action reward (action s) s -
            mean (action s)) <=
          ∑ s ∈ S1,
            2 * Real.sqrt
              (2 * sigma2 * Real.log (1 / delta) /
                (pullCount action (action s) s : Real)) := by
            apply Finset.sum_le_sum
            intro s hs
            have hsRange : s ∈ Finset.range n := (Finset.mem_filter.mp hs).1
            have hsCount : pullCount action (action s) s ≠ 0 :=
              (Finset.mem_filter.mp hs).2
            have hwidth : 0 <= Real.sqrt
                (2 * sigma2 * Real.log (1 / delta) /
                  (pullCount action (action s) s : Real)) :=
              Real.sqrt_nonneg _
            unfold clippedUCB
            rw [if_neg hsCount]
            have hraw := hgood s (Finset.mem_range.mp hsRange) hsCount
            have hmean := hmeanMem (action s)
            grind
      _ <= ∑ s ∈ Finset.range n,
          2 * Real.sqrt
            (2 * sigma2 * Real.log (1 / delta) /
              (pullCount action (action s) s : Real)) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            intro s _hs _hnot
            positivity
      _ = 2 * Real.sqrt (2 * sigma2 * Real.log (1 / delta)) *
          ∑ s ∈ Finset.range n,
            (1 / Real.sqrt (pullCount action (action s) s)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro s _hs
            rw [Real.sqrt_div' _ (by positivity)]
            ring
      _ = 2 * Real.sqrt (2 * sigma2 * Real.log (1 / delta)) *
          ∑ arm : Fin K,
            ∑ j ∈ Finset.range (pullCount action arm n),
              (1 / Real.sqrt j) := by
            congr 1
            exact finset_sum_comp_pullCount action n
              (fun j : Nat => 1 / Real.sqrt (j : Real))
      _ <= 2 * Real.sqrt (2 * sigma2 * Real.log (1 / delta)) *
          (2 * ∑ arm : Fin K, Real.sqrt (pullCount action arm n)) := by
            rw [Finset.mul_sum _ _ 2]
            gcongr with arm
            by_cases hcount : pullCount action arm n = 0
            · simp [hcount]
            · have hbound := finset_sum_one_div_sqrt_le
                (Nat.pos_of_ne_zero hcount)
              rw [Finset.sum_range_succ] at hbound
              have hnonneg : 0 <=
                  1 / Real.sqrt (pullCount action arm n) := by
                positivity
              linarith
      _ <= 2 * Real.sqrt (2 * sigma2 * Real.log (1 / delta)) *
          (2 * Real.sqrt (K *
            ∑ arm : Fin K, (pullCount action arm n : Real))) := by
            gcongr
            have hsqrt := finset_sum_sqrt_le
              (Finset.univ : Finset (Fin K))
              (fun arm => (pullCount action arm n : Real))
              (fun arm => Nat.cast_nonneg _)
            simpa using hsqrt
      _ = 2 * Real.sqrt (2 * sigma2 * Real.log (1 / delta)) *
          (2 * Real.sqrt (K * n)) := by
            rw [← Nat.cast_sum, finset_sum_pullCount_eq_time action n]
      _ = 4 * Real.sqrt
          (2 * sigma2 * Real.log (1 / delta) * K * n) := by
            ring_nf
            rw [← Real.sqrt_mul' _ (by positivity)]
            ring_nf

theorem clippedUCBHistory_mem_Icc
    {K : Nat} (l u sigma2 delta : Real) (hlu : l <= u) (n : Nat)
    (history : History.FinitePairHistory (Fin K) Real n)
    (arm : Fin K) :
    clippedUCBHistory l u sigma2 delta n history arm ∈ Set.Icc l u := by
  unfold clippedUCBHistory
  split_ifs
  · exact ⟨hlu, le_rfl⟩
  · constructor <;> simp only [le_max_iff, max_le_iff, min_le_iff,
      le_min_iff] <;> grind

/-- A fixed-arm clipped score is measurable on inclusive pair histories. -/
theorem measurable_clippedUCBHistory
    {K : Nat} (l u sigma2 delta : Real) (n : Nat) (arm : Fin K) :
    Measurable (fun history : History.FinitePairHistory (Fin K) Real n =>
      clippedUCBHistory l u sigma2 delta n history arm) := by
  let hcount : Measurable
      (fun history : History.FinitePairHistory (Fin K) Real n =>
        ETC.realHistoryPullCount n history arm) :=
    UCB.measurable_realHistoryPullCount n arm
  let hcountReal : Measurable
      (fun history : History.FinitePairHistory (Fin K) Real n =>
        (ETC.realHistoryPullCount n history arm : Real)) :=
    (measurable_of_countable (fun count : Nat => (count : Real))).comp hcount
  let hraw : Measurable
      (fun history : History.FinitePairHistory (Fin K) Real n =>
        ETC.realHistoryEmpMean n history arm +
          Real.sqrt
            (2 * sigma2 * Real.log (1 / delta) /
              (ETC.realHistoryPullCount n history arm : Real))) :=
    (UCB.measurable_realHistoryEmpMean n arm).add
      ((measurable_const.div hcountReal).sqrt)
  exact Measurable.ite
    (measurableSet_eq_fun hcount measurable_const)
    measurable_const
    (measurable_const.max (measurable_const.min hraw))

/-- Joint measurability in the visible history and candidate action. -/
theorem measurable_uncurry_clippedUCBHistory
    {K : Nat} (l u sigma2 delta : Real) (n : Nat) :
    Measurable (fun pair :
      History.FinitePairHistory (Fin K) Real n × Fin K =>
        clippedUCBHistory l u sigma2 delta n pair.1 pair.2) := by
  apply measurable_from_prod_countable_left
  intro arm
  exact measurable_clippedUCBHistory l u sigma2 delta n arm

/-- `HistoryActionScore` instance for the pinned LML clipped-UCB formula. -/
def clippedUCBHistoryScore
    {K : Nat} (l u sigma2 delta : Real) :
    HistoryActionScore (Fin K) Real where
  initial := fun _ => u
  successor := fun n history arm =>
    clippedUCBHistory l u sigma2 delta n history arm
  measurable_initial := measurable_const
  measurable_successor :=
    measurable_uncurry_clippedUCBHistory l u sigma2 delta

/-- Inclusive finite-history and exclusive trace versions agree at `n + 1`. -/
theorem clippedUCBHistory_finitePairHistoryOfTrace
    {K : Nat} (l u sigma2 delta : Real)
    (action : ActionTrace (Fin K)) (reward : RewardTrace Real)
    (n : Nat) (arm : Fin K) :
    clippedUCBHistory l u sigma2 delta n
        (History.finitePairHistoryOfTrace action reward n) arm =
      clippedUCB l u sigma2 delta action reward arm (n + 1) := by
  simp only [clippedUCBHistory, clippedUCB,
    ETC.realHistoryPullCount_finitePairHistoryOfTrace,
    UCB.realHistoryEmpiricalMean_finitePairHistoryOfTrace]

/-- Evaluating the history score at the selected action recovers `clippedUCB`. -/
theorem clippedUCBHistoryScore_atTrace
    {K : Nat} (l u sigma2 delta : Real)
    (action : ActionTrace (Fin K)) (reward : RewardTrace Real) (t : Nat) :
    (clippedUCBHistoryScore l u sigma2 delta).atTrace action reward t =
      clippedUCB l u sigma2 delta action reward (action t) t := by
  cases t with
  | zero => simp [clippedUCBHistoryScore, HistoryActionScore.atTrace]
  | succ n =>
      exact clippedUCBHistory_finitePairHistoryOfTrace
        l u sigma2 delta action reward n (action (n + 1))

/-- Evaluating at a comparison arm recovers the same trace score. -/
theorem clippedUCBHistoryScore_atBestTrace
    {K : Nat} (l u sigma2 delta : Real)
    (bestArm : Fin K)
    (action : ActionTrace (Fin K)) (reward : RewardTrace Real) (t : Nat) :
    (clippedUCBHistoryScore l u sigma2 delta).atBestTrace
        bestArm action reward t =
      clippedUCB l u sigma2 delta action reward bestArm t := by
  cases t with
  | zero => simp [clippedUCBHistoryScore, HistoryActionScore.atBestTrace]
  | succ n =>
      exact clippedUCBHistory_finitePairHistoryOfTrace
        l u sigma2 delta action reward n bestArm

/-- A measurable real function with pointwise range in `[l, u]` is integrable. -/
theorem integrable_of_measurable_mem_Icc
    {Omega : Type u} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (f : Omega -> Real) (hf : Measurable f)
    {l u : Real} (hmem : forall omega, f omega ∈ Set.Icc l u) :
    Integrable f mu := by
  refine Integrable.of_bound hf.aestronglyMeasurable (max |l| |u|) ?_
  filter_upwards with omega
  rw [Real.norm_eq_abs]
  have h := hmem omega
  rcases h with ⟨hl, hu⟩
  exact abs_le_max_abs_abs hl hu

theorem integrable_trajectoryHistoryScore_clippedUCB
    {Env : Type u} {K : Nat}
    [MeasurableSpace Env]
    (mu : Measure (Env × ((n : Nat) -> Fin K × Real))) [IsFiniteMeasure mu]
    (l u sigma2 delta : Real) (hlu : l <= u) (t : Nat) :
    Integrable (fun sample =>
      trajectoryHistoryScore
        (clippedUCBHistoryScore l u sigma2 delta) sample t) mu := by
  apply integrable_of_measurable_mem_Icc mu
  · simpa [trajectoryHistoryScore] using
      ((clippedUCBHistoryScore l u sigma2 delta).measurable_atTrace
        environmentTrajectoryAction environmentTrajectoryReward
        measurable_environmentTrajectoryAction_apply
        measurable_environmentTrajectoryReward_apply t)
  · intro sample
    rw [trajectoryHistoryScore, clippedUCBHistoryScore_atTrace]
    exact clippedUCB_mem_Icc l u sigma2 delta hlu
      (environmentTrajectoryAction sample)
      (environmentTrajectoryReward sample)
      (environmentTrajectoryAction sample t) t

theorem integrable_trajectoryBestHistoryScore_clippedUCB
    {Env : Type u} {K : Nat}
    [MeasurableSpace Env]
    (mu : Measure (Env × ((n : Nat) -> Fin K × Real))) [IsFiniteMeasure mu]
    (bestAction : Env -> Fin K) (hbestAction : Measurable bestAction)
    (l u sigma2 delta : Real) (hlu : l <= u) (t : Nat) :
    Integrable (fun sample =>
      trajectoryBestHistoryScore
        (clippedUCBHistoryScore l u sigma2 delta) bestAction sample t) mu := by
  apply integrable_of_measurable_mem_Icc mu
  · simpa [trajectoryBestHistoryScore] using
      ((clippedUCBHistoryScore l u sigma2 delta).measurable_atBestTrace
        (bestAction ∘ Prod.fst) (hbestAction.comp measurable_fst)
        environmentTrajectoryAction environmentTrajectoryReward
        measurable_environmentTrajectoryAction_apply
        measurable_environmentTrajectoryReward_apply t)
  · intro sample
    rw [trajectoryBestHistoryScore, clippedUCBHistoryScore_atBestTrace]
    exact clippedUCB_mem_Icc l u sigma2 delta hlu
      (environmentTrajectoryAction sample)
      (environmentTrajectoryReward sample)
      (bestAction sample.1) t

theorem integrable_trajectoryMean_bestAction
    {Env : Type u} {K : Nat}
    [MeasurableSpace Env]
    (mu : Measure (Env × ((n : Nat) -> Fin K × Real))) [IsFiniteMeasure mu]
    (mean : Env -> Fin K -> Real)
    (hmean : Measurable (fun pair : Env × Fin K => mean pair.1 pair.2))
    (hmeanMem : forall env arm, mean env arm ∈ Set.Icc l u)
    (bestAction : Env -> Fin K) (hbestAction : Measurable bestAction) :
    Integrable (fun sample : Env × ((n : Nat) -> Fin K × Real) =>
      mean sample.1 (bestAction sample.1)) mu := by
  apply integrable_of_measurable_mem_Icc mu
  · exact hmean.comp
      (measurable_fst.prodMk (hbestAction.comp measurable_fst))
  · intro sample
    exact hmeanMem sample.1 (bestAction sample.1)

theorem integrable_trajectoryMean_action
    {Env : Type u} {K : Nat}
    [MeasurableSpace Env]
    (mu : Measure (Env × ((n : Nat) -> Fin K × Real))) [IsFiniteMeasure mu]
    (mean : Env -> Fin K -> Real)
    (hmean : Measurable (fun pair : Env × Fin K => mean pair.1 pair.2))
    (hmeanMem : forall env arm, mean env arm ∈ Set.Icc l u)
    (t : Nat) :
    Integrable (fun sample : Env × ((n : Nat) -> Fin K × Real) =>
      mean sample.1 (environmentTrajectoryAction sample t)) mu := by
  apply integrable_of_measurable_mem_Icc mu
  · exact hmean.comp
      (measurable_fst.prodMk (measurable_environmentTrajectoryAction_apply t))
  · intro sample
    exact hmeanMem sample.1 (environmentTrajectoryAction sample t)

/--
Concrete clipped-UCB specialization of the actual-trajectory Thompson
Bayesian-regret decomposition.  Range and measurability assumptions discharge
all four integrability families from `integral_trajectoryBayesMeanRegret_eq_add_historyScore`.
-/
theorem integral_trajectoryBayesMeanRegret_eq_add_clippedUCB
    {Env : Type u} {K : Nat}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [Nonempty (Fin K)]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (environment : MeasurableHistoryEnvironment Env (Fin K) Real)
    (bestAction : Env -> Fin K) (hbestAction : Measurable bestAction)
    (mean : Env -> Fin K -> Real)
    (hmean : Measurable (fun pair : Env × Fin K => mean pair.1 pair.2))
    (l u sigma2 delta : Real) (hlu : l <= u)
    (hmeanMem : forall env arm, mean env arm ∈ Set.Icc l u)
    (horizon : Nat) :
    let algorithm :=
      uniformReferenceThompsonAlgorithm prior environment bestAction hbestAction
    let actualMeasure :=
      prior ⊗ₘ canonicalMeasurableEnvironmentTrajectoryKernel algorithm environment
    integral actualMeasure (fun sample =>
        trajectoryBayesMeanRegret mean bestAction sample horizon) =
      integral actualMeasure (fun sample =>
        ∑ t ∈ range horizon,
          (mean sample.1 (bestAction sample.1) -
            clippedUCB l u sigma2 delta
              (environmentTrajectoryAction sample)
              (environmentTrajectoryReward sample)
              (bestAction sample.1) t)) +
      integral actualMeasure (fun sample =>
        ∑ t ∈ range horizon,
          (clippedUCB l u sigma2 delta
              (environmentTrajectoryAction sample)
              (environmentTrajectoryReward sample)
              (environmentTrajectoryAction sample t) t -
            mean sample.1 (environmentTrajectoryAction sample t))) := by
  dsimp only
  let algorithm :=
    uniformReferenceThompsonAlgorithm prior environment bestAction hbestAction
  let actualMeasure :=
    prior ⊗ₘ canonicalMeasurableEnvironmentTrajectoryKernel algorithm environment
  have hmeanBest : Integrable (fun sample :
      Env × ((n : Nat) -> Fin K × Real) =>
        mean sample.1 (bestAction sample.1)) actualMeasure :=
    integrable_trajectoryMean_bestAction actualMeasure mean hmean hmeanMem
      bestAction hbestAction
  have hmeanAction : forall t : Nat, t < horizon -> Integrable (fun sample :
      Env × ((n : Nat) -> Fin K × Real) =>
        mean sample.1 (environmentTrajectoryAction sample t)) actualMeasure :=
    fun t _ => integrable_trajectoryMean_action
      actualMeasure mean hmean hmeanMem t
  have hscoreAction : forall t : Nat, t < horizon -> Integrable (fun sample :
      Env × ((n : Nat) -> Fin K × Real) =>
        trajectoryHistoryScore
          (clippedUCBHistoryScore l u sigma2 delta) sample t) actualMeasure :=
    fun t _ => integrable_trajectoryHistoryScore_clippedUCB
      actualMeasure l u sigma2 delta hlu t
  have hscoreBest : forall t : Nat, t < horizon -> Integrable (fun sample :
      Env × ((n : Nat) -> Fin K × Real) =>
        trajectoryBestHistoryScore
          (clippedUCBHistoryScore l u sigma2 delta)
          bestAction sample t) actualMeasure :=
    fun t _ => integrable_trajectoryBestHistoryScore_clippedUCB
      actualMeasure bestAction hbestAction l u sigma2 delta hlu t
  simpa only [actualMeasure, algorithm,
    trajectoryHistoryScore, trajectoryBestHistoryScore,
    clippedUCBHistoryScore_atTrace,
    clippedUCBHistoryScore_atBestTrace] using
    (integral_trajectoryBayesMeanRegret_eq_add_historyScore
      prior environment bestAction hbestAction mean
      (clippedUCBHistoryScore l u sigma2 delta) horizon
      hmeanBest hmeanAction hscoreAction hscoreBest)

end Thompson
end BanditRLProof
