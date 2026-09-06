import BanditRLProof.Algorithms.ETCRealArgmaxTie

/-!
# Native Real ETC finite-history score bridge

This module mirrors the finite-pair-history `pullCount'`, `sumRewards'`, and
`empMean'` score surface used by the pinned LML ETC source. It identifies that
history score with the existing native Real exploration score, then feeds the
history-shaped commit law into the exact source adapter.
-/

namespace BanditRLProof
namespace ETC

open MeasureTheory ProbabilityTheory

/-- Number of occurrences of an arm in an inclusive finite pair history. -/
noncomputable def realHistoryPullCount {K : Nat} (n : Nat)
    (history : History.FinitePairHistory (Fin K) Real n)
    (arm : Fin K) : Nat :=
  Finset.univ.sum (fun i => if (history i).1 = arm then 1 else 0)

/-- Sum of rewards of an arm in an inclusive finite pair history. -/
noncomputable def realHistorySumRewards {K : Nat} (n : Nat)
    (history : History.FinitePairHistory (Fin K) Real n)
    (arm : Fin K) : Real :=
  Finset.univ.sum (fun i => if (history i).1 = arm then (history i).2 else 0)

/-- Empirical mean of an arm in an inclusive finite pair history. -/
noncomputable def realHistoryEmpMean {K : Nat} (n : Nat)
    (history : History.FinitePairHistory (Fin K) Real n)
    (arm : Fin K) : Real :=
  ETC.realHistorySumRewards n history arm /
    (ETC.realHistoryPullCount n history arm : Real)

/-- Inclusive history pull counts are exclusive trace pull counts at `n + 1`. -/
theorem realHistoryPullCount_finitePairHistoryOfTrace
    {K : Nat} (action : ActionTrace (Fin K)) (reward : RewardTrace Real)
    (n : Nat) (arm : Fin K) :
    ETC.realHistoryPullCount n
        (History.finitePairHistoryOfTrace action reward n) arm =
      pullCount action arm (n + 1) := by
  rw [pullCount_eq_finset_filter_card]
  simp only [ETC.realHistoryPullCount,
    History.finitePairHistoryOfTrace_apply]
  calc
    (∑ i : Finset.Iic n, if action i.1 = arm then 1 else 0) =
        (Finset.Iic n).sum
          (fun i : Nat => if action i = arm then 1 else 0) :=
      Finset.sum_coe_sort (Finset.Iic n)
        (fun i : Nat => if action i = arm then 1 else 0)
    _ = (Finset.range (n + 1)).sum
          (fun i : Nat => if action i = arm then 1 else 0) := by
      congr 1
      ext i
      simp [Finset.mem_Iic, Finset.mem_range]
    _ = ((Finset.range (n + 1)).filter
          (fun i : Nat => action i = arm)).card := by
      classical
      induction Finset.range (n + 1) using Finset.induction_on with
      | empty => simp
      | @insert i s hi ih =>
          by_cases hia : action i = arm
          · simp_all
          · simp_all

/-- Inclusive history reward sums are exclusive trace sums at `n + 1`. -/
theorem realHistorySumRewards_finitePairHistoryOfTrace
    {K : Nat} (action : ActionTrace (Fin K)) (reward : RewardTrace Real)
    (n : Nat) (arm : Fin K) :
    ETC.realHistorySumRewards n
        (History.finitePairHistoryOfTrace action reward n) arm =
      sumRewards action reward arm (n + 1) := by
  simp only [ETC.realHistorySumRewards,
    History.finitePairHistoryOfTrace_apply]
  rw [Finset.sum_coe_sort (s := Finset.Iic n)
    (f := fun i : Nat => if action i = arm then reward i else 0)]
  rw [sumRewards_eq_finset_filter_sum]
  rw [Finset.sum_filter]
  apply Finset.sum_congr
  · ext i
    simp [Finset.mem_Iic, Finset.mem_range]
  · intro i hi
    rfl

/-- The source-shaped history mean is the trace empirical mean at `n + 1`. -/
theorem realHistoryEmpMean_finitePairHistoryOfTrace
    {K : Nat} (action : ActionTrace (Fin K)) (reward : RewardTrace Real)
    (n : Nat) (arm : Fin K) :
    ETC.realHistoryEmpMean n
        (History.finitePairHistoryOfTrace action reward n) arm =
      sumRewards action reward arm (n + 1) /
        (pullCount action arm (n + 1) : Real) := by
  rw [ETC.realHistoryEmpMean,
    ETC.realHistorySumRewards_finitePairHistoryOfTrace,
    ETC.realHistoryPullCount_finitePairHistoryOfTrace]

private theorem pullCount_eq_of_eq_on_lt
    {Action : Type} [DecidableEq Action]
    (action action' : ActionTrace Action) (arm : Action) (n : Nat)
    (haction : forall t, t < n -> action t = action' t) :
    pullCount action arm n = pullCount action' arm n := by
  rw [pullCount_eq_finset_filter_card, pullCount_eq_finset_filter_card]
  congr 1
  ext t
  simp only [Finset.mem_filter, Finset.mem_range]
  by_cases ht : t < n
  · simp [ht, haction t ht]
  · simp [ht]

private theorem sumRewards_eq_of_action_eq_on_lt
    {Action Reward : Type} [DecidableEq Action] [AddCommMonoid Reward]
    (action action' : ActionTrace Action) (reward : RewardTrace Reward)
    (arm : Action) (n : Nat)
    (haction : forall t, t < n -> action t = action' t) :
    sumRewards action reward arm n = sumRewards action' reward arm n := by
  rw [sumRewards_eq_finset_filter_sum, sumRewards_eq_finset_filter_sum]
  apply Finset.sum_congr
  · ext t
    simp only [Finset.mem_filter, Finset.mem_range]
    by_cases ht : t < n
    · simp [ht, haction t ht]
    · simp [ht]
  · intro t ht
    rfl

/--
At the exploration boundary, the pinned-source finite-history score equals the
native Real exploration score whenever the observed actions are round robin.
-/
theorem realHistoryEmpMean_exploration_eq_realEmpMeanAtExploration
    {K : Nat} (spec : ETC.Spec K) (baseCommitArm : Fin K)
    (action : ActionTrace (Fin K)) (reward : RewardTrace Real)
    (hm : 0 < spec.explorationPulls)
    (hactionExplore : forall t, t < K * spec.explorationPulls ->
      action t = ETC.exploreArm spec t)
    (arm : Fin K) :
    ETC.realHistoryEmpMean (K * spec.explorationPulls - 1)
        (History.finitePairHistoryOfTrace action reward
          (K * spec.explorationPulls - 1)) arm =
      ETC.realEmpMeanAtExploration spec baseCommitArm reward arm := by
  have hpos : 0 < K * spec.explorationPulls :=
    Nat.mul_pos spec.hK hm
  have hsucc : K * spec.explorationPulls - 1 + 1 =
      K * spec.explorationPulls := by omega
  rw [ETC.realHistoryEmpMean_finitePairHistoryOfTrace]
  rw [hsucc]
  rw [ETC.realEmpMeanAtExploration]
  have hboundary : K * spec.explorationPulls =
      spec.explorationPulls * K := by simp [Nat.mul_comm]
  have hactionFixed : forall t, t < K * spec.explorationPulls ->
      action t = ETC.actionWithCommit spec baseCommitArm t := by
    intro t ht
    rw [ETC.actionWithCommit_eq_exploreArm_of_lt spec baseCommitArm
      (by simpa [Nat.mul_comm] using ht)]
    exact hactionExplore t ht
  rw [hboundary]
  rw [show (pullCount action arm (spec.explorationPulls * K) : Real) =
      (pullCount (ETC.actionWithCommit spec baseCommitArm) arm
        (spec.explorationPulls * K) : Real) by
    norm_num
    exact ETC.pullCount_eq_of_eq_on_lt
      action (ETC.actionWithCommit spec baseCommitArm) arm
        (spec.explorationPulls * K)
        (by
          intro t ht
          exact hactionFixed t (by simpa [Nat.mul_comm] using ht))]
  congr 1
  · exact ETC.sumRewards_eq_of_action_eq_on_lt
      action (ETC.actionWithCommit spec baseCommitArm) reward arm
        (spec.explorationPulls * K)
        (by
          intro t ht
          exact hactionFixed t (by simpa [Nat.mul_comm] using ht))

/--
Exact native Real ETC regret from a source-shaped finite-history commit score.
The history score is rewritten locally; callers no longer provide a commit law
already phrased with `realEmpMeanAtExploration`.
-/
theorem integral_realKernelRegret_externalAction_le_exact_sum_of_actionDependent_actionRewardHistory_condDistrib_of_historyLeastEncodedCommit_persist
    {Omega : Type u} {K : Nat} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (spec : ETC.Spec K)
    (nu : ProbabilityTheory.Kernel (Fin K) Real)
    [ProbabilityTheory.IsMarkovKernel nu]
    (sigma2 : NNReal)
    (hsubG : forall arm, ProbabilityTheory.HasSubgaussianMGF
      (fun reward => reward - realKernelMean nu arm) sigma2 (nu arm))
    (hm : 0 < spec.explorationPulls) (n : Nat)
    (hn : K * spec.explorationPulls <= n)
    (action : Omega -> ActionTrace (Fin K))
    (reward : Omega -> RewardTrace Real)
    (haction : forall t, Measurable (fun omega => action omega t))
    (hreward : forall t, Measurable (fun omega => reward omega t))
    (hactionExplore : forall t, t < K * spec.explorationPulls ->
      Filter.EventuallyEq (ae mu)
        (fun omega => action omega t)
        (fun _omega => ETC.exploreArm spec t))
    (hactionCommit : Filter.EventuallyEq (ae mu)
      (fun omega => action omega (K * spec.explorationPulls))
      (fun omega => ETC.realLeastEncodedArgmax spec.hK
        (fun arm => ETC.realHistoryEmpMean
          (K * spec.explorationPulls - 1)
          (History.finitePairHistoryOfTrace (action omega) (reward omega)
            (K * spec.explorationPulls - 1)) arm)))
    (hactionPersist : forall t, K * spec.explorationPulls <= t ->
      Filter.EventuallyEq (ae mu)
        (fun omega => action omega t)
        (fun omega => action omega (K * spec.explorationPulls)))
    (hzero : ProbabilityTheory.condDistrib
        (fun omega => reward omega 0)
        (fun omega => action omega 0) mu =ᵐ[mu.map (fun omega => action omega 0)]
      ProbabilityTheory.Kernel.ofFunOfCountable (fun arm : Fin K => nu arm))
    (hcond : forall i, i < spec.explorationPulls * K - 1 ->
      let fullCondition := fun omega : Omega =>
        (History.finitePairHistoryOfTrace
            (action omega) (reward omega) i,
          action omega (i + 1))
      ProbabilityTheory.condDistrib
          (fun omega => reward omega (i + 1))
          fullCondition mu =ᵐ[mu.map fullCondition]
        (RewardKernel.contextIndependentOfActionLaws
          (Context := History.FinitePairHistory (Fin K) Real i)
          (fun arm : Fin K => nu arm)
          (fun _arm => inferInstance)).kernel) :
    integral mu (fun omega => realKernelRegret nu (action omega) n) <=
      (Finset.univ : Finset (Fin K)).sum (fun arm =>
        realKernelGap nu arm *
          ((spec.explorationPulls : Real) +
            ((n - K * spec.explorationPulls : Nat) : Real) *
              Real.exp
                (-(spec.explorationPulls : Real) *
                  (realKernelGap nu arm) ^ 2 /
                    (4 * (sigma2 : Real))))) := by
  have hExploreAll : Filter.Eventually
      (fun omega => forall t, t < K * spec.explorationPulls ->
        action omega t = ETC.exploreArm spec t) (ae mu) := by
    rw [ae_all_iff]
    intro t
    by_cases ht : t < K * spec.explorationPulls
    · filter_upwards [hactionExplore t ht] with omega homega
      intro _ht
      exact homega
    · filter_upwards [] with omega
      intro hfalse
      exact (ht hfalse).elim
  have hactionCommitLocal : Filter.EventuallyEq (ae mu)
      (fun omega => action omega (K * spec.explorationPulls))
      (fun omega => ETC.realLeastEncodedArgmax spec.hK
        (fun arm => ETC.realEmpMeanAtExploration spec
          (ETC.realKernelBestArm spec.hK nu) (reward omega) arm)) := by
    filter_upwards [hactionCommit, hExploreAll] with omega hcommit hexplore
    rw [hcommit]
    congr 1
    funext arm
    exact ETC.realHistoryEmpMean_exploration_eq_realEmpMeanAtExploration
      spec (ETC.realKernelBestArm spec.hK nu) (action omega) (reward omega)
        hm hexplore arm
  exact
    ETC.integral_realKernelRegret_externalAction_le_exact_sum_of_actionDependent_actionRewardHistory_condDistrib_of_leastEncodedCommit_persist
      mu spec nu sigma2 hsubG hm n hn action reward haction hreward
        hactionExplore hactionCommitLocal hactionPersist hzero hcond

end ETC
end BanditRLProof
