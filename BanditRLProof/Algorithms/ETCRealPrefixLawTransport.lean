import BanditRLProof.Algorithms.ETCFiniteArmRewardLaw
import BanditRLProof.Algorithms.ETCRealInfinitePiTail

/-!
# Native Real ETC finite-prefix law transport

This module factors the native Real ETC commit, action, and finite-horizon
kernel regret through the finite exploration reward prefix. It then transports
the canonical infinite-product regret bound to an arbitrary probability space
from equality of that finite-prefix pushforward law. A final adapter permits
an external action process that agrees almost surely with the local ETC action.
-/

namespace BanditRLProof

open MeasureTheory

namespace ETC

/-- The reward coordinates read during ETC exploration. -/
def realExplorationRewardPrefix {K : Nat} (spec : ETC.Spec K)
    (trajectory : RewardTrace Real) : Fin (spec.explorationPulls * K) -> Real :=
  fun t => trajectory t.1

/-- Extend a finite exploration prefix by zero outside the exploration phase. -/
def realRewardTraceOfExplorationPrefix {K : Nat} (spec : ETC.Spec K)
    (rewardPrefix : Fin (spec.explorationPulls * K) -> Real) : RewardTrace Real :=
  fun t => if ht : t < spec.explorationPulls * K then rewardPrefix ⟨t, ht⟩ else 0

/-- Taking the exploration prefix after extension recovers the original prefix. -/
@[simp] theorem realExplorationRewardPrefix_realRewardTraceOfExplorationPrefix
    {K : Nat} (spec : ETC.Spec K)
    (rewardPrefix : Fin (spec.explorationPulls * K) -> Real) :
    ETC.realExplorationRewardPrefix spec
        (ETC.realRewardTraceOfExplorationPrefix spec rewardPrefix) =
      rewardPrefix := by
  funext t
  simp [ETC.realExplorationRewardPrefix,
    ETC.realRewardTraceOfExplorationPrefix, t.isLt]

/-- Prefix extraction from a Real reward trace is measurable. -/
theorem measurable_realExplorationRewardPrefix {K : Nat} (spec : ETC.Spec K) :
    Measurable (ETC.realExplorationRewardPrefix spec) := by
  exact measurable_pi_lambda _ (fun t => measurable_pi_apply t.1)

/-- Zero extension of a finite Real reward prefix is measurable. -/
theorem measurable_realRewardTraceOfExplorationPrefix {K : Nat}
    (spec : ETC.Spec K) :
    Measurable (ETC.realRewardTraceOfExplorationPrefix spec) := by
  apply measurable_pi_lambda
  intro t
  by_cases ht : t < spec.explorationPulls * K
  · simpa [ETC.realRewardTraceOfExplorationPrefix, ht] using
      (measurable_pi_apply (⟨t, ht⟩ : Fin (spec.explorationPulls * K)))
  · simp [ETC.realRewardTraceOfExplorationPrefix, ht]

/-- Timewise measurable rewards give a measurable finite exploration prefix. -/
theorem measurable_realExplorationRewardPrefix_comp
    {Omega : Type u} {K : Nat} [MeasurableSpace Omega]
    (spec : ETC.Spec K) (reward : Omega -> RewardTrace Real)
    (hreward : forall t, Measurable (fun omega => reward omega t)) :
    Measurable (fun omega =>
      ETC.realExplorationRewardPrefix spec (reward omega)) := by
  exact measurable_pi_lambda _ (fun t => hreward t.1)

/-- Reward sums agree when the reward traces agree before the horizon. -/
theorem sumRewards_eq_of_eq_on_lt
    {Action Reward : Type} [DecidableEq Action] [AddCommMonoid Reward]
    (action : ActionTrace Action) (reward reward' : RewardTrace Reward)
    (a : Action) (n : Nat)
    (hreward : forall t, t < n -> reward t = reward' t) :
    sumRewards action reward a n = sumRewards action reward' a n := by
  rw [sumRewards_eq_finset_filter_sum, sumRewards_eq_finset_filter_sum]
  apply Finset.sum_congr rfl
  intro t ht
  exact hreward t (Finset.mem_range.mp (Finset.mem_filter.mp ht).1)

/-- Native Real exploration means depend only on the exploration reward prefix. -/
theorem realEmpMeanAtExploration_eq_of_eq_on_exploration
    {K : Nat} (spec : ETC.Spec K) (baseCommitArm : Fin K)
    (reward reward' : RewardTrace Real)
    (hreward : forall t, t < spec.explorationPulls * K ->
      reward t = reward' t) (a : Fin K) :
    ETC.realEmpMeanAtExploration spec baseCommitArm reward a =
      ETC.realEmpMeanAtExploration spec baseCommitArm reward' a := by
  rw [ETC.realEmpMeanAtExploration_eq_sumRewards_div_explorationPulls,
    ETC.realEmpMeanAtExploration_eq_sumRewards_div_explorationPulls]
  congr 1
  exact ETC.sumRewards_eq_of_eq_on_lt
    (ETC.actionWithCommit spec baseCommitArm) reward reward' a
    (spec.explorationPulls * K) hreward

/-- Native Real empirical argmax commit depends only on exploration rewards. -/
theorem realExplorationArgmaxCommit_eq_of_eq_on_exploration
    {K : Nat} (spec : ETC.Spec K) (baseCommitArm : Fin K)
    (reward reward' : RewardTrace Real)
    (hreward : forall t, t < spec.explorationPulls * K ->
      reward t = reward' t) :
    ETC.realExplorationArgmaxCommit spec baseCommitArm reward =
      ETC.realExplorationArgmaxCommit spec baseCommitArm reward' := by
  unfold ETC.realExplorationArgmaxCommit
  congr 1
  funext a
  exact ETC.realEmpMeanAtExploration_eq_of_eq_on_exploration
    spec baseCommitArm reward reward' hreward a

/-- Extending the extracted prefix does not change the ETC commit arm. -/
theorem realExplorationArgmaxCommit_realRewardTraceOf_prefix_eq
    {K : Nat} (spec : ETC.Spec K) (baseCommitArm : Fin K)
    (trajectory : RewardTrace Real) :
    ETC.realExplorationArgmaxCommit spec baseCommitArm trajectory =
      ETC.realExplorationArgmaxCommit spec baseCommitArm
        (ETC.realRewardTraceOfExplorationPrefix spec
          (ETC.realExplorationRewardPrefix spec trajectory)) := by
  apply ETC.realExplorationArgmaxCommit_eq_of_eq_on_exploration
  intro t ht
  simp [ETC.realRewardTraceOfExplorationPrefix,
    ETC.realExplorationRewardPrefix, ht]

/-- Extending the extracted prefix does not change the native Real ETC action. -/
theorem realExplorationArgmaxAction_realRewardTraceOf_prefix_eq
    {K : Nat} (spec : ETC.Spec K) (baseCommitArm : Fin K)
    (trajectory : RewardTrace Real) :
    ETC.realExplorationArgmaxAction spec baseCommitArm trajectory =
      ETC.realExplorationArgmaxAction spec baseCommitArm
        (ETC.realRewardTraceOfExplorationPrefix spec
          (ETC.realExplorationRewardPrefix spec trajectory)) := by
  simp only [ETC.realExplorationArgmaxAction]
  rw [ETC.realExplorationArgmaxCommit_realRewardTraceOf_prefix_eq]

/-- Kernel regret is measurable from a timewise measurable finite-arm action. -/
theorem measurable_realKernelRegret_of_forall_measurable_action
    {Omega : Type u} {K : Nat} [MeasurableSpace Omega]
    (nu : ProbabilityTheory.Kernel (Fin K) Real)
    (action : Omega -> ActionTrace (Fin K))
    (haction : forall t, Measurable (fun omega => action omega t))
    (n : Nat) :
    Measurable (fun omega => realKernelRegret nu (action omega) n) := by
  rw [show (fun omega => realKernelRegret nu (action omega) n) =
      (fun omega => (Finset.range n).sum
        (fun t => realKernelGap nu (action omega t))) by
    funext omega
    exact realKernelRegret_eq_finset_sum_gap nu (action omega) n]
  refine Finset.measurable_sum _ ?_
  intro t _ht
  exact (measurable_of_finite (realKernelGap nu)).comp (haction t)

/-- The finite-prefix functional whose value is native Real ETC kernel regret. -/
noncomputable def realKernelRegretOfExplorationPrefix
    {K : Nat} (spec : ETC.Spec K) (nu : ProbabilityTheory.Kernel (Fin K) Real)
    (baseCommitArm : Fin K) (n : Nat)
    (rewardPrefix : Fin (spec.explorationPulls * K) -> Real) : Real :=
  realKernelRegret nu
    (ETC.realExplorationArgmaxAction spec baseCommitArm
      (ETC.realRewardTraceOfExplorationPrefix spec rewardPrefix)) n

/-- The finite-prefix kernel-regret functional is measurable. -/
theorem measurable_realKernelRegretOfExplorationPrefix
    {K : Nat} (spec : ETC.Spec K)
    (nu : ProbabilityTheory.Kernel (Fin K) Real)
    (baseCommitArm : Fin K) (n : Nat) :
    Measurable
      (ETC.realKernelRegretOfExplorationPrefix spec nu baseCommitArm n) := by
  let extension := ETC.realRewardTraceOfExplorationPrefix spec
  let commit := fun rewardPrefix : Fin (spec.explorationPulls * K) -> Real =>
    ETC.realExplorationArgmaxCommit spec baseCommitArm (extension rewardPrefix)
  let action := fun rewardPrefix : Fin (spec.explorationPulls * K) -> Real =>
    ETC.actionWithCommit spec (commit rewardPrefix)
  have hextension : Measurable extension :=
    ETC.measurable_realRewardTraceOfExplorationPrefix spec
  have hcommit : Measurable commit := by
    exact ETC.measurable_realExplorationArgmaxCommit
      spec baseCommitArm extension (fun t => (measurable_pi_apply t).comp hextension)
  have haction : forall t, Measurable (fun rewardPrefix => action rewardPrefix t) := by
    intro t
    exact (measurable_of_countable
      (fun arm : Fin K => ETC.actionWithCommit spec arm t)).comp hcommit
  simpa [ETC.realKernelRegretOfExplorationPrefix, extension, commit, action,
    ETC.realExplorationArgmaxAction] using
    (ETC.measurable_realKernelRegret_of_forall_measurable_action
      nu action haction n)

/-- Native Real ETC kernel regret factors through the exploration prefix. -/
theorem realKernelRegret_realExplorationArgmaxAction_eq_prefixFunctional
    {K : Nat} (spec : ETC.Spec K)
    (nu : ProbabilityTheory.Kernel (Fin K) Real)
    (baseCommitArm : Fin K) (trajectory : RewardTrace Real) (n : Nat) :
    realKernelRegret nu
        (ETC.realExplorationArgmaxAction spec baseCommitArm trajectory) n =
      ETC.realKernelRegretOfExplorationPrefix spec nu baseCommitArm n
        (ETC.realExplorationRewardPrefix spec trajectory) := by
  rw [ETC.realKernelRegretOfExplorationPrefix]
  rw [ETC.realExplorationArgmaxAction_realRewardTraceOf_prefix_eq]

/-- Kernel regret agrees when two action traces agree before the horizon. -/
theorem realKernelRegret_eq_of_action_eq_on_lt
    {K : Nat} (nu : ProbabilityTheory.Kernel (Fin K) Real)
    (action action' : ActionTrace (Fin K)) (n : Nat)
    (haction : forall t, t < n -> action t = action' t) :
    realKernelRegret nu action n = realKernelRegret nu action' n := by
  rw [realKernelRegret_eq_finset_sum_gap,
    realKernelRegret_eq_finset_sum_gap]
  apply Finset.sum_congr rfl
  intro t ht
  rw [haction t (Finset.mem_range.mp ht)]

/-- A constant-kernel Ionescu-Tulcea trajectory is the infinite product law. -/
theorem real_trajMeasure_const_eq_infinitePi
    (coordLaw : Nat -> Measure Real)
    [forall t, IsProbabilityMeasure (coordLaw t)] :
    ProbabilityTheory.Kernel.trajMeasure (coordLaw 0)
        (fun i => ProbabilityTheory.Kernel.const
          ((j : Finset.Iic i) -> Real) (coordLaw (i + 1))) =
      Measure.infinitePi coordLaw := by
  calc
    ProbabilityTheory.Kernel.trajMeasure (coordLaw 0)
        (fun i => ProbabilityTheory.Kernel.const
          ((j : Finset.Iic i) -> Real) (coordLaw (i + 1))) =
      Measure.infinitePiNat coordLaw := by
        rw [ProbabilityTheory.Kernel.trajMeasure, Measure.infinitePiNat]
        congr 1
        exact
          ((MeasureTheory.measurePreserving_piUnique
            (fun j : Finset.Iic 0 => coordLaw j)).symm
              (MeasurableEquiv.piUnique (fun _j : Finset.Iic 0 => Real))).map_eq
    _ = Measure.infinitePi coordLaw := by
      exact (Measure.isProjectiveLimit_infinitePiNat coordLaw).unique
        (Measure.isProjectiveLimit_infinitePi coordLaw)

/-- Convert the inclusive history through `horizon - 1` to a `Fin horizon` prefix. -/
def realExplorationPrefixOfFiniteRewardHistory
    {K : Nat} (spec : ETC.Spec K)
    (history : History.FiniteRewardHistory Real
      (spec.explorationPulls * K - 1)) :
    Fin (spec.explorationPulls * K) -> Real :=
  fun t => history
    ⟨t.1, Finset.mem_Iic.mpr (Nat.le_pred_of_lt t.2)⟩

/-- The inclusive-history to `Fin` exploration-prefix conversion is measurable. -/
theorem measurable_realExplorationPrefixOfFiniteRewardHistory
    {K : Nat} (spec : ETC.Spec K) :
    Measurable (ETC.realExplorationPrefixOfFiniteRewardHistory spec) := by
  exact measurable_pi_lambda _ (fun t => measurable_pi_apply
    (⟨t.1, Finset.mem_Iic.mpr (Nat.le_pred_of_lt t.2)⟩ :
      Finset.Iic (spec.explorationPulls * K - 1)))

/-- Conversion of a trace's inclusive history is its `Fin` exploration prefix. -/
theorem realExplorationPrefixOfFiniteRewardHistory_of_trace
    {K : Nat} (spec : ETC.Spec K) (trajectory : RewardTrace Real) :
    ETC.realExplorationPrefixOfFiniteRewardHistory spec
        (History.finiteRewardHistoryOfTrace trajectory
          (spec.explorationPulls * K - 1)) =
      ETC.realExplorationRewardPrefix spec trajectory := by
  rfl

/--
Equality of finite exploration-prefix laws transports the canonical native
Real ETC exact regret bound to an arbitrary reward process.
-/
theorem integral_realKernelRegret_realExplorationArgmaxAction_le_exact_sum_of_prefixLaw_eq_infinitePi
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
    (reward : Omega -> RewardTrace Real)
    (hreward : forall t, Measurable (fun omega => reward omega t))
    (hprefixLaw :
      Measure.map
          (fun omega => ETC.realExplorationRewardPrefix spec (reward omega)) mu =
        Measure.map (ETC.realExplorationRewardPrefix spec)
          (Measure.infinitePi (fun t : Nat => nu (ETC.exploreArm spec t)))) :
    let best := ETC.realKernelBestArm spec.hK nu
    integral mu (fun omega =>
        realKernelRegret nu
          (ETC.realExplorationArgmaxAction spec best (reward omega)) n) <=
      (Finset.univ : Finset (Fin K)).sum (fun arm =>
        realKernelGap nu arm *
          ((spec.explorationPulls : Real) +
            ((n - K * spec.explorationPulls : Nat) : Real) *
              Real.exp
                (-(spec.explorationPulls : Real) *
                  (realKernelGap nu arm) ^ 2 /
                    (4 * (sigma2 : Real))))) := by
  dsimp only
  let best := ETC.realKernelBestArm spec.hK nu
  let coordLaw := fun t : Nat => nu (ETC.exploreArm spec t)
  let canonicalMu := Measure.infinitePi coordLaw
  let prefixFunctional :=
    ETC.realKernelRegretOfExplorationPrefix spec nu best n
  have hprefix_external : Measurable (fun omega =>
      ETC.realExplorationRewardPrefix spec (reward omega)) :=
    ETC.measurable_realExplorationRewardPrefix_comp spec reward hreward
  have hprefix_canonical : Measurable
      (ETC.realExplorationRewardPrefix spec) :=
    ETC.measurable_realExplorationRewardPrefix spec
  have hfunctional : Measurable prefixFunctional :=
    ETC.measurable_realKernelRegretOfExplorationPrefix spec nu best n
  have hintegral_prefix :
      integral mu (fun omega => prefixFunctional
          (ETC.realExplorationRewardPrefix spec (reward omega))) =
        integral canonicalMu (fun trajectory : RewardTrace Real =>
          prefixFunctional (ETC.realExplorationRewardPrefix spec trajectory)) := by
    calc
      integral mu (fun omega => prefixFunctional
          (ETC.realExplorationRewardPrefix spec (reward omega))) =
        integral (Measure.map
          (fun omega => ETC.realExplorationRewardPrefix spec (reward omega)) mu)
          prefixFunctional := by
            exact (integral_map hprefix_external.aemeasurable
              hfunctional.aestronglyMeasurable).symm
      _ = integral (Measure.map (ETC.realExplorationRewardPrefix spec)
          canonicalMu) prefixFunctional := by
            rw [show Measure.map
                (fun omega => ETC.realExplorationRewardPrefix spec (reward omega)) mu =
              Measure.map (ETC.realExplorationRewardPrefix spec) canonicalMu by
                simpa [canonicalMu, coordLaw] using hprefixLaw]
      _ = integral canonicalMu (fun trajectory : RewardTrace Real =>
          prefixFunctional (ETC.realExplorationRewardPrefix spec trajectory)) := by
            exact integral_map hprefix_canonical.aemeasurable
              hfunctional.aestronglyMeasurable
  calc
    integral mu (fun omega =>
        realKernelRegret nu
          (ETC.realExplorationArgmaxAction spec best (reward omega)) n) =
      integral mu (fun omega => prefixFunctional
        (ETC.realExplorationRewardPrefix spec (reward omega))) := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall (fun omega =>
            ETC.realKernelRegret_realExplorationArgmaxAction_eq_prefixFunctional
              spec nu best (reward omega) n)
    _ = integral canonicalMu (fun trajectory : RewardTrace Real =>
        prefixFunctional (ETC.realExplorationRewardPrefix spec trajectory)) :=
      hintegral_prefix
    _ = integral canonicalMu (fun trajectory : RewardTrace Real =>
        realKernelRegret nu
          (ETC.realExplorationArgmaxAction spec best trajectory) n) := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall (fun trajectory =>
            (ETC.realKernelRegret_realExplorationArgmaxAction_eq_prefixFunctional
              spec nu best trajectory n).symm)
    _ <= (Finset.univ : Finset (Fin K)).sum (fun arm =>
        realKernelGap nu arm *
          ((spec.explorationPulls : Real) +
            ((n - K * spec.explorationPulls : Nat) : Real) *
              Real.exp
                (-(spec.explorationPulls : Real) *
                  (realKernelGap nu arm) ^ 2 /
                    (4 * (sigma2 : Real))))) := by
          simpa [canonicalMu, coordLaw, best] using
            (ETC.integral_realKernelRegret_realExplorationArgmaxAction_le_exact_sum_of_infinitePi_kernel
              spec nu sigma2 hsubG hm n hn)

/--
External-action version of the finite-prefix law transport theorem. The two
remaining upstream obligations are explicit: finite-prefix reward law equality
and almost-sure equality with the local native Real ETC action.
-/
theorem integral_realKernelRegret_externalAction_le_exact_sum_of_prefixLaw_eq_infinitePi
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
    (hreward : forall t, Measurable (fun omega => reward omega t))
    (hprefixLaw :
      Measure.map
          (fun omega => ETC.realExplorationRewardPrefix spec (reward omega)) mu =
        Measure.map (ETC.realExplorationRewardPrefix spec)
          (Measure.infinitePi (fun t : Nat => nu (ETC.exploreArm spec t))))
    (haction : Filter.Eventually
      (fun omega => forall t, t < n ->
        action omega t =
          ETC.realExplorationArgmaxAction spec
            (ETC.realKernelBestArm spec.hK nu) (reward omega) t)
      (ae mu)) :
    integral mu (fun omega => realKernelRegret nu (action omega) n) <=
      (Finset.univ : Finset (Fin K)).sum (fun arm =>
        realKernelGap nu arm *
          ((spec.explorationPulls : Real) +
            ((n - K * spec.explorationPulls : Nat) : Real) *
              Real.exp
                (-(spec.explorationPulls : Real) *
                  (realKernelGap nu arm) ^ 2 /
                    (4 * (sigma2 : Real))))) := by
  calc
    integral mu (fun omega => realKernelRegret nu (action omega) n) =
      integral mu (fun omega => realKernelRegret nu
        (ETC.realExplorationArgmaxAction spec
          (ETC.realKernelBestArm spec.hK nu) (reward omega)) n) := by
            apply integral_congr_ae
            filter_upwards [haction] with omega haction_eq
            exact ETC.realKernelRegret_eq_of_action_eq_on_lt
              nu (action omega)
              (ETC.realExplorationArgmaxAction spec
                (ETC.realKernelBestArm spec.hK nu) (reward omega))
              n haction_eq
    _ <= (Finset.univ : Finset (Fin K)).sum (fun arm =>
        realKernelGap nu arm *
          ((spec.explorationPulls : Real) +
            ((n - K * spec.explorationPulls : Nat) : Real) *
              Real.exp
                (-(spec.explorationPulls : Real) *
                  (realKernelGap nu arm) ^ 2 /
                    (4 * (sigma2 : Real))))) :=
      ETC.integral_realKernelRegret_realExplorationArgmaxAction_le_exact_sum_of_prefixLaw_eq_infinitePi
        mu spec nu sigma2 hsubG hm n hn reward hreward hprefixLaw

/--
External native Real exact ETC regret from the scheduled exploration-arm
initial marginal and successor conditional reward laws. This is the direct
law surface needed before mapping an upstream `IsAlgEnvSeq` witness.
-/
theorem integral_realKernelRegret_externalAction_le_exact_sum_of_initial_map_eq_condDistrib
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
    (hreward : forall t, Measurable (fun omega => reward omega t))
    (hzero : Measure.map (fun omega => reward omega 0) mu =
      nu (ETC.exploreArm spec 0))
    (hcond : forall i, i < spec.explorationPulls * K - 1 ->
      ProbabilityTheory.condDistrib
          (fun omega => reward omega (i + 1))
          (fun omega =>
            History.finiteRewardHistoryOfTrace (reward omega) i)
          mu =ᵐ[mu.map (fun omega =>
            History.finiteRewardHistoryOfTrace (reward omega) i)]
        ProbabilityTheory.Kernel.const
          (History.FiniteRewardHistory Real i)
          (nu (ETC.exploreArm spec (i + 1))))
    (haction : Filter.Eventually
      (fun omega => forall t, t < n ->
        action omega t =
          ETC.realExplorationArgmaxAction spec
            (ETC.realKernelBestArm spec.hK nu) (reward omega) t)
      (ae mu)) :
    integral mu (fun omega => realKernelRegret nu (action omega) n) <=
      (Finset.univ : Finset (Fin K)).sum (fun arm =>
        realKernelGap nu arm *
          ((spec.explorationPulls : Real) +
            ((n - K * spec.explorationPulls : Nat) : Real) *
              Real.exp
                (-(spec.explorationPulls : Real) *
                  (realKernelGap nu arm) ^ 2 /
                    (4 * (sigma2 : Real))))) := by
  let coordLaw := fun t : Nat => nu (ETC.exploreArm spec t)
  let stepKernel := fun i => ProbabilityTheory.Kernel.const
    (History.FiniteRewardHistory Real i) (coordLaw (i + 1))
  letI : forall t, IsProbabilityMeasure (coordLaw t) := fun _t => inferInstance
  let trajMeasure := ProbabilityTheory.Kernel.trajMeasure
    (X := fun _ : Nat => Real) (coordLaw 0) stepKernel
  let historyMap : RewardTrace Real ->
      History.FiniteRewardHistory Real (spec.explorationPulls * K - 1) :=
    fun trajectory => History.finiteRewardHistoryOfTrace trajectory
      (spec.explorationPulls * K - 1)
  let convert := ETC.realExplorationPrefixOfFiniteRewardHistory spec
  have hhistory_external : Measurable (fun omega => historyMap (reward omega)) := by
    exact History.measurable_finiteRewardHistoryOfTrace reward hreward
      (spec.explorationPulls * K - 1)
  have hhistory_canonical : Measurable historyMap := by
    exact History.measurable_finiteRewardHistoryOfTrace
      (fun trajectory : RewardTrace Real => trajectory)
      (fun t => measurable_pi_apply t)
      (spec.explorationPulls * K - 1)
  have hconvert : Measurable convert :=
    ETC.measurable_realExplorationPrefixOfFiniteRewardHistory spec
  have hprefix_history :
      Measure.map (fun omega => historyMap (reward omega)) mu =
        Measure.map historyMap trajMeasure := by
    exact RewardKernel.rewardTrace_prefix_map_eq_trajMeasure_of_condDistrib
      mu (coordLaw 0) reward hreward stepKernel
      (by simpa [coordLaw] using hzero)
      (spec.explorationPulls * K - 1)
      (by
        intro i hi
        simpa [stepKernel, coordLaw] using hcond i hi)
  have hprefix_converted := congrArg (Measure.map convert) hprefix_history
  rw [Measure.map_map hconvert hhistory_external,
    Measure.map_map hconvert hhistory_canonical] at hprefix_converted
  have hcomp_external :
      convert ∘ (fun omega => historyMap (reward omega)) =
        fun omega => ETC.realExplorationRewardPrefix spec (reward omega) := by
    funext omega
    exact ETC.realExplorationPrefixOfFiniteRewardHistory_of_trace
      spec (reward omega)
  have hcomp_canonical : convert ∘ historyMap =
      ETC.realExplorationRewardPrefix spec := by
    funext trajectory
    exact ETC.realExplorationPrefixOfFiniteRewardHistory_of_trace
      spec trajectory
  have htraj : trajMeasure = Measure.infinitePi coordLaw := by
    simpa [trajMeasure, stepKernel] using
      (ETC.real_trajMeasure_const_eq_infinitePi coordLaw)
  rw [hcomp_external, hcomp_canonical, htraj] at hprefix_converted
  exact
    ETC.integral_realKernelRegret_externalAction_le_exact_sum_of_prefixLaw_eq_infinitePi
      mu spec nu sigma2 hsubG hm n hn action reward hreward
      (by simpa [coordLaw] using hprefix_converted) haction

end ETC
end BanditRLProof
