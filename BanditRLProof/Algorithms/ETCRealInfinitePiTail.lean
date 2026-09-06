import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring
import BanditRLProof.Algorithms.ETCRealEmpiricalMean
import BanditRLProof.ConcentrationSubGaussian
import BanditRLProof.IndependenceFoundation
import BanditRLProof.RealKernelRegretPullCount

/-!
# Native Real ETC concentration under the canonical infinite product law

This module proves the exact single-arm ETC wrong-commit tail for a native
Real reward kernel under the canonical independent-coordinate product law.
It then consumes that tail in the expected pull-count and finite-sum kernel
regret identities. Transport from an arbitrary external algorithm/environment
sequence remains a downstream law-identification obligation.
-/

namespace BanditRLProof

open MeasureTheory

namespace ETC

/-- A finite maximizer of the identity-integral means of a Real reward kernel. -/
noncomputable def realKernelBestArm {K : Nat} (hK : 0 < K)
    (nu : ProbabilityTheory.Kernel (Fin K) Real) : Fin K :=
  ETC.realArgmaxCommit hK (realKernelMean nu)

/-- The selected kernel best arm dominates every arm mean. -/
theorem realKernelMean_le_realKernelBestArm {K : Nat} (hK : 0 < K)
    (nu : ProbabilityTheory.Kernel (Fin K) Real) (a : Fin K) :
    realKernelMean nu a <=
      realKernelMean nu (ETC.realKernelBestArm hK nu) := by
  exact ETC.realArgmaxCommit_spec hK (realKernelMean nu) a

/-- The finite supremum of kernel means is attained at `realKernelBestArm`. -/
theorem ciSup_realKernelMean_eq_realKernelBestArm {K : Nat} (hK : 0 < K)
    (nu : ProbabilityTheory.Kernel (Fin K) Real) :
    (⨆ a : Fin K, realKernelMean nu a) =
      realKernelMean nu (ETC.realKernelBestArm hK nu) := by
  letI : Nonempty (Fin K) := ⟨Fin.mk 0 hK⟩
  apply le_antisymm
  · exact ciSup_le (fun a => ETC.realKernelMean_le_realKernelBestArm hK nu a)
  · exact le_ciSup (f := realKernelMean nu) (by simp)
      (ETC.realKernelBestArm hK nu)

/-- Kernel gap is the selected best mean minus the queried arm mean. -/
theorem realKernelGap_eq_realKernelBestArm_sub {K : Nat} (hK : 0 < K)
    (nu : ProbabilityTheory.Kernel (Fin K) Real) (a : Fin K) :
    realKernelGap nu a =
      realKernelMean nu (ETC.realKernelBestArm hK nu) -
        realKernelMean nu a := by
  rw [realKernelGap, realMeanGap,
    ETC.ciSup_realKernelMean_eq_realKernelBestArm hK nu]

/-- Native Real centered candidate-minus-best reward difference. -/
noncomputable def realCenteredPairwiseRewardDiff
    {Omega : Type u} {K : Nat}
    (spec : ETC.Spec K) (mean : Fin K -> Real) (best commitArm : Fin K)
    (reward : Omega -> RewardTrace Real) (a : Fin K)
    (t : Nat) (omega : Omega) : Real :=
  (if ETC.actionWithCommit spec commitArm t = a then
      reward omega t - mean a else 0) +
    (if ETC.actionWithCommit spec commitArm t = best then
      mean best - reward omega t else 0)

/-- Native Real threshold of the centered pairwise exploration event. -/
noncomputable def realCenteredPairwiseGapThreshold
    {K : Nat} (spec : ETC.Spec K) (mean : Fin K -> Real)
    (best a : Fin K) : Real :=
  (spec.explorationPulls : Real) * (mean best - mean a)

/-- Variance proxy charged at candidate and best-arm exploration coordinates. -/
noncomputable def realCenteredPairwiseRewardDiffVarianceProxy
    {K : Nat} (spec : ETC.Spec K) (best commitArm : Fin K)
    (cReward : Fin K -> Nat -> NNReal) (a : Fin K) (t : Nat) : NNReal :=
  if ETC.actionWithCommit spec commitArm t = a then cReward a t
  else if ETC.actionWithCommit spec commitArm t = best then cReward best t
  else 0

/-- Selected centered Real rewards equal reward sum minus count times mean. -/
theorem real_selectedSubMean_sum_eq_sumRewards_sub_pullCount_mul
    {Action : Type} [DecidableEq Action]
    (action : ActionTrace Action) (reward : RewardTrace Real)
    (a : Action) (n : Nat) (mu : Real) :
    (Finset.range n).sum
        (fun t => if action t = a then reward t - mu else 0) =
      sumRewards action reward a n - (pullCount action a n : Real) * mu := by
  classical
  calc
    (Finset.range n).sum
        (fun t => if action t = a then reward t - mu else 0) =
      ((Finset.range n).filter (fun t => action t = a)).sum
        (fun t => reward t - mu) := by rw [Finset.sum_filter]
    _ = ((Finset.range n).filter (fun t => action t = a)).sum reward -
        ((Finset.range n).filter (fun t => action t = a)).sum
          (fun _t => mu) := by rw [Finset.sum_sub_distrib]
    _ = sumRewards action reward a n -
        (((Finset.range n).filter (fun t => action t = a)).card : Real) * mu := by
          rw [← sumRewards_eq_finset_filter_sum]
          rw [Finset.sum_const]
          simp [nsmul_eq_mul, mul_comm]
    _ = sumRewards action reward a n - (pullCount action a n : Real) * mu := by
          rw [pullCount_eq_finset_filter_card]

/-- Selected negative centered Real rewards equal count times mean minus sum. -/
theorem real_meanSubSelected_sum_eq_pullCount_mul_sub_sumRewards
    {Action : Type} [DecidableEq Action]
    (action : ActionTrace Action) (reward : RewardTrace Real)
    (a : Action) (n : Nat) (mu : Real) :
    (Finset.range n).sum
        (fun t => if action t = a then mu - reward t else 0) =
      (pullCount action a n : Real) * mu - sumRewards action reward a n := by
  classical
  calc
    (Finset.range n).sum
        (fun t => if action t = a then mu - reward t else 0) =
      ((Finset.range n).filter (fun t => action t = a)).sum
        (fun t => mu - reward t) := by rw [Finset.sum_filter]
    _ = ((Finset.range n).filter (fun t => action t = a)).sum
          (fun _t => mu) -
        ((Finset.range n).filter (fun t => action t = a)).sum reward := by
          rw [Finset.sum_sub_distrib]
    _ = (((Finset.range n).filter (fun t => action t = a)).card : Real) * mu -
        sumRewards action reward a n := by
          have hsum :
              ((Finset.range n).filter (fun t => action t = a)).sum reward =
                sumRewards action reward a n :=
            (sumRewards_eq_finset_filter_sum
              (action := action) (reward := reward) (a := a) (t := n)).symm
          rw [hsum]
          rw [Finset.sum_const]
          simp [nsmul_eq_mul, mul_comm]
    _ = (pullCount action a n : Real) * mu -
        sumRewards action reward a n := by
          rw [pullCount_eq_finset_filter_card]

/-- Equal exploration counts turn a raw reward comparison into a centered sum. -/
theorem real_sumRewards_le_imp_centered_pairwise_sum_ge
    {Action : Type} [DecidableEq Action]
    (action : ActionTrace Action) (reward : RewardTrace Real)
    (a b : Action) (n m : Nat) (muA muB : Real)
    (hcount_a : pullCount action a n = m)
    (hcount_b : pullCount action b n = m)
    (hraw : sumRewards action reward b n <= sumRewards action reward a n) :
    (m : Real) * (muB - muA) <=
      (Finset.range n).sum (fun t =>
        (if action t = a then reward t - muA else 0) +
        (if action t = b then muB - reward t else 0)) := by
  classical
  rw [Finset.sum_add_distrib]
  rw [ETC.real_selectedSubMean_sum_eq_sumRewards_sub_pullCount_mul]
  rw [ETC.real_meanSubSelected_sum_eq_pullCount_mul_sub_sumRewards]
  rw [hcount_a, hcount_b]
  have hdiff : 0 <=
      sumRewards action reward a n - sumRewards action reward b n :=
    sub_nonneg.mpr hraw
  calc
    (m : Real) * (muB - muA) = 0 + (m : Real) * (muB - muA) := by ring
    _ <= (sumRewards action reward a n - sumRewards action reward b n) +
        (m : Real) * (muB - muA) := by gcongr
    _ = (sumRewards action reward a n - (m : Real) * muA) +
        ((m : Real) * muB - sumRewards action reward b n) := by ring

/-- A native Real commit fiber is contained in its centered pairwise tail event. -/
theorem realExplorationArgmaxCommit_eq_arm_event_subset_centeredPairwise_sum_event
    {Omega : Type u} {K : Nat}
    (spec : ETC.Spec K) (mean : Fin K -> Real) (best baseCommitArm : Fin K)
    (reward : Omega -> RewardTrace Real) (a : Fin K)
    (hm : 0 < spec.explorationPulls) :
    Set.Subset
      {omega | ETC.realExplorationArgmaxCommit spec baseCommitArm
          (reward omega) = a}
      {omega | ETC.realCenteredPairwiseGapThreshold spec mean best a <=
        (Finset.range (spec.explorationPulls * K)).sum (fun t =>
          ETC.realCenteredPairwiseRewardDiff
            spec mean best baseCommitArm reward a t omega)} := by
  intro omega hcommit
  have hscore := ETC.realArgmaxCommit_spec spec.hK
    (fun b => ETC.realEmpMeanAtExploration spec baseCommitArm (reward omega) b)
    best
  rw [show ETC.realArgmaxCommit spec.hK
      (fun b => ETC.realEmpMeanAtExploration spec baseCommitArm
        (reward omega) b) = a by exact hcommit] at hscore
  rw [ETC.realEmpMeanAtExploration_eq_sumRewards_div_explorationPulls,
    ETC.realEmpMeanAtExploration_eq_sumRewards_div_explorationPulls] at hscore
  have hmReal : 0 < (spec.explorationPulls : Real) := by exact_mod_cast hm
  have hraw :
      sumRewards (ETC.actionWithCommit spec baseCommitArm) (reward omega) best
          (spec.explorationPulls * K) <=
        sumRewards (ETC.actionWithCommit spec baseCommitArm) (reward omega) a
          (spec.explorationPulls * K) :=
    (div_le_div_iff_of_pos_right hmReal).mp hscore
  exact ETC.real_sumRewards_le_imp_centered_pairwise_sum_ge
    (ETC.actionWithCommit spec baseCommitArm) (reward omega) a best
    (spec.explorationPulls * K) spec.explorationPulls (mean a) (mean best)
    (ETC.pullCount_actionWithCommit_explorationPulls_mul_K_eq
      spec baseCommitArm a)
    (ETC.pullCount_actionWithCommit_explorationPulls_mul_K_eq
      spec baseCommitArm best)
    hraw

/-- Coordinate independence survives the native Real pairwise transform. -/
theorem iIndepFun_realCenteredPairwiseRewardDiff_of_iIndepFun_reward
    {Omega : Type u} {K : Nat} [MeasurableSpace Omega]
    (mu : Measure Omega) (spec : ETC.Spec K) (mean : Fin K -> Real)
    (best commitArm : Fin K) (reward : Omega -> RewardTrace Real)
    (h_reward_indep : ProbabilityTheory.iIndepFun
      (fun t omega => reward omega t) mu) (a : Fin K) :
    ProbabilityTheory.iIndepFun
      (fun t omega => ETC.realCenteredPairwiseRewardDiff
        spec mean best commitArm reward a t omega) mu := by
  let transform : Nat -> Real -> Real := fun t r =>
    (if ETC.actionWithCommit spec commitArm t = a then r - mean a else 0) +
      (if ETC.actionWithCommit spec commitArm t = best then mean best - r else 0)
  have htransform : forall t, Measurable (transform t) := by
    intro t
    simp only [transform]
    split_ifs <;> fun_prop
  have hcomp := h_reward_indep.comp transform htransform
  simpa [transform, ETC.realCenteredPairwiseRewardDiff] using hcomp

/-- Per-coordinate centered sub-Gaussianity transfers to the pairwise summand. -/
theorem realCenteredPairwiseRewardDiff_hasSubgaussianMGF_of_centeredReward
    {Omega : Type u} {K : Nat} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsZeroOrProbabilityMeasure mu]
    (spec : ETC.Spec K) (mean : Fin K -> Real) (best commitArm : Fin K)
    (reward : Omega -> RewardTrace Real) (cReward : Fin K -> Nat -> NNReal)
    (a : Fin K) (t : Nat) (hne : a ≠ best)
    (h_subG : forall b, ETC.actionWithCommit spec commitArm t = b ->
      ProbabilityTheory.HasSubgaussianMGF
        (fun omega => reward omega t - mean b) (cReward b t) mu) :
    ProbabilityTheory.HasSubgaussianMGF
      (fun omega => ETC.realCenteredPairwiseRewardDiff
        spec mean best commitArm reward a t omega)
      (ETC.realCenteredPairwiseRewardDiffVarianceProxy
        spec best commitArm cReward a t) mu := by
  classical
  by_cases ha : ETC.actionWithCommit spec commitArm t = a
  · have hnot_best : ETC.actionWithCommit spec commitArm t ≠ best := by
      intro hbest
      exact hne (ha.symm.trans hbest)
    simpa [ETC.realCenteredPairwiseRewardDiffVarianceProxy,
      ETC.realCenteredPairwiseRewardDiff, ha, hnot_best, hne] using h_subG a ha
  · by_cases hbest : ETC.actionWithCommit spec commitArm t = best
    · have hbest_ne_a : best ≠ a := Ne.symm hne
      have h := (h_subG best hbest).neg
      have htarget : ProbabilityTheory.HasSubgaussianMGF
          (fun omega => mean best - reward omega t) (cReward best t) mu := by
        refine h.congr (Filter.Eventually.of_forall (fun omega => ?_))
        simp [Pi.neg_apply, sub_eq_add_neg]
      simpa [ETC.realCenteredPairwiseRewardDiffVarianceProxy,
        ETC.realCenteredPairwiseRewardDiff, ha, hbest, hbest_ne_a] using htarget
    · have hfun :
          (fun omega => ETC.realCenteredPairwiseRewardDiff
            spec mean best commitArm reward a t omega) =
          (fun _omega => (0 : Real)) := by
        funext omega
        simp [ETC.realCenteredPairwiseRewardDiff, ha, hbest]
      rw [hfun]
      simp [ETC.realCenteredPairwiseRewardDiffVarianceProxy, ha, hbest]

/-- The constant pairwise proxy sums to exactly `2 * m * sigma2`. -/
theorem sum_realCenteredPairwiseRewardDiffVarianceProxy_const_eq_two_mul
    {K : Nat} (spec : ETC.Spec K) (best : Fin K)
    (sigma2 : NNReal) (a : Fin K) (hne : a ≠ best) :
    (Finset.range (spec.explorationPulls * K)).sum (fun t =>
        ETC.realCenteredPairwiseRewardDiffVarianceProxy
          spec best best (fun _ _ => sigma2) a t) =
      (2 : NNReal) * (spec.explorationPulls : NNReal) * sigma2 := by
  classical
  let action : ActionTrace (Fin K) := ETC.actionWithCommit spec best
  have hpoint : forall t,
      ETC.realCenteredPairwiseRewardDiffVarianceProxy
          spec best best (fun _ _ => sigma2) a t =
        (if action t = a then sigma2 else 0) +
          (if action t = best then sigma2 else 0) := by
    intro t
    by_cases ha : action t = a
    · simp [ETC.realCenteredPairwiseRewardDiffVarianceProxy, action, ha, hne]
    · by_cases hbest : action t = best
      · simp [ETC.realCenteredPairwiseRewardDiffVarianceProxy, action,
          hbest, Ne.symm hne]
      · simp [ETC.realCenteredPairwiseRewardDiffVarianceProxy, action, ha, hbest]
  have hselected : forall b : Fin K,
      (Finset.range (spec.explorationPulls * K)).sum
          (fun t => if action t = b then sigma2 else 0) =
        (spec.explorationPulls : NNReal) * sigma2 := by
    intro b
    calc
      (Finset.range (spec.explorationPulls * K)).sum
          (fun t => if action t = b then sigma2 else 0) =
        ((Finset.range (spec.explorationPulls * K)).filter
          (fun t => action t = b)).sum (fun _t => sigma2) := by
            rw [Finset.sum_filter]
      _ = (((Finset.range (spec.explorationPulls * K)).filter
          (fun t => action t = b)).card : NNReal) * sigma2 := by
            simp [nsmul_eq_mul]
      _ = (spec.explorationPulls : NNReal) * sigma2 := by
            rw [← pullCount_eq_finset_filter_card]
            simp [action,
              ETC.pullCount_actionWithCommit_explorationPulls_mul_K_eq]
  rw [Finset.sum_congr rfl (fun t _ht => hpoint t)]
  rw [Finset.sum_add_distrib, hselected a, hselected best]
  ring

/--
Exact native Real single-arm wrong-commit tail under action-matched independent
kernel coordinates.
-/
theorem real_measure_realExplorationArgmaxCommit_eq_arm_le_exp_of_infinitePi_kernel
    {K : Nat} (spec : ETC.Spec K)
    (nu : ProbabilityTheory.Kernel (Fin K) Real)
    [ProbabilityTheory.IsMarkovKernel nu]
    (sigma2 : NNReal)
    (hsubG : forall arm, ProbabilityTheory.HasSubgaussianMGF
      (fun reward => reward - realKernelMean nu arm) sigma2 (nu arm))
    (hm : 0 < spec.explorationPulls) (a : Fin K)
    (hne : a ≠ ETC.realKernelBestArm spec.hK nu) :
    let best := ETC.realKernelBestArm spec.hK nu
    let coordLaw := fun t : Nat => nu (ETC.exploreArm spec t)
    (Measure.infinitePi coordLaw).real
        {trajectory : RewardTrace Real |
          ETC.realExplorationArgmaxCommit spec best trajectory = a} <=
      Real.exp
        (-(spec.explorationPulls : Real) * (realKernelGap nu a) ^ 2 /
          (4 * (sigma2 : Real))) := by
  dsimp only
  let best := ETC.realKernelBestArm spec.hK nu
  let coordLaw := fun t : Nat => nu (ETC.exploreArm spec t)
  let mu := Measure.infinitePi coordLaw
  letI : forall t : Nat, IsProbabilityMeasure (coordLaw t) := fun _t =>
    inferInstance
  have hind_reward : ProbabilityTheory.iIndepFun
      (fun t (trajectory : RewardTrace Real) => trajectory t) mu := by
    exact IndependenceFoundation.iIndepFun_rewardTrace_infinitePi coordLaw
  have hind : ProbabilityTheory.iIndepFun
      (fun t trajectory => ETC.realCenteredPairwiseRewardDiff
        spec (realKernelMean nu) best best
        (fun trajectory : RewardTrace Real => trajectory) a t trajectory) mu :=
    ETC.iIndepFun_realCenteredPairwiseRewardDiff_of_iIndepFun_reward
      mu spec (realKernelMean nu) best best
      (fun trajectory : RewardTrace Real => trajectory) hind_reward a
  have hcoord_subG : forall t, t < spec.explorationPulls * K ->
      ProbabilityTheory.HasSubgaussianMGF
        (fun trajectory : RewardTrace Real =>
          trajectory t - realKernelMean nu
            (ETC.actionWithCommit spec best t))
        sigma2 mu := by
    intro t ht
    have haction : ETC.actionWithCommit spec best t = ETC.exploreArm spec t :=
      ETC.actionWithCommit_eq_exploreArm_of_lt spec best ht
    have hmap : Measure.map
        (fun trajectory : RewardTrace Real => trajectory t) mu = coordLaw t := by
      simpa [mu] using Measure.infinitePi_map_eval coordLaw t
    have hcoord : ProbabilityTheory.HasSubgaussianMGF
        ((fun reward : Real =>
          reward - realKernelMean nu (ETC.exploreArm spec t)) ∘
            (fun trajectory : RewardTrace Real => trajectory t))
        sigma2 mu := by
      apply ProbabilityTheory.HasSubgaussianMGF.of_map
        (Y := fun trajectory : RewardTrace Real => trajectory t)
        (X := fun reward : Real =>
          reward - realKernelMean nu (ETC.exploreArm spec t))
        (measurable_pi_apply t).aemeasurable
      rw [hmap]
      simpa [coordLaw] using hsubG (ETC.exploreArm spec t)
    simpa [Function.comp_apply, haction] using hcoord
  have hpair_subG : forall t, t ∈ Finset.range (spec.explorationPulls * K) ->
      ProbabilityTheory.HasSubgaussianMGF
        (fun trajectory : RewardTrace Real =>
          ETC.realCenteredPairwiseRewardDiff
            spec (realKernelMean nu) best best
            (fun trajectory : RewardTrace Real => trajectory) a t trajectory)
        (ETC.realCenteredPairwiseRewardDiffVarianceProxy
          spec best best (fun _ _ => sigma2) a t) mu := by
    intro t ht
    exact ETC.realCenteredPairwiseRewardDiff_hasSubgaussianMGF_of_centeredReward
      mu spec (realKernelMean nu) best best
      (fun trajectory : RewardTrace Real => trajectory)
      (fun _ _ => sigma2) a t hne
      (fun b hb => by simpa [hb] using hcoord_subG t (Finset.mem_range.mp ht))
  have hgap_nonneg : 0 <= realKernelGap nu a := by
    rw [ETC.realKernelGap_eq_realKernelBestArm_sub spec.hK nu]
    exact sub_nonneg.mpr (ETC.realKernelMean_le_realKernelBestArm spec.hK nu a)
  have hthreshold_nonneg : 0 <=
      ETC.realCenteredPairwiseGapThreshold
        spec (realKernelMean nu) best a := by
    rw [ETC.realCenteredPairwiseGapThreshold]
    exact mul_nonneg (Nat.cast_nonneg _)
      (sub_nonneg.mpr (by
        simpa [best] using ETC.realKernelMean_le_realKernelBestArm spec.hK nu a))
  have htail := Concentration.subGaussian_sum_tail_of_iIndepFun
    mu hind hpair_subG hthreshold_nonneg
  have hsubset :=
    ETC.realExplorationArgmaxCommit_eq_arm_event_subset_centeredPairwise_sum_event
      spec (realKernelMean nu) best best
      (fun trajectory : RewardTrace Real => trajectory) a hm
  have hmeasure : mu.real
      {trajectory : RewardTrace Real |
        ETC.realExplorationArgmaxCommit spec best trajectory = a} <=
      mu.real {trajectory : RewardTrace Real |
        ETC.realCenteredPairwiseGapThreshold spec (realKernelMean nu) best a <=
          (Finset.range (spec.explorationPulls * K)).sum (fun t =>
            ETC.realCenteredPairwiseRewardDiff
              spec (realKernelMean nu) best best
              (fun trajectory : RewardTrace Real => trajectory)
              a t trajectory)} :=
    measureReal_mono hsubset
  calc
    mu.real {trajectory : RewardTrace Real |
        ETC.realExplorationArgmaxCommit spec best trajectory = a} <=
      Real.exp
        (-(ETC.realCenteredPairwiseGapThreshold
              spec (realKernelMean nu) best a) ^ 2 /
          (2 * (((Finset.range (spec.explorationPulls * K)).sum
            (ETC.realCenteredPairwiseRewardDiffVarianceProxy
              spec best best (fun _ _ => sigma2) a) : NNReal) : Real))) :=
        hmeasure.trans htail
    _ = Real.exp
        (-(spec.explorationPulls : Real) * (realKernelGap nu a) ^ 2 /
          (4 * (sigma2 : Real))) := by
      congr 1
      rw [ETC.sum_realCenteredPairwiseRewardDiffVarianceProxy_const_eq_two_mul
        spec best sigma2 a hne]
      rw [ETC.realKernelGap_eq_realKernelBestArm_sub spec.hK nu a]
      simp only [ETC.realCenteredPairwiseGapThreshold, best]
      norm_num
      have hm_ne : (spec.explorationPulls : Real) ≠ 0 := by
        exact_mod_cast Nat.ne_of_gt hm
      by_cases hsigma : (sigma2 : Real) = 0
      · simp [hsigma]
      · field_simp [hm_ne, hsigma]
        ring

/-- Exact native Real per-arm expected pull-count bound under `infinitePi`. -/
theorem integral_real_pullCount_realExplorationArgmaxAction_le_exp_of_infinitePi_kernel
    {K : Nat} (spec : ETC.Spec K)
    (nu : ProbabilityTheory.Kernel (Fin K) Real)
    [ProbabilityTheory.IsMarkovKernel nu]
    (sigma2 : NNReal)
    (hsubG : forall arm, ProbabilityTheory.HasSubgaussianMGF
      (fun reward => reward - realKernelMean nu arm) sigma2 (nu arm))
    (hm : 0 < spec.explorationPulls) (a : Fin K) (n : Nat)
    (hn : K * spec.explorationPulls <= n)
    (hne : a ≠ ETC.realKernelBestArm spec.hK nu) :
    let best := ETC.realKernelBestArm spec.hK nu
    let coordLaw := fun t : Nat => nu (ETC.exploreArm spec t)
    integral (Measure.infinitePi coordLaw) (fun trajectory : RewardTrace Real =>
        (pullCount (ETC.realExplorationArgmaxAction spec best trajectory) a n : Real)) <=
      (spec.explorationPulls : Real) +
        ((n - K * spec.explorationPulls : Nat) : Real) *
          Real.exp
            (-(spec.explorationPulls : Real) * (realKernelGap nu a) ^ 2 /
              (4 * (sigma2 : Real))) := by
  dsimp only
  let best := ETC.realKernelBestArm spec.hK nu
  let coordLaw := fun t : Nat => nu (ETC.exploreArm spec t)
  letI : forall t : Nat, IsProbabilityMeasure (coordLaw t) := fun _t =>
    inferInstance
  exact
    ETC.integral_real_pullCount_realExplorationArgmaxAction_le_exploration_add_remaining_mul_of_commit_prob_le
      (Measure.infinitePi coordLaw) spec best
      (fun trajectory : RewardTrace Real => trajectory)
      (fun t => measurable_pi_apply t) a n
      (Real.exp
        (-(spec.explorationPulls : Real) * (realKernelGap nu a) ^ 2 /
          (4 * (sigma2 : Real))))
      hn
      (ETC.real_measure_realExplorationArgmaxCommit_eq_arm_le_exp_of_infinitePi_kernel
        spec nu sigma2 hsubG hm a hne)

/--
Exact LML-shaped finite-sum native Real kernel regret bound under the canonical
independent exploration-coordinate law.
-/
theorem integral_realKernelRegret_realExplorationArgmaxAction_le_exact_sum_of_infinitePi_kernel
    {K : Nat} (spec : ETC.Spec K)
    (nu : ProbabilityTheory.Kernel (Fin K) Real)
    [ProbabilityTheory.IsMarkovKernel nu]
    (sigma2 : NNReal)
    (hsubG : forall arm, ProbabilityTheory.HasSubgaussianMGF
      (fun reward => reward - realKernelMean nu arm) sigma2 (nu arm))
    (hm : 0 < spec.explorationPulls) (n : Nat)
    (hn : K * spec.explorationPulls <= n) :
    let best := ETC.realKernelBestArm spec.hK nu
    let coordLaw := fun t : Nat => nu (ETC.exploreArm spec t)
    integral (Measure.infinitePi coordLaw) (fun trajectory : RewardTrace Real =>
        realKernelRegret nu
          (ETC.realExplorationArgmaxAction spec best trajectory) n) <=
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
  let mu := Measure.infinitePi coordLaw
  let action : RewardTrace Real -> ActionTrace (Fin K) := fun trajectory =>
    ETC.realExplorationArgmaxAction spec best trajectory
  letI : Nonempty (Fin K) := ⟨Fin.mk 0 spec.hK⟩
  letI : forall t : Nat, IsProbabilityMeasure (coordLaw t) := fun _t =>
    inferInstance
  have hmeas_commit : Measurable (fun trajectory : RewardTrace Real =>
      ETC.realExplorationArgmaxCommit spec best trajectory) :=
    ETC.measurable_realExplorationArgmaxCommit spec best
      (fun trajectory : RewardTrace Real => trajectory)
      (fun t => measurable_pi_apply t)
  have hcount : forall arm : Fin K, Integrable
      (fun trajectory : RewardTrace Real =>
        (pullCount (action trajectory) arm n : Real)) mu := by
    intro arm
    simpa [action, ETC.realExplorationArgmaxAction] using
      (ETC.integrable_real_pullCount_actionWithCommit_choice_of_measurable_commit
        mu spec
        (fun trajectory : RewardTrace Real =>
          ETC.realExplorationArgmaxCommit spec best trajectory)
        arm n hmeas_commit)
  rw [show (fun trajectory : RewardTrace Real =>
      realKernelRegret nu
        (ETC.realExplorationArgmaxAction spec best trajectory) n) =
      (fun trajectory : RewardTrace Real =>
        realKernelRegret nu (action trajectory) n) by rfl]
  rw [integral_realKernelRegret_eq_sum_gap_mul_integral_pullCount
    mu nu action n hcount]
  refine Finset.sum_le_sum ?_
  intro arm _harm
  by_cases hbest : arm = best
  · subst arm
    simp [ETC.realKernelGap_eq_realKernelBestArm_sub spec.hK nu, best]
  · exact mul_le_mul_of_nonneg_left
      (ETC.integral_real_pullCount_realExplorationArgmaxAction_le_exp_of_infinitePi_kernel
        spec nu sigma2 hsubG hm arm n hn hbest)
      (realKernelGap_nonneg nu arm)

end ETC
end BanditRLProof
