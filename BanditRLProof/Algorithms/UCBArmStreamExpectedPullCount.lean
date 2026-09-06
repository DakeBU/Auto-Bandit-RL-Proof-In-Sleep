import BanditRLProof.Algorithms.UCBArmStreamTail
import BanditRLProof.Algorithms.ETCCountLemmas
import BanditRLProof.Algorithms.ETCFiniteArmRewardLaw
import BanditRLProof.Algorithms.ETCRealInfinitePiTail
import BanditRLProof.ExpectationPullCount
import BanditRLProof.MeasurablePullCountCast
import BanditRLProof.RealKernelRegretPullCount
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Expected pull counts for the recursive arm-stream UCB process

This module connects the source-faithful one-sided index tails to the local
selected-small/selected-large pull-count decomposition. It stays in ENNReal
until a downstream Bochner-regret wrapper requests a Real expectation.
-/

namespace BanditRLProof

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace UCB

/-- During initialization the recursive process follows round robin exactly. -/
theorem armStreamAction_eq_initializationArm_of_lt
    {K : Nat} (hK : 0 < K) (c : Real)
    (stream : ArmRewardStream K) (t : Nat) (ht : t < K) :
    armStreamAction hK c stream t = initializationArm hK t := by
  cases t with
  | zero => simp
  | succ n =>
      have hn : n < K - 1 := by omega
      rw [armStreamAction_succ]
      simp [realHistoryNextArm, hn]

/-- Every arm is pulled exactly once in the first full initialization cycle. -/
theorem pullCount_armStreamAction_K_eq_one
    {K : Nat} (hK : 0 < K) (c : Real)
    (stream : ArmRewardStream K) (arm : Fin K) :
    pullCount (armStreamAction hK c stream) arm K = 1 := by
  let spec : ETC.Spec K := { hK := hK, explorationPulls := 1 }
  have haction : forall t, t < K ->
      armStreamAction hK c stream t = ETC.exploreArm spec t := by
    intro t ht
    exact armStreamAction_eq_initializationArm_of_lt hK c stream t ht
  have hcount :
      pullCount (armStreamAction hK c stream) arm K =
        pullCount (ETC.exploreArm spec) arm K := by
    rw [pullCount_eq_finset_filter_card, pullCount_eq_finset_filter_card]
    congr 1
    ext t
    simp only [Finset.mem_filter, Finset.mem_range]
    by_cases ht : t < K
    · simp [ht, haction t ht]
    · simp [ht]
  rw [hcount]
  exact ETC.pullCount_exploreArm_K_eq_one spec arm

/-- After initialization every arm has positive prior pull count. -/
theorem pullCount_armStreamAction_pos_of_K_le
    {K : Nat} (hK : 0 < K) (c : Real)
    (stream : ArmRewardStream K) (arm : Fin K) (t : Nat) (ht : K <= t) :
    0 < pullCount (armStreamAction hK c stream) arm t := by
  have hmono := pullCount_mono
    (armStreamAction hK c stream) arm ht
  rw [pullCount_armStreamAction_K_eq_one hK c stream arm] at hmono
  omega

/-- A second pull cannot occur before the round-robin cycle is complete. -/
theorem K_lt_of_one_lt_pullCount_armStreamAction
    {K : Nat} (hK : 0 < K) (c : Real)
    (stream : ArmRewardStream K) (arm : Fin K) (t : Nat)
    (hcount : 1 < pullCount (armStreamAction hK c stream) arm t) :
    K < t := by
  by_contra hnot
  have ht : t <= K := Nat.le_of_not_gt hnot
  have hmono := pullCount_mono
    (armStreamAction hK c stream) arm ht
  rw [pullCount_armStreamAction_K_eq_one hK c stream arm] at hmono
  omega

/-- After initialization the recursive action is the native trace UCB argmax. -/
theorem armStreamAction_eq_realIndexAction_of_K_le
    {K : Nat} (hK : 0 < K) (c : Real)
    (stream : ArmRewardStream K) (t : Nat) (ht : K <= t) :
    armStreamAction hK c stream t =
      realIndexAction hK
        (armStreamAction hK c stream)
        (armStreamReward hK c stream) c t := by
  cases t with
  | zero => omega
  | succ n =>
      have hn : ¬ (n < K - 1) := by
        cases K with
        | zero => omega
        | succ k =>
            simp only [Nat.add_sub_cancel] at *
            omega
      rw [armStreamAction_succ_eq_realHistoryIndexAction_of_not_lt
        hK c stream n hn]
      exact realHistoryIndexAction_finitePairHistoryOfTrace
        hK (armStreamAction hK c stream)
          (armStreamReward hK c stream) c n

/-- The selected recursive action maximizes the actual random-width index. -/
theorem realIndex_le_realIndex_armStreamAction_of_K_le
    {K : Nat} (hK : 0 < K) (c : Real)
    (stream : ArmRewardStream K) (t : Nat) (ht : K <= t)
    (arm : Fin K) :
    realIndex (armStreamAction hK c stream) (armStreamReward hK c stream)
        c arm t <=
      realIndex (armStreamAction hK c stream) (armStreamReward hK c stream)
        c (armStreamAction hK c stream t) t := by
  rw [armStreamAction_eq_realIndexAction_of_K_le hK c stream t ht]
  exact realIndexAction_spec hK
    (armStreamAction hK c stream) (armStreamReward hK c stream) c t arm

/-- Good confidence inequalities force the selected arm gap below twice its width. -/
theorem meanGap_le_two_realWidth_of_selected
    {K : Nat} (hK : 0 < K) (c : Real)
    (stream : ArmRewardStream K) (t : Nat) (ht : K <= t)
    (trueMean : Fin K -> Real) (best chosen : Fin K)
    (hselected : armStreamAction hK c stream t = chosen)
    (hbest : trueMean best <=
      realEmpiricalMean (armStreamAction hK c stream)
        (armStreamReward hK c stream) best t +
      realWidth (armStreamAction hK c stream) c best t)
    (hchosen : realEmpiricalMean (armStreamAction hK c stream)
        (armStreamReward hK c stream) chosen t -
      realWidth (armStreamAction hK c stream) c chosen t <=
        trueMean chosen) :
    meanGap trueMean best chosen <=
      2 * realWidth (armStreamAction hK c stream) c chosen t := by
  apply meanGap_le_two_radius_of_confidenceScore_max
    trueMean
    (fun arm => realEmpiricalMean (armStreamAction hK c stream)
      (armStreamReward hK c stream) arm t)
    (fun arm => realWidth (armStreamAction hK c stream) c arm t)
    best chosen hbest hchosen
  simpa [confidenceScore, hselected] using
    (realIndex_le_realIndex_armStreamAction_of_K_le
      hK c stream t ht best)

/-- Squaring the good-event gap inequality gives the standard UCB count bound. -/
theorem pullCount_le_eight_scale_log_div_gap_sq
    {K : Nat} (action : ActionTrace (Fin K)) (arm : Fin K)
    (scale gap : Real) (t : Nat)
    (hscale : 0 <= scale) (hgap : 0 < gap)
    (hcount : 0 < pullCount action arm t)
    (hgap_le : gap <= 2 * realWidth action scale arm t) :
    (pullCount action arm t : Real) <=
      8 * scale * Real.log ((t + 1 : Nat) : Real) / gap ^ 2 := by
  rw [realWidth] at hgap_le
  have hsq : gap ^ 2 <=
      (2 * Real.sqrt
        (2 * scale * Real.log ((t + 1 : Nat) : Real) /
          (pullCount action arm t : Real))) ^ 2 := by
    gcongr
  have hlog : 0 <= Real.log ((t + 1 : Nat) : Real) := by
    apply Real.log_nonneg
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le t)
  have hsqrt : 0 <=
      2 * scale * Real.log ((t + 1 : Nat) : Real) /
        (pullCount action arm t : Real) := by positivity
  rw [mul_pow, Real.sq_sqrt hsqrt] at hsq
  have hcountReal : 0 < (pullCount action arm t : Real) := by exact_mod_cast hcount
  have hgapSq : 0 < gap ^ 2 := sq_pos_of_pos hgap
  field_simp [ne_of_gt hcountReal, ne_of_gt hgapSq] at hsq ⊢
  nlinarith

/-- Real threshold used for the horizon-wide pull-count split. -/
noncomputable def realPullThreshold
    (c : Real) (sigma2 : NNReal) (gap : Real) (n : Nat) : Real :=
  8 * c * (sigma2 : Real) * Real.log ((n + 1 : Nat) : Real) / gap ^ 2

/-- Integer split point: one more than the ceiling of the real threshold. -/
noncomputable def pullThreshold
    (c : Real) (sigma2 : NNReal) (gap : Real) (n : Nat) : Nat :=
  Nat.ceil (realPullThreshold c sigma2 gap n) + 1

/-- The one-sided inverse-power tail budget at time `t`. -/
noncomputable def indexTail (c : Real) (t : Nat) : ENNReal :=
  (1 : ENNReal) / (((t + 1 : Nat) : ENNReal) ^ (c - 1))

/-- Finite-horizon sum of the source-faithful one-sided index tails. -/
noncomputable def constSum (c : Real) (n : Nat) : ENNReal :=
  (Finset.range n).sum (indexTail c)

/-- A selected arm whose prior count has crossed the horizon threshold. -/
noncomputable def selectedLargePullCountEvent
    {K : Nat} (hK : 0 < K) (c : Real) (sigma2 : NNReal)
    (gap : Real) (arm : Fin K) (n t : Nat) : Set (ArmRewardStream K) :=
  {stream |
    armStreamAction hK (c * (sigma2 : Real)) stream t = arm ∧
      pullThreshold c sigma2 gap n <=
        pullCount (armStreamAction hK (c * (sigma2 : Real)) stream) arm t}

/-- Lower-index failure for a fixed arm of the recursive process. -/
noncomputable def lowerIndexFailure
    {K : Nat} (hK : 0 < K) (c : Real) (sigma2 : NNReal)
    (arm : Fin K) (mean : Real) (t : Nat) : Set (ArmRewardStream K) :=
  {stream |
    0 < pullCount
        (armStreamAction hK (c * (sigma2 : Real)) stream) arm t ∧
      realEmpiricalMean
          (armStreamAction hK (c * (sigma2 : Real)) stream)
          (armStreamReward hK (c * (sigma2 : Real)) stream) arm t +
        realWidth
          (armStreamAction hK (c * (sigma2 : Real)) stream)
          (c * (sigma2 : Real)) arm t <= mean}

/-- Upper-index failure for a fixed arm of the recursive process. -/
noncomputable def upperIndexFailure
    {K : Nat} (hK : 0 < K) (c : Real) (sigma2 : NNReal)
    (arm : Fin K) (mean : Real) (t : Nat) : Set (ArmRewardStream K) :=
  {stream |
    0 < pullCount
        (armStreamAction hK (c * (sigma2 : Real)) stream) arm t ∧
      mean <=
        realEmpiricalMean
            (armStreamAction hK (c * (sigma2 : Real)) stream)
            (armStreamReward hK (c * (sigma2 : Real)) stream) arm t -
          realWidth
            (armStreamAction hK (c * (sigma2 : Real)) stream)
            (c * (sigma2 : Real)) arm t}

/--
Crossing the horizon count threshold while selecting a positive-gap arm forces
one of the two one-sided index failures used by the arm-stream tail module.
-/
theorem selectedLargePullCountEvent_subset_lower_union_upper
    {K : Nat} (hK : 0 < K) (c : Real) (sigma2 : NNReal)
    (nu : Kernel (Fin K) Real) (arm : Fin K) (n t : Nat)
    (hc : 0 < c) (hsigma2 : sigma2 ≠ 0)
    (hgap : 0 < realKernelGap nu arm) (ht : t < n) :
    selectedLargePullCountEvent hK c sigma2
        (realKernelGap nu arm) arm n t ⊆
      lowerIndexFailure hK c sigma2 (ETC.realKernelBestArm hK nu)
          (realKernelMean nu (ETC.realKernelBestArm hK nu)) t ∪
        upperIndexFailure hK c sigma2 arm (realKernelMean nu arm) t := by
  intro stream hselected
  have hn : 0 < n := Nat.zero_lt_of_lt ht
  have hsigma2Real : 0 < (sigma2 : Real) := by
    exact_mod_cast (pos_iff_ne_zero.mpr hsigma2)
  have hlogn : 0 < Real.log ((n + 1 : Nat) : Real) := by
    apply Real.log_pos
    have : 1 < n + 1 := by omega
    exact_mod_cast this
  have hthresholdPos :
      0 < realPullThreshold c sigma2 (realKernelGap nu arm) n := by
    unfold realPullThreshold
    positivity
  have hceilPos :
      0 < Nat.ceil (realPullThreshold c sigma2 (realKernelGap nu arm) n) :=
    Nat.ceil_pos.mpr hthresholdPos
  have hcountLarge :
      1 < pullCount
        (armStreamAction hK (c * (sigma2 : Real)) stream) arm t := by
    rw [selectedLargePullCountEvent, pullThreshold] at hselected
    have hthresholdCount := hselected.2
    omega
  have hKt : K <= t := Nat.le_of_lt
    (K_lt_of_one_lt_pullCount_armStreamAction
      hK (c * (sigma2 : Real)) stream arm t hcountLarge)
  have hbestCount :
      0 < pullCount
        (armStreamAction hK (c * (sigma2 : Real)) stream)
        (ETC.realKernelBestArm hK nu) t :=
    pullCount_armStreamAction_pos_of_K_le
      hK (c * (sigma2 : Real)) stream (ETC.realKernelBestArm hK nu) t hKt
  have harmCount :
      0 < pullCount
        (armStreamAction hK (c * (sigma2 : Real)) stream) arm t := by
    omega
  by_cases hlower : stream ∈
      lowerIndexFailure hK c sigma2 (ETC.realKernelBestArm hK nu)
        (realKernelMean nu (ETC.realKernelBestArm hK nu)) t
  · exact Or.inl hlower
  by_cases hupper : stream ∈
      upperIndexFailure hK c sigma2 arm (realKernelMean nu arm) t
  · exact Or.inr hupper
  exfalso
  have hbest :
      realKernelMean nu (ETC.realKernelBestArm hK nu) <=
        realEmpiricalMean
            (armStreamAction hK (c * (sigma2 : Real)) stream)
            (armStreamReward hK (c * (sigma2 : Real)) stream)
            (ETC.realKernelBestArm hK nu) t +
          realWidth
            (armStreamAction hK (c * (sigma2 : Real)) stream)
            (c * (sigma2 : Real)) (ETC.realKernelBestArm hK nu) t := by
    simp only [lowerIndexFailure, Set.mem_setOf_eq] at hlower
    have hnot : ¬
        realEmpiricalMean
            (armStreamAction hK (c * (sigma2 : Real)) stream)
            (armStreamReward hK (c * (sigma2 : Real)) stream)
            (ETC.realKernelBestArm hK nu) t +
          realWidth
            (armStreamAction hK (c * (sigma2 : Real)) stream)
            (c * (sigma2 : Real)) (ETC.realKernelBestArm hK nu) t <=
          realKernelMean nu (ETC.realKernelBestArm hK nu) := by
      intro hle
      exact hlower ⟨hbestCount, hle⟩
    exact le_of_lt (lt_of_not_ge hnot)
  have harm :
      realEmpiricalMean
          (armStreamAction hK (c * (sigma2 : Real)) stream)
          (armStreamReward hK (c * (sigma2 : Real)) stream) arm t -
        realWidth
          (armStreamAction hK (c * (sigma2 : Real)) stream)
          (c * (sigma2 : Real)) arm t <= realKernelMean nu arm := by
    simp only [upperIndexFailure, Set.mem_setOf_eq] at hupper
    have hnot : ¬ realKernelMean nu arm <=
        realEmpiricalMean
            (armStreamAction hK (c * (sigma2 : Real)) stream)
            (armStreamReward hK (c * (sigma2 : Real)) stream) arm t -
          realWidth
            (armStreamAction hK (c * (sigma2 : Real)) stream)
            (c * (sigma2 : Real)) arm t := by
      intro hle
      exact hupper ⟨harmCount, hle⟩
    exact le_of_lt (lt_of_not_ge hnot)
  have hgapWidth :
      realKernelGap nu arm <=
        2 * realWidth
          (armStreamAction hK (c * (sigma2 : Real)) stream)
          (c * (sigma2 : Real)) arm t := by
    rw [ETC.realKernelGap_eq_realKernelBestArm_sub hK nu arm]
    exact meanGap_le_two_realWidth_of_selected
      hK (c * (sigma2 : Real)) stream t hKt (realKernelMean nu)
      (ETC.realKernelBestArm hK nu) arm hselected.1 hbest harm
  have hcountBound := pullCount_le_eight_scale_log_div_gap_sq
    (armStreamAction hK (c * (sigma2 : Real)) stream) arm
    (c * (sigma2 : Real)) (realKernelGap nu arm) t
    (by positivity) hgap harmCount hgapWidth
  have hlogle :
      Real.log ((t + 1 : Nat) : Real) <=
        Real.log ((n + 1 : Nat) : Real) := by
    exact Real.strictMonoOn_log.monotoneOn
      (by simp only [Set.mem_Ioi]; positivity)
      (by simp only [Set.mem_Ioi]; positivity)
      (by exact_mod_cast Nat.succ_le_succ (Nat.le_of_lt ht))
  have htimeBound :
      8 * (c * (sigma2 : Real)) * Real.log ((t + 1 : Nat) : Real) /
          (realKernelGap nu arm) ^ 2 <=
        realPullThreshold c sigma2 (realKernelGap nu arm) n := by
    rw [realPullThreshold]
    have hcoef : 0 <= 8 * c * (sigma2 : Real) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hlogle hcoef
    apply (div_le_div_iff_of_pos_right (sq_pos_of_pos hgap)).2
    nlinarith
  have hceilBound :
      realPullThreshold c sigma2 (realKernelGap nu arm) n <=
        (Nat.ceil (realPullThreshold c sigma2
          (realKernelGap nu arm) n) : Real) :=
    Nat.le_ceil _
  have hcountCeil :
      (pullCount
          (armStreamAction hK (c * (sigma2 : Real)) stream) arm t : Real) <=
        (Nat.ceil (realPullThreshold c sigma2
          (realKernelGap nu arm) n) : Real) :=
    hcountBound.trans (htimeBound.trans hceilBound)
  rw [selectedLargePullCountEvent, pullThreshold] at hselected
  have hthresholdCast :
      ((Nat.ceil (realPullThreshold c sigma2
          (realKernelGap nu arm) n) + 1 : Nat) : Real) <=
        (pullCount
          (armStreamAction hK (c * (sigma2 : Real)) stream) arm t : Real) := by
    exact_mod_cast hselected.2
  norm_num at hthresholdCast
  linarith

/-- The selected-large event has twice the one-sided inverse-power budget. -/
theorem measure_selectedLargePullCountEvent_le_two_mul_indexTail
    {K : Nat} (hK : 0 < K) (c : Real) (sigma2 : NNReal)
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu]
    (arm : Fin K) (n t : Nat)
    (hc : 0 < c) (hsigma2 : sigma2 ≠ 0)
    (hgap : 0 < realKernelGap nu arm) (ht : t < n)
    (hsubGBest : HasSubgaussianMGF
      (fun reward => reward -
        realKernelMean nu (ETC.realKernelBestArm hK nu)) sigma2
      (nu (ETC.realKernelBestArm hK nu)))
    (hsubGArm : HasSubgaussianMGF
      (fun reward => reward - realKernelMean nu arm) sigma2 (nu arm)) :
    armStreamMeasure nu
        (selectedLargePullCountEvent hK c sigma2
          (realKernelGap nu arm) arm n t) <=
      2 * indexTail c t := by
  calc
    armStreamMeasure nu
        (selectedLargePullCountEvent hK c sigma2
          (realKernelGap nu arm) arm n t) <=
      armStreamMeasure nu
        (lowerIndexFailure hK c sigma2 (ETC.realKernelBestArm hK nu)
            (realKernelMean nu (ETC.realKernelBestArm hK nu)) t ∪
          upperIndexFailure hK c sigma2 arm (realKernelMean nu arm) t) := by
      exact measure_mono
        (selectedLargePullCountEvent_subset_lower_union_upper
          hK c sigma2 nu arm n t hc hsigma2 hgap ht)
    _ <=
      armStreamMeasure nu
          (lowerIndexFailure hK c sigma2 (ETC.realKernelBestArm hK nu)
            (realKernelMean nu (ETC.realKernelBestArm hK nu)) t) +
        armStreamMeasure nu
          (upperIndexFailure hK c sigma2 arm (realKernelMean nu arm) t) :=
      measure_union_le _ _
    _ <= indexTail c t + indexTail c t := by
      apply add_le_add
      · simpa [lowerIndexFailure, indexTail] using
          measure_realEmpiricalMean_add_realWidth_le_mean_rpow_bound
            hK c nu (ETC.realKernelBestArm hK nu)
              (realKernelMean nu (ETC.realKernelBestArm hK nu)) sigma2
                hsubGBest (le_of_lt hc) hsigma2 t
      · simpa [upperIndexFailure, indexTail] using
          measure_mean_le_realEmpiricalMean_sub_realWidth_rpow_bound
            hK c nu arm (realKernelMean nu arm) sigma2
              hsubGArm (le_of_lt hc) hsigma2 t
    _ = 2 * indexTail c t := by rw [two_mul]

/-- Finite-time selected-large indicators integrate to twice `constSum`. -/
theorem lintegral_selectedLargePullCount_indicator_sum_le_two_mul_constSum
    {K : Nat} (hK : 0 < K) (c : Real) (sigma2 : NNReal)
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu]
    (arm : Fin K) (n : Nat)
    (hc : 0 < c) (hsigma2 : sigma2 ≠ 0)
    (hgap : 0 < realKernelGap nu arm)
    (hsubGBest : HasSubgaussianMGF
      (fun reward => reward -
        realKernelMean nu (ETC.realKernelBestArm hK nu)) sigma2
      (nu (ETC.realKernelBestArm hK nu)))
    (hsubGArm : HasSubgaussianMGF
      (fun reward => reward - realKernelMean nu arm) sigma2 (nu arm)) :
    ∫⁻ stream : ArmRewardStream K,
        (Finset.range n).sum (fun t : Nat =>
          if armStreamAction hK (c * (sigma2 : Real)) stream t = arm ∧
              pullThreshold c sigma2 (realKernelGap nu arm) n <=
                pullCount
                  (armStreamAction hK (c * (sigma2 : Real)) stream) arm t then
            (1 : ENNReal)
          else 0) ∂armStreamMeasure nu <=
      2 * constSum c n := by
  rw [lintegral_selectedLargePullCount_indicator_sum_eq_sum_measure
    (mu := armStreamMeasure nu)
    (action := armStreamAction hK (c * (sigma2 : Real)))
    (haction := measurable_armStreamAction hK (c * (sigma2 : Real)))
    (chosen := arm)
    (T := n)
    (B := pullThreshold c sigma2 (realKernelGap nu arm) n)]
  calc
    (Finset.range n).sum (fun t : Nat =>
        armStreamMeasure nu
          {stream : ArmRewardStream K |
            armStreamAction hK (c * (sigma2 : Real)) stream t = arm ∧
              pullThreshold c sigma2 (realKernelGap nu arm) n <=
                pullCount
                  (armStreamAction hK (c * (sigma2 : Real)) stream) arm t}) <=
      (Finset.range n).sum (fun t : Nat => 2 * indexTail c t) := by
        apply Finset.sum_le_sum
        intro t ht
        rw [Finset.mem_range] at ht
        simpa [selectedLargePullCountEvent] using
          measure_selectedLargePullCountEvent_le_two_mul_indexTail
            hK c sigma2 nu arm n t hc hsigma2 hgap ht hsubGBest hsubGArm
    _ = 2 * constSum c n := by
      rw [constSum, Finset.mul_sum]

/--
ENNReal expected pull-count bound for one positive-gap arm of the concrete
recursive UCB process.
-/
theorem lintegral_natCast_pullCount_armStreamAction_le_threshold_add_two_mul_constSum
    {K : Nat} (hK : 0 < K) (c : Real) (sigma2 : NNReal)
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu]
    (arm : Fin K) (n : Nat)
    (hc : 0 < c) (hsigma2 : sigma2 ≠ 0)
    (hgap : 0 < realKernelGap nu arm)
    (hsubGBest : HasSubgaussianMGF
      (fun reward => reward -
        realKernelMean nu (ETC.realKernelBestArm hK nu)) sigma2
      (nu (ETC.realKernelBestArm hK nu)))
    (hsubGArm : HasSubgaussianMGF
      (fun reward => reward - realKernelMean nu arm) sigma2 (nu arm)) :
    ∫⁻ stream : ArmRewardStream K,
        (pullCount
          (armStreamAction hK (c * (sigma2 : Real)) stream) arm n : ENNReal)
        ∂armStreamMeasure nu <=
      (pullThreshold c sigma2 (realKernelGap nu arm) n : ENNReal) +
        2 * constSum c n := by
  let action : ArmRewardStream K -> ActionTrace (Fin K) :=
    armStreamAction hK (c * (sigma2 : Real))
  let largeCount : ArmRewardStream K -> ENNReal := fun stream =>
    (Finset.range n).sum (fun t : Nat =>
      if action stream t = arm ∧
          pullThreshold c sigma2 (realKernelGap nu arm) n <=
            pullCount (action stream) arm t then
        (1 : ENNReal)
      else 0)
  have hpoint : forall stream : ArmRewardStream K,
      (pullCount (action stream) arm n : ENNReal) <=
        (pullThreshold c sigma2 (realKernelGap nu arm) n : ENNReal) +
          largeCount stream := by
    intro stream
    exact natCast_pullCount_le_threshold_add_selectedLargePullCount_indicator_sum
      (action stream) arm n
        (pullThreshold c sigma2 (realKernelGap nu arm) n)
  have hlarge : ∫⁻ stream : ArmRewardStream K, largeCount stream
      ∂armStreamMeasure nu <= 2 * constSum c n := by
    simpa [action, largeCount] using
      lintegral_selectedLargePullCount_indicator_sum_le_two_mul_constSum
        hK c sigma2 nu arm n hc hsigma2 hgap hsubGBest hsubGArm
  calc
    ∫⁻ stream : ArmRewardStream K,
        (pullCount (action stream) arm n : ENNReal) ∂armStreamMeasure nu <=
      ∫⁻ stream : ArmRewardStream K,
        ((pullThreshold c sigma2 (realKernelGap nu arm) n : ENNReal) +
          largeCount stream) ∂armStreamMeasure nu :=
      lintegral_mono hpoint
    _ =
      ∫⁻ _stream : ArmRewardStream K,
          (pullThreshold c sigma2 (realKernelGap nu arm) n : ENNReal)
            ∂armStreamMeasure nu +
        ∫⁻ stream : ArmRewardStream K, largeCount stream
            ∂armStreamMeasure nu := by
      rw [lintegral_add_left measurable_const]
    _ =
      (pullThreshold c sigma2 (realKernelGap nu arm) n : ENNReal) +
        ∫⁻ stream : ArmRewardStream K, largeCount stream
          ∂armStreamMeasure nu := by
      rw [lintegral_const]
      simp [IsProbabilityMeasure.measure_univ]
    _ <=
      (pullThreshold c sigma2 (realKernelGap nu arm) n : ENNReal) +
        2 * constSum c n := add_le_add (le_refl _) hlarge

/-- Every finite inverse-power tail budget is finite. -/
theorem indexTail_ne_top (c : Real) (t : Nat) : indexTail c t ≠ ∞ := by
  unfold indexTail
  finiteness

/-- The finite-horizon inverse-power tail sum is finite. -/
theorem constSum_ne_top (c : Real) (n : Nat) : constSum c n ≠ ∞ := by
  unfold constSum
  exact ENNReal.sum_ne_top.mpr fun t _ht => indexTail_ne_top c t

/-- Real pull counts of the measurable recursive process are integrable. -/
theorem integrable_real_pullCount_armStreamAction
    {K : Nat} (hK : 0 < K) (c : Real)
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu]
    (arm : Fin K) (n : Nat) :
    Integrable (fun stream : ArmRewardStream K =>
      (pullCount (armStreamAction hK c stream) arm n : Real))
      (armStreamMeasure nu) := by
  have hmeas : Measurable (fun stream : ArmRewardStream K =>
      (pullCount (armStreamAction hK c stream) arm n : Real)) :=
    measurable_natCast_pullCount (armStreamAction hK c)
      (measurable_armStreamAction hK c) arm n
  refine Integrable.of_bound hmeas.aestronglyMeasurable (n : Real) ?_
  filter_upwards [] with stream
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast pullCount_le_time (armStreamAction hK c stream) arm n

/--
Real Bochner expected pull-count bound obtained from the ENNReal endpoint.
-/
theorem integral_real_pullCount_armStreamAction_le_threshold_add_two_mul_constSum
    {K : Nat} (hK : 0 < K) (c : Real) (sigma2 : NNReal)
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu]
    (arm : Fin K) (n : Nat)
    (hc : 0 < c) (hsigma2 : sigma2 ≠ 0)
    (hgap : 0 < realKernelGap nu arm)
    (hsubGBest : HasSubgaussianMGF
      (fun reward => reward -
        realKernelMean nu (ETC.realKernelBestArm hK nu)) sigma2
      (nu (ETC.realKernelBestArm hK nu)))
    (hsubGArm : HasSubgaussianMGF
      (fun reward => reward - realKernelMean nu arm) sigma2 (nu arm)) :
    ∫ stream : ArmRewardStream K,
        (pullCount
          (armStreamAction hK (c * (sigma2 : Real)) stream) arm n : Real)
        ∂armStreamMeasure nu <=
      (pullThreshold c sigma2 (realKernelGap nu arm) n : Real) +
        2 * (constSum c n).toReal := by
  let count : ArmRewardStream K -> Real := fun stream =>
    (pullCount
      (armStreamAction hK (c * (sigma2 : Real)) stream) arm n : Real)
  have hcountInt : Integrable count (armStreamMeasure nu) := by
    simpa [count] using integrable_real_pullCount_armStreamAction
      hK (c * (sigma2 : Real)) nu arm n
  have hcountNonneg :
      ∀ᵐ stream ∂armStreamMeasure nu, 0 <= count stream :=
    ae_of_all _ fun stream => Nat.cast_nonneg _
  have hlin :
      ∫⁻ stream : ArmRewardStream K, ENNReal.ofReal (count stream)
          ∂armStreamMeasure nu <=
        (pullThreshold c sigma2 (realKernelGap nu arm) n : ENNReal) +
          2 * constSum c n := by
    simpa [count] using
      lintegral_natCast_pullCount_armStreamAction_le_threshold_add_two_mul_constSum
        hK c sigma2 nu arm n hc hsigma2 hgap hsubGBest hsubGArm
  have hrhs :
      (pullThreshold c sigma2 (realKernelGap nu arm) n : ENNReal) +
          2 * constSum c n ≠ ∞ := by
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.coe_ne_top,
      ENNReal.mul_ne_top ENNReal.ofNat_ne_top (constSum_ne_top c n)⟩
  have hofReal :
      ENNReal.ofReal (∫ stream : ArmRewardStream K, count stream
          ∂armStreamMeasure nu) <=
        (pullThreshold c sigma2 (realKernelGap nu arm) n : ENNReal) +
          2 * constSum c n := by
    rw [ofReal_integral_eq_lintegral_ofReal hcountInt hcountNonneg]
    exact hlin
  have hreal := (ENNReal.ofReal_le_iff_le_toReal hrhs).mp hofReal
  have htoReal :
      ((pullThreshold c sigma2 (realKernelGap nu arm) n : ENNReal) +
          2 * constSum c n).toReal =
        (pullThreshold c sigma2 (realKernelGap nu arm) n : Real) +
          2 * (constSum c n).toReal := by
    calc
      ((pullThreshold c sigma2 (realKernelGap nu arm) n : ENNReal) +
          2 * constSum c n).toReal =
        (pullThreshold c sigma2 (realKernelGap nu arm) n : ENNReal).toReal +
          (2 * constSum c n).toReal :=
        ENNReal.toReal_add ENNReal.coe_ne_top
          (ENNReal.mul_ne_top ENNReal.ofNat_ne_top (constSum_ne_top c n))
      _ = (pullThreshold c sigma2 (realKernelGap nu arm) n : Real) +
          2 * (constSum c n).toReal := by
        rw [ENNReal.toReal_mul]
        simp
  rw [htoReal] at hreal
  simpa [count] using hreal

/-- The ceiling threshold is bounded by the exact LML real threshold plus two. -/
theorem pullThreshold_cast_le_realPullThreshold_add_two
    (c : Real) (sigma2 : NNReal) (gap : Real) (n : Nat)
    (hthreshold : 0 <= realPullThreshold c sigma2 gap n) :
    (pullThreshold c sigma2 gap n : Real) <=
      realPullThreshold c sigma2 gap n + 2 := by
  rw [pullThreshold, Nat.cast_add, Nat.cast_one]
  exact le_of_lt (by
    have hceil := Nat.ceil_lt_add_one hthreshold
    linarith)

/-- LML-shaped Real expected pull-count bound without a ceiling term. -/
theorem integral_real_pullCount_armStreamAction_le_realThreshold_add_two_add_two_mul_constSum
    {K : Nat} (hK : 0 < K) (c : Real) (sigma2 : NNReal)
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu]
    (arm : Fin K) (n : Nat)
    (hc : 0 < c) (hsigma2 : sigma2 ≠ 0)
    (hgap : 0 < realKernelGap nu arm)
    (hsubGBest : HasSubgaussianMGF
      (fun reward => reward -
        realKernelMean nu (ETC.realKernelBestArm hK nu)) sigma2
      (nu (ETC.realKernelBestArm hK nu)))
    (hsubGArm : HasSubgaussianMGF
      (fun reward => reward - realKernelMean nu arm) sigma2 (nu arm)) :
    ∫ stream : ArmRewardStream K,
        (pullCount
          (armStreamAction hK (c * (sigma2 : Real)) stream) arm n : Real)
        ∂armStreamMeasure nu <=
      realPullThreshold c sigma2 (realKernelGap nu arm) n + 2 +
        2 * (constSum c n).toReal := by
  refine (integral_real_pullCount_armStreamAction_le_threshold_add_two_mul_constSum
    hK c sigma2 nu arm n hc hsigma2 hgap hsubGBest hsubGArm).trans ?_
  gcongr
  apply pullThreshold_cast_le_realPullThreshold_add_two
  unfold realPullThreshold
  positivity

/--
Finite-arm expected regret bound for the concrete recursive arm-stream UCB
process, in the same gap-weighted shape as the pinned LML route.
-/
theorem integral_realKernelRegret_armStreamAction_le_sum_gap_mul_realThreshold_add_two_add_two_mul_constSum
    {K : Nat} (hK : 0 < K) (c : Real) (sigma2 : NNReal)
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu]
    (n : Nat) (hc : 0 < c) (hsigma2 : sigma2 ≠ 0)
    (hsubG : forall arm : Fin K, HasSubgaussianMGF
      (fun reward => reward - realKernelMean nu arm) sigma2 (nu arm)) :
    ∫ stream : ArmRewardStream K,
        realKernelRegret nu
          (armStreamAction hK (c * (sigma2 : Real)) stream) n
        ∂armStreamMeasure nu <=
      (Finset.univ : Finset (Fin K)).sum (fun arm =>
        realKernelGap nu arm *
          (realPullThreshold c sigma2 (realKernelGap nu arm) n + 2 +
            2 * (constSum c n).toReal)) := by
  letI : Nonempty (Fin K) := ⟨Fin.mk 0 hK⟩
  have hcount : forall arm : Fin K,
      Integrable (fun stream : ArmRewardStream K =>
        (pullCount
          (armStreamAction hK (c * (sigma2 : Real)) stream) arm n : Real))
        (armStreamMeasure nu) := fun arm =>
    integrable_real_pullCount_armStreamAction
      hK (c * (sigma2 : Real)) nu arm n
  rw [integral_realKernelRegret_eq_sum_gap_mul_integral_pullCount
    (armStreamMeasure nu) nu
      (armStreamAction hK (c * (sigma2 : Real))) n hcount]
  apply Finset.sum_le_sum
  intro arm _harm
  have hgapNonneg : 0 <= realKernelGap nu arm :=
    realKernelGap_nonneg nu arm
  by_cases hgapZero : realKernelGap nu arm = 0
  · simp [hgapZero]
  · have hgapPos : 0 < realKernelGap nu arm :=
      lt_of_le_of_ne hgapNonneg (Ne.symm hgapZero)
    exact mul_le_mul_of_nonneg_left
      (integral_real_pullCount_armStreamAction_le_realThreshold_add_two_add_two_mul_constSum
        hK c sigma2 nu arm n hc hsigma2 hgapPos
          (hsubG (ETC.realKernelBestArm hK nu)) (hsubG arm))
      hgapNonneg

/--
Canonical arm-stream specialization of the pinned LML UCB regret theorem,
with exactly the upstream gap-weighted finite-sum right-hand side.
-/
theorem integral_realKernelRegret_armStreamAction_le_lml_sum
    {K : Nat} (hK : 0 < K) (c : Real) (sigma2 : NNReal)
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu]
    (n : Nat) (hc : 0 < c) (hsigma2 : sigma2 ≠ 0)
    (hsubG : forall arm : Fin K, HasSubgaussianMGF
      (fun reward => reward - realKernelMean nu arm) sigma2 (nu arm)) :
    ∫ stream : ArmRewardStream K,
        realKernelRegret nu
          (armStreamAction hK (c * (sigma2 : Real)) stream) n
        ∂armStreamMeasure nu <=
      (Finset.univ : Finset (Fin K)).sum (fun arm =>
        8 * c * (sigma2 : Real) * Real.log ((n + 1 : Nat) : Real) /
            realKernelGap nu arm +
          realKernelGap nu arm * (2 + 2 * (constSum c n).toReal)) := by
  refine (integral_realKernelRegret_armStreamAction_le_sum_gap_mul_realThreshold_add_two_add_two_mul_constSum
    hK c sigma2 nu n hc hsigma2 hsubG).trans_eq ?_
  apply Finset.sum_congr rfl
  intro arm _harm
  by_cases hgap : realKernelGap nu arm = 0
  · simp [hgap, realPullThreshold]
  · unfold realPullThreshold
    field_simp [hgap]
    ring

/-- The complete recursive arm-stream action trace is measurable. -/
theorem measurable_armStreamActionTrace
    {K : Nat} (hK : 0 < K) (c : Real) :
    Measurable (armStreamAction hK c :
      ArmRewardStream K -> ActionTrace (Fin K)) := by
  exact measurable_pi_lambda _ (measurable_armStreamAction hK c)

/-- Kernel regret is a measurable functional of a finite-arm action trace. -/
theorem measurable_realKernelRegret_actionTrace
    {K : Nat} (nu : Kernel (Fin K) Real) (n : Nat) :
    Measurable (fun action : ActionTrace (Fin K) =>
      realKernelRegret nu action n) := by
  rw [show (fun action : ActionTrace (Fin K) =>
      realKernelRegret nu action n) =
      (fun action => (Finset.range n).sum
        (fun t => realKernelGap nu (action t))) by
    funext action
    exact realKernelRegret_eq_finset_sum_gap nu action n]
  refine Finset.measurable_sum _ ?_
  intro t _ht
  exact (measurable_of_finite (realKernelGap nu)).comp
    (measurable_pi_apply t)

/--
Any external action process with the same complete action-trace law as the
canonical arm-stream UCB process inherits its exact LML-shaped regret bound.
-/
theorem integral_realKernelRegret_externalAction_le_lml_sum_of_identDistrib_armStreamAction
    {Omega : Type*} [MeasurableSpace Omega]
    {K : Nat} (hK : 0 < K) (c : Real) (sigma2 : NNReal)
    (mu : Measure Omega)
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu]
    (action : Omega -> ActionTrace (Fin K))
    (hident : IdentDistrib action
      (armStreamAction hK (c * (sigma2 : Real)))
      mu (armStreamMeasure nu))
    (n : Nat) (hc : 0 < c) (hsigma2 : sigma2 ≠ 0)
    (hsubG : forall arm : Fin K, HasSubgaussianMGF
      (fun reward => reward - realKernelMean nu arm) sigma2 (nu arm)) :
    integral mu (fun omega => realKernelRegret nu (action omega) n) <=
      (Finset.univ : Finset (Fin K)).sum (fun arm =>
        8 * c * (sigma2 : Real) * Real.log ((n + 1 : Nat) : Real) /
            realKernelGap nu arm +
          realKernelGap nu arm * (2 + 2 * (constSum c n).toReal)) := by
  have hregretIntegral :=
    (hident.comp (measurable_realKernelRegret_actionTrace nu n)).integral_eq
  rw [show integral mu (fun omega => realKernelRegret nu (action omega) n) =
      integral (armStreamMeasure nu) (fun stream =>
        realKernelRegret nu
          (armStreamAction hK (c * (sigma2 : Real)) stream) n) by
    simpa only [Function.comp_apply] using hregretIntegral]
  exact integral_realKernelRegret_armStreamAction_le_lml_sum
    hK c sigma2 nu n hc hsigma2 hsubG

/--
An external action generated almost surely by the recursive UCB map inherits
the canonical action-trace law from an identically distributed latent arm
stream.
-/
theorem identDistrib_action_armStreamAction_of_identDistrib_armStream
    {Omega : Type*} [MeasurableSpace Omega]
    {K : Nat} (hK : 0 < K) (c : Real)
    (mu : Measure Omega)
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu]
    (armStream : Omega -> ArmRewardStream K)
    (action : Omega -> ActionTrace (Fin K))
    (hstreamLaw : IdentDistrib armStream
      (id : ArmRewardStream K -> ArmRewardStream K)
      mu (armStreamMeasure nu))
    (haction : ∀ᵐ omega ∂mu,
      action omega = armStreamAction hK c (armStream omega)) :
    IdentDistrib action (armStreamAction hK c)
      mu (armStreamMeasure nu) := by
  have hgeneratedLaw : IdentDistrib
      (fun omega => armStreamAction hK c (armStream omega))
      (armStreamAction hK c) mu (armStreamMeasure nu) := by
    simpa only [Function.comp_apply, id_eq] using
      hstreamLaw.comp (measurable_armStreamActionTrace hK c)
  have hactionMeasurable : AEMeasurable action mu :=
    hgeneratedLaw.aemeasurable_fst.congr
      (Filter.EventuallyEq.symm haction)
  exact (IdentDistrib.of_ae_eq hactionMeasurable haction).trans hgeneratedLaw

/--
Exact LML-shaped regret for an external action generated from a latent arm
stream with the canonical complete stream law.
-/
theorem integral_realKernelRegret_externalAction_le_lml_sum_of_identDistrib_armStream
    {Omega : Type*} [MeasurableSpace Omega]
    {K : Nat} (hK : 0 < K) (c : Real) (sigma2 : NNReal)
    (mu : Measure Omega)
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu]
    (armStream : Omega -> ArmRewardStream K)
    (action : Omega -> ActionTrace (Fin K))
    (hstreamLaw : IdentDistrib armStream
      (id : ArmRewardStream K -> ArmRewardStream K)
      mu (armStreamMeasure nu))
    (haction : ∀ᵐ omega ∂mu,
      action omega =
        armStreamAction hK (c * (sigma2 : Real)) (armStream omega))
    (n : Nat) (hc : 0 < c) (hsigma2 : sigma2 ≠ 0)
    (hsubG : forall arm : Fin K, HasSubgaussianMGF
      (fun reward => reward - realKernelMean nu arm) sigma2 (nu arm)) :
    integral mu (fun omega => realKernelRegret nu (action omega) n) <=
      (Finset.univ : Finset (Fin K)).sum (fun arm =>
        8 * c * (sigma2 : Real) * Real.log ((n + 1 : Nat) : Real) /
            realKernelGap nu arm +
          realKernelGap nu arm * (2 + 2 * (constSum c n).toReal)) := by
  apply
    integral_realKernelRegret_externalAction_le_lml_sum_of_identDistrib_armStreamAction
      hK c sigma2 mu nu action
      (identDistrib_action_armStreamAction_of_identDistrib_armStream
        hK (c * (sigma2 : Real)) mu nu armStream action hstreamLaw haction)
      n hc hsigma2 hsubG

/--
Identical laws of complete action/reward trajectories imply identical laws of
their action traces. This is the projection used by LML's
`IsAlgEnvSeq.identDistrib_trajectory` route.
-/
theorem identDistrib_action_of_identDistrib_actionRewardTrace
    {Omega Xi : Type*} [MeasurableSpace Omega] [MeasurableSpace Xi]
    {K : Nat}
    (mu : Measure Omega) (mu' : Measure Xi)
    (action : Omega -> ActionTrace (Fin K))
    (reward : Omega -> RewardTrace Real)
    (action' : Xi -> ActionTrace (Fin K))
    (reward' : Xi -> RewardTrace Real)
    (htrajectory : IdentDistrib
      (fun omega t => (action omega t, reward omega t))
      (fun xi t => (action' xi t, reward' xi t)) mu mu') :
    IdentDistrib action action' mu mu' := by
  have hprojectAction : Measurable
      (fun trajectory : ActionTrace (Fin K × Real) =>
        fun t => (trajectory t).1) := by
    exact measurable_pi_lambda _ (fun t =>
      measurable_fst.comp (measurable_pi_apply t))
  simpa only [Function.comp_apply] using htrajectory.comp hprojectAction

/--
Exact LML-shaped regret transported from an observable action/reward trajectory
law matching the canonical recursive arm-stream UCB trajectory.
-/
theorem integral_realKernelRegret_externalAction_le_lml_sum_of_identDistrib_actionRewardTrace
    {Omega : Type*} [MeasurableSpace Omega]
    {K : Nat} (hK : 0 < K) (c : Real) (sigma2 : NNReal)
    (mu : Measure Omega)
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu]
    (action : Omega -> ActionTrace (Fin K))
    (reward : Omega -> RewardTrace Real)
    (htrajectory : IdentDistrib
      (fun omega t => (action omega t, reward omega t))
      (fun stream t =>
        (armStreamAction hK (c * (sigma2 : Real)) stream t,
          armStreamReward hK (c * (sigma2 : Real)) stream t))
      mu (armStreamMeasure nu))
    (n : Nat) (hc : 0 < c) (hsigma2 : sigma2 ≠ 0)
    (hsubG : forall arm : Fin K, HasSubgaussianMGF
      (fun x => x - realKernelMean nu arm) sigma2 (nu arm)) :
    integral mu (fun omega => realKernelRegret nu (action omega) n) <=
      (Finset.univ : Finset (Fin K)).sum (fun arm =>
        8 * c * (sigma2 : Real) * Real.log ((n + 1 : Nat) : Real) /
            realKernelGap nu arm +
          realKernelGap nu arm * (2 + 2 * (constSum c n).toReal)) := by
  apply
    integral_realKernelRegret_externalAction_le_lml_sum_of_identDistrib_armStreamAction
      hK c sigma2 mu nu action
      (identDistrib_action_of_identDistrib_actionRewardTrace
        mu (armStreamMeasure nu) action reward
        (armStreamAction hK (c * (sigma2 : Real)))
        (armStreamReward hK (c * (sigma2 : Real))) htrajectory)
      n hc hsigma2 hsubG

/--
Exact LML-shaped regret from upstream-style initial and successor
action/reward conditional laws. The external process and the canonical
arm-stream UCB process need only share the same initial pair marginal and the
same history-indexed successor pair kernels; full trajectory `IdentDistrib` is
then supplied by Ionescu-Tulcea/projective-limit uniqueness.
-/
theorem integral_realKernelRegret_externalAction_le_lml_sum_of_common_actionReward_condDistrib
    {Omega : Type*} [MeasurableSpace Omega]
    {K : Nat} [NeZero K] (hK : 0 < K) (c : Real) (sigma2 : NNReal)
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu]
    (action : Omega -> ActionTrace (Fin K))
    (reward : Omega -> RewardTrace Real)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (mu0 : Measure (Fin K × Real)) [IsProbabilityMeasure mu0]
    (pairKernel : (i : Nat) ->
      Kernel (History.FinitePairHistory (Fin K) Real i) (Fin K × Real))
    [forall i, IsMarkovKernel (pairKernel i)]
    (hzero : Measure.map
      (fun omega : Omega => (action omega 0, reward omega 0)) mu = mu0)
    (hzeroCanonical : Measure.map
      (fun stream : ArmRewardStream K =>
        (armStreamAction hK (c * (sigma2 : Real)) stream 0,
          armStreamReward hK (c * (sigma2 : Real)) stream 0))
      (armStreamMeasure nu) = mu0)
    (hcond : forall i : Nat,
      condDistrib
          (fun omega : Omega =>
            (action omega (i + 1), reward omega (i + 1)))
          (fun omega : Omega =>
            History.finitePairHistoryOfTrace
              (action omega) (reward omega) i)
          mu =ᵐ[mu.map (fun omega : Omega =>
            History.finitePairHistoryOfTrace
              (action omega) (reward omega) i)]
        pairKernel i)
    (hcondCanonical : forall i : Nat,
      condDistrib
          (fun stream : ArmRewardStream K =>
            (armStreamAction hK (c * (sigma2 : Real)) stream (i + 1),
              armStreamReward hK (c * (sigma2 : Real)) stream (i + 1)))
          (fun stream : ArmRewardStream K =>
            History.finitePairHistoryOfTrace
              (armStreamAction hK (c * (sigma2 : Real)) stream)
              (armStreamReward hK (c * (sigma2 : Real)) stream) i)
          (armStreamMeasure nu) =ᵐ[(armStreamMeasure nu).map
            (fun stream : ArmRewardStream K =>
              History.finitePairHistoryOfTrace
                (armStreamAction hK (c * (sigma2 : Real)) stream)
                (armStreamReward hK (c * (sigma2 : Real)) stream) i)]
        pairKernel i)
    (n : Nat) (hc : 0 < c) (hsigma2 : sigma2 ≠ 0)
    (hsubG : forall arm : Fin K, HasSubgaussianMGF
      (fun x => x - realKernelMean nu arm) sigma2 (nu arm)) :
    integral mu (fun omega => realKernelRegret nu (action omega) n) <=
      (Finset.univ : Finset (Fin K)).sum (fun arm =>
        8 * c * (sigma2 : Real) * Real.log ((n + 1 : Nat) : Real) /
            realKernelGap nu arm +
          realKernelGap nu arm * (2 + 2 * (constSum c n).toReal)) := by
  have htrajectory : IdentDistrib
      (fun omega t => (action omega t, reward omega t))
      (fun stream t =>
        (armStreamAction hK (c * (sigma2 : Real)) stream t,
          armStreamReward hK (c * (sigma2 : Real)) stream t))
      mu (armStreamMeasure nu) := by
    apply RewardKernel.identDistrib_rewardTrace_of_common_condDistrib
      mu (armStreamMeasure nu) mu0
      (fun omega t => (action omega t, reward omega t))
      (fun stream t =>
        (armStreamAction hK (c * (sigma2 : Real)) stream t,
          armStreamReward hK (c * (sigma2 : Real)) stream t))
      (fun t => Measurable.prod (haction t) (hreward t))
      (fun t => Measurable.prod
        (measurable_armStreamAction hK (c * (sigma2 : Real)) t)
        (measurable_armStreamReward hK (c * (sigma2 : Real)) t))
      pairKernel hzero hzeroCanonical
    · intro i
      simpa only [History.finiteRewardHistoryOfTrace,
        History.finitePairHistoryOfTrace] using hcond i
    · intro i
      simpa only [History.finiteRewardHistoryOfTrace,
        History.finitePairHistoryOfTrace] using hcondCanonical i
  exact
    integral_realKernelRegret_externalAction_le_lml_sum_of_identDistrib_actionRewardTrace
      hK c sigma2 mu nu action reward htrajectory n hc hsigma2 hsubG

/--
An external action/reward process has the same complete observable trajectory
law as canonical arm-stream UCB when its initial pair marginal and every
successor pair conditional distribution agree with the corresponding canonical
ones. The canonical initial measure and kernel family are chosen internally.
-/
theorem identDistrib_actionRewardTrace_of_condDistrib_eq_armStream
    {Omega : Type*} [MeasurableSpace Omega]
    {K : Nat} [NeZero K] (hK : 0 < K) (c : Real) (sigma2 : NNReal)
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu]
    (action : Omega -> ActionTrace (Fin K))
    (reward : Omega -> RewardTrace Real)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (hzero : Measure.map
      (fun omega : Omega => (action omega 0, reward omega 0)) mu =
        Measure.map
          (fun stream : ArmRewardStream K =>
            (armStreamAction hK (c * (sigma2 : Real)) stream 0,
              armStreamReward hK (c * (sigma2 : Real)) stream 0))
          (armStreamMeasure nu))
    (hcond : forall i : Nat,
      condDistrib
          (fun omega : Omega =>
            (action omega (i + 1), reward omega (i + 1)))
          (fun omega : Omega =>
            History.finitePairHistoryOfTrace
              (action omega) (reward omega) i)
          mu =ᵐ[mu.map (fun omega : Omega =>
            History.finitePairHistoryOfTrace
              (action omega) (reward omega) i)]
        condDistrib
          (fun stream : ArmRewardStream K =>
            (armStreamAction hK (c * (sigma2 : Real)) stream (i + 1),
              armStreamReward hK (c * (sigma2 : Real)) stream (i + 1)))
          (fun stream : ArmRewardStream K =>
            History.finitePairHistoryOfTrace
              (armStreamAction hK (c * (sigma2 : Real)) stream)
              (armStreamReward hK (c * (sigma2 : Real)) stream) i)
          (armStreamMeasure nu)) :
    IdentDistrib
      (fun omega t => (action omega t, reward omega t))
      (fun stream t =>
        (armStreamAction hK (c * (sigma2 : Real)) stream t,
          armStreamReward hK (c * (sigma2 : Real)) stream t))
      mu (armStreamMeasure nu) := by
  let canonicalPair : ArmRewardStream K -> RewardTrace (Fin K × Real) :=
    fun stream t =>
      (armStreamAction hK (c * (sigma2 : Real)) stream t,
        armStreamReward hK (c * (sigma2 : Real)) stream t)
  let mu0 : Measure (Fin K × Real) :=
    Measure.map (fun stream => canonicalPair stream 0) (armStreamMeasure nu)
  let pairKernel : (i : Nat) ->
      Kernel (History.FinitePairHistory (Fin K) Real i) (Fin K × Real) :=
    fun i => condDistrib
      (fun stream => canonicalPair stream (i + 1))
      (fun stream => History.finiteRewardHistoryOfTrace
        (canonicalPair stream) i)
      (armStreamMeasure nu)
  have hcanonicalPair : forall t : Nat,
      Measurable (fun stream => canonicalPair stream t) := by
    intro t
    exact Measurable.prod
      (measurable_armStreamAction hK (c * (sigma2 : Real)) t)
      (measurable_armStreamReward hK (c * (sigma2 : Real)) t)
  letI : IsProbabilityMeasure mu0 :=
    Measure.isProbabilityMeasure_map (hcanonicalPair 0).aemeasurable
  apply RewardKernel.identDistrib_rewardTrace_of_common_condDistrib
    mu (armStreamMeasure nu) mu0
    (fun omega t => (action omega t, reward omega t)) canonicalPair
    (fun t => Measurable.prod (haction t) (hreward t))
    hcanonicalPair pairKernel
  · simpa [mu0, canonicalPair] using hzero
  · rfl
  · intro i
    simpa only [pairKernel, canonicalPair,
      History.finiteRewardHistoryOfTrace,
      History.finitePairHistoryOfTrace] using hcond i
  · intro i
    exact Filter.Eventually.of_forall (fun _history => rfl)

/--
An external process has the canonical observable UCB trajectory law from the
four split law surfaces used by LML's `IsAlgEnvSeq`: the initial action law,
the initial feedback law given that action, the successor action law given
finite pair history, and the successor feedback law given history and the next
action. The canonical split kernels and their `compProd` pair kernels are
chosen internally.
-/
theorem identDistrib_actionRewardTrace_of_split_condDistrib_eq_armStream
    {Omega : Type*} [MeasurableSpace Omega]
    {K : Nat} [NeZero K] (hK : 0 < K) (c : Real) (sigma2 : NNReal)
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu]
    (action : Omega -> ActionTrace (Fin K))
    (reward : Omega -> RewardTrace Real)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (hzeroAction : Measure.map (fun omega : Omega => action omega 0) mu =
      Measure.map
        (fun stream : ArmRewardStream K =>
          armStreamAction hK (c * (sigma2 : Real)) stream 0)
        (armStreamMeasure nu))
    (hzeroFeedback :
      condDistrib (fun omega : Omega => reward omega 0)
          (fun omega : Omega => action omega 0) mu =ᵐ[
            mu.map (fun omega : Omega => action omega 0)]
        condDistrib
          (fun stream : ArmRewardStream K =>
            armStreamReward hK (c * (sigma2 : Real)) stream 0)
          (fun stream : ArmRewardStream K =>
            armStreamAction hK (c * (sigma2 : Real)) stream 0)
          (armStreamMeasure nu))
    (hcondAction : forall i : Nat,
      condDistrib (fun omega : Omega => action omega (i + 1))
          (fun omega : Omega =>
            History.finitePairHistoryOfTrace
              (action omega) (reward omega) i) mu =ᵐ[
            mu.map (fun omega : Omega =>
              History.finitePairHistoryOfTrace
                (action omega) (reward omega) i)]
        condDistrib
          (fun stream : ArmRewardStream K =>
            armStreamAction hK (c * (sigma2 : Real)) stream (i + 1))
          (fun stream : ArmRewardStream K =>
            History.finitePairHistoryOfTrace
              (armStreamAction hK (c * (sigma2 : Real)) stream)
              (armStreamReward hK (c * (sigma2 : Real)) stream) i)
          (armStreamMeasure nu))
    (hcondFeedback : forall i : Nat,
      condDistrib (fun omega : Omega => reward omega (i + 1))
          (fun omega : Omega =>
            (History.finitePairHistoryOfTrace
                (action omega) (reward omega) i,
              action omega (i + 1))) mu =ᵐ[
            mu.map (fun omega : Omega =>
              (History.finitePairHistoryOfTrace
                  (action omega) (reward omega) i,
                action omega (i + 1)))]
        condDistrib
          (fun stream : ArmRewardStream K =>
            armStreamReward hK (c * (sigma2 : Real)) stream (i + 1))
          (fun stream : ArmRewardStream K =>
            (History.finitePairHistoryOfTrace
                (armStreamAction hK (c * (sigma2 : Real)) stream)
                (armStreamReward hK (c * (sigma2 : Real)) stream) i,
              armStreamAction hK (c * (sigma2 : Real)) stream (i + 1)))
          (armStreamMeasure nu)) :
    IdentDistrib
      (fun omega t => (action omega t, reward omega t))
      (fun stream t =>
        (armStreamAction hK (c * (sigma2 : Real)) stream t,
          armStreamReward hK (c * (sigma2 : Real)) stream t))
      mu (armStreamMeasure nu) := by
  let canonicalAction : ArmRewardStream K -> ActionTrace (Fin K) :=
    armStreamAction hK (c * (sigma2 : Real))
  let canonicalReward : ArmRewardStream K -> RewardTrace Real :=
    armStreamReward hK (c * (sigma2 : Real))
  let p0 : Measure (Fin K) :=
    Measure.map (fun stream => canonicalAction stream 0) (armStreamMeasure nu)
  let feedback0 : Kernel (Fin K) Real :=
    condDistrib (fun stream => canonicalReward stream 0)
      (fun stream => canonicalAction stream 0) (armStreamMeasure nu)
  let actionKernel : (i : Nat) ->
      Kernel (History.FinitePairHistory (Fin K) Real i) (Fin K) :=
    fun i => condDistrib (fun stream => canonicalAction stream (i + 1))
      (fun stream => History.finitePairHistoryOfTrace
        (canonicalAction stream) (canonicalReward stream) i)
      (armStreamMeasure nu)
  let feedbackKernel : (i : Nat) ->
      Kernel (History.FinitePairHistory (Fin K) Real i × Fin K) Real :=
    fun i => condDistrib (fun stream => canonicalReward stream (i + 1))
      (fun stream =>
        (History.finitePairHistoryOfTrace
            (canonicalAction stream) (canonicalReward stream) i,
          canonicalAction stream (i + 1)))
      (armStreamMeasure nu)
  let mu0 : Measure (Fin K × Real) := p0 ⊗ₘ feedback0
  let pairKernel : (i : Nat) ->
      Kernel (History.FinitePairHistory (Fin K) Real i) (Fin K × Real) :=
    fun i => actionKernel i ⊗ₖ feedbackKernel i
  have hcanonicalAction : forall t : Nat,
      Measurable (fun stream => canonicalAction stream t) := by
    intro t
    exact measurable_armStreamAction hK (c * (sigma2 : Real)) t
  have hcanonicalReward : forall t : Nat,
      Measurable (fun stream => canonicalReward stream t) := by
    intro t
    exact measurable_armStreamReward hK (c * (sigma2 : Real)) t
  letI : IsProbabilityMeasure p0 :=
    Measure.isProbabilityMeasure_map (hcanonicalAction 0).aemeasurable
  letI : IsProbabilityMeasure mu0 := by
    dsimp only [mu0]
    infer_instance
  letI : forall i, IsMarkovKernel (pairKernel i) := by
    intro i
    dsimp only [pairKernel]
    infer_instance
  apply RewardKernel.identDistrib_rewardTrace_of_common_condDistrib
    mu (armStreamMeasure nu) mu0
    (fun omega t => (action omega t, reward omega t))
    (fun stream t => (canonicalAction stream t, canonicalReward stream t))
    (fun t => Measurable.prod (haction t) (hreward t))
    (fun t => Measurable.prod (hcanonicalAction t) (hcanonicalReward t))
    pairKernel
  · exact RewardKernel.pair_map_eq_compProd_of_map_eq_of_condDistrib
      mu (fun omega => action omega 0) (fun omega => reward omega 0)
      (hreward 0) p0 feedback0 (by simpa [p0, canonicalAction] using hzeroAction)
      (by simpa [feedback0, canonicalAction, canonicalReward] using hzeroFeedback)
  · exact RewardKernel.pair_map_eq_compProd_of_map_eq_of_condDistrib
      (armStreamMeasure nu) (fun stream => canonicalAction stream 0)
      (fun stream => canonicalReward stream 0) (hcanonicalReward 0)
      p0 feedback0 rfl (Filter.Eventually.of_forall (fun _action => rfl))
  · intro i
    exact RewardKernel.condDistrib_pair_ae_eq_compProd_of_split
      mu
      (fun omega => History.finitePairHistoryOfTrace
        (action omega) (reward omega) i)
      (History.measurable_finitePairHistoryOfTrace action reward haction hreward i)
      (fun omega => action omega (i + 1)) (haction (i + 1))
      (fun omega => reward omega (i + 1)) (hreward (i + 1))
      (actionKernel i) (feedbackKernel i)
      (by simpa [actionKernel, canonicalAction, canonicalReward] using hcondAction i)
      (by simpa [feedbackKernel, canonicalAction, canonicalReward] using hcondFeedback i)
  · intro i
    exact RewardKernel.condDistrib_pair_ae_eq_compProd_of_split
      (armStreamMeasure nu)
      (fun stream => History.finitePairHistoryOfTrace
        (canonicalAction stream) (canonicalReward stream) i)
      (History.measurable_finitePairHistoryOfTrace
        canonicalAction canonicalReward hcanonicalAction hcanonicalReward i)
      (fun stream => canonicalAction stream (i + 1)) (hcanonicalAction (i + 1))
      (fun stream => canonicalReward stream (i + 1)) (hcanonicalReward (i + 1))
      (actionKernel i) (feedbackKernel i)
      (Filter.Eventually.of_forall (fun _history => rfl))
      (Filter.Eventually.of_forall (fun _historyAction => rfl))

/--
Exact canonical arm-stream UCB regret from the four split action/feedback law
fields corresponding to LML's `IsAlgEnvSeq` interface.
-/
theorem integral_realKernelRegret_externalAction_le_lml_sum_of_split_condDistrib_eq_armStream
    {Omega : Type*} [MeasurableSpace Omega]
    {K : Nat} [NeZero K] (hK : 0 < K) (c : Real) (sigma2 : NNReal)
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu]
    (action : Omega -> ActionTrace (Fin K))
    (reward : Omega -> RewardTrace Real)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (hzeroAction : Measure.map (fun omega : Omega => action omega 0) mu =
      Measure.map
        (fun stream : ArmRewardStream K =>
          armStreamAction hK (c * (sigma2 : Real)) stream 0)
        (armStreamMeasure nu))
    (hzeroFeedback :
      condDistrib (fun omega : Omega => reward omega 0)
          (fun omega : Omega => action omega 0) mu =ᵐ[
            mu.map (fun omega : Omega => action omega 0)]
        condDistrib
          (fun stream : ArmRewardStream K =>
            armStreamReward hK (c * (sigma2 : Real)) stream 0)
          (fun stream : ArmRewardStream K =>
            armStreamAction hK (c * (sigma2 : Real)) stream 0)
          (armStreamMeasure nu))
    (hcondAction : forall i : Nat,
      condDistrib (fun omega : Omega => action omega (i + 1))
          (fun omega : Omega =>
            History.finitePairHistoryOfTrace
              (action omega) (reward omega) i) mu =ᵐ[
            mu.map (fun omega : Omega =>
              History.finitePairHistoryOfTrace
                (action omega) (reward omega) i)]
        condDistrib
          (fun stream : ArmRewardStream K =>
            armStreamAction hK (c * (sigma2 : Real)) stream (i + 1))
          (fun stream : ArmRewardStream K =>
            History.finitePairHistoryOfTrace
              (armStreamAction hK (c * (sigma2 : Real)) stream)
              (armStreamReward hK (c * (sigma2 : Real)) stream) i)
          (armStreamMeasure nu))
    (hcondFeedback : forall i : Nat,
      condDistrib (fun omega : Omega => reward omega (i + 1))
          (fun omega : Omega =>
            (History.finitePairHistoryOfTrace
                (action omega) (reward omega) i,
              action omega (i + 1))) mu =ᵐ[
            mu.map (fun omega : Omega =>
              (History.finitePairHistoryOfTrace
                  (action omega) (reward omega) i,
                action omega (i + 1)))]
        condDistrib
          (fun stream : ArmRewardStream K =>
            armStreamReward hK (c * (sigma2 : Real)) stream (i + 1))
          (fun stream : ArmRewardStream K =>
            (History.finitePairHistoryOfTrace
                (armStreamAction hK (c * (sigma2 : Real)) stream)
                (armStreamReward hK (c * (sigma2 : Real)) stream) i,
              armStreamAction hK (c * (sigma2 : Real)) stream (i + 1)))
          (armStreamMeasure nu))
    (n : Nat) (hc : 0 < c) (hsigma2 : sigma2 ≠ 0)
    (hsubG : forall arm : Fin K, HasSubgaussianMGF
      (fun x => x - realKernelMean nu arm) sigma2 (nu arm)) :
    integral mu (fun omega => realKernelRegret nu (action omega) n) <=
      (Finset.univ : Finset (Fin K)).sum (fun arm =>
        8 * c * (sigma2 : Real) * Real.log ((n + 1 : Nat) : Real) /
            realKernelGap nu arm +
          realKernelGap nu arm * (2 + 2 * (constSum c n).toReal)) := by
  exact
    integral_realKernelRegret_externalAction_le_lml_sum_of_identDistrib_actionRewardTrace
      hK c sigma2 mu nu action reward
      (identDistrib_actionRewardTrace_of_split_condDistrib_eq_armStream
        hK c sigma2 mu nu action reward haction hreward hzeroAction
        hzeroFeedback hcondAction hcondFeedback)
      n hc hsigma2 hsubG

/--
Exact LML-shaped regret when the external initial and successor observable pair
laws agree directly with canonical arm-stream UCB.
-/
theorem integral_realKernelRegret_externalAction_le_lml_sum_of_condDistrib_eq_armStream
    {Omega : Type*} [MeasurableSpace Omega]
    {K : Nat} [NeZero K] (hK : 0 < K) (c : Real) (sigma2 : NNReal)
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu]
    (action : Omega -> ActionTrace (Fin K))
    (reward : Omega -> RewardTrace Real)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (hzero : Measure.map
      (fun omega : Omega => (action omega 0, reward omega 0)) mu =
        Measure.map
          (fun stream : ArmRewardStream K =>
            (armStreamAction hK (c * (sigma2 : Real)) stream 0,
              armStreamReward hK (c * (sigma2 : Real)) stream 0))
          (armStreamMeasure nu))
    (hcond : forall i : Nat,
      condDistrib
          (fun omega : Omega =>
            (action omega (i + 1), reward omega (i + 1)))
          (fun omega : Omega =>
            History.finitePairHistoryOfTrace
              (action omega) (reward omega) i)
          mu =ᵐ[mu.map (fun omega : Omega =>
            History.finitePairHistoryOfTrace
              (action omega) (reward omega) i)]
        condDistrib
          (fun stream : ArmRewardStream K =>
            (armStreamAction hK (c * (sigma2 : Real)) stream (i + 1),
              armStreamReward hK (c * (sigma2 : Real)) stream (i + 1)))
          (fun stream : ArmRewardStream K =>
            History.finitePairHistoryOfTrace
              (armStreamAction hK (c * (sigma2 : Real)) stream)
              (armStreamReward hK (c * (sigma2 : Real)) stream) i)
          (armStreamMeasure nu))
    (n : Nat) (hc : 0 < c) (hsigma2 : sigma2 ≠ 0)
    (hsubG : forall arm : Fin K, HasSubgaussianMGF
      (fun x => x - realKernelMean nu arm) sigma2 (nu arm)) :
    integral mu (fun omega => realKernelRegret nu (action omega) n) <=
      (Finset.univ : Finset (Fin K)).sum (fun arm =>
        8 * c * (sigma2 : Real) * Real.log ((n + 1 : Nat) : Real) /
            realKernelGap nu arm +
          realKernelGap nu arm * (2 + 2 * (constSum c n).toReal)) := by
  exact
    integral_realKernelRegret_externalAction_le_lml_sum_of_identDistrib_actionRewardTrace
      hK c sigma2 mu nu action reward
      (identDistrib_actionRewardTrace_of_condDistrib_eq_armStream
        hK c sigma2 mu nu action reward haction hreward hzero hcond)
      n hc hsigma2 hsubG

end UCB
end BanditRLProof
