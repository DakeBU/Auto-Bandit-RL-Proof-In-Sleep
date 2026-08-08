import BanditRLProof.RL.FiniteHorizonNaturalCausalInverseSqrtThresholdUnboundedHittingAfterExpectedPositivePartConsistency
import BanditRLProof.RL.FiniteHorizonNaturalCausalInverseSqrtThresholdUnboundedHittingAfterPolynomialSecondMomentExpectedAbsoluteAsymptotics
import BanditRLProof.UnboundedStoppingTimeWeightedL2CoordinateIntegrability
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# L1 consistency at the uncapped inverse-sqrt hitting time

The positive part of the stopped average is already controlled by the hit
threshold.  For a delayed finite hit, first-hit minimality makes the previous
average positive, so the negative overshoot can only come from the final
successor-batch realized-regret coordinate divided by the hit index.  A
square-summable reciprocal weight and uniform coordinate L2 control then make
that overshoot vanish.  This is not optional stopping.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal ProbabilityTheory Topology

namespace BanditRLProof.FiniteHorizonRL

universe u v

variable {State : Type u} {Action : Type v}
    [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action]
    [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action]

namespace HeterogeneousAdaptiveStochasticEpisodeBatchSource

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] in
/-- Exact one-step recursion for the natural round-average realized regret. -/
theorem naturalAverageRealizedBehaviorRegret_succ_eq
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat -> Nat}
    (source : HeterogeneousAdaptiveStochasticEpisodeBatchSource
      mdp initialState episodes)
    (trajectory : HeterogeneousStochasticEpisodeBatchTrajectory mdp episodes)
    (n : Nat) :
    source.naturalAverageRealizedBehaviorRegret trajectory (n + 1) =
      ((n : Real) *
          source.naturalAverageRealizedBehaviorRegret trajectory n +
        source.naturalSuccessorBatchAverageRealizedRegret trajectory n) /
        ((n + 1 : Nat) : Real) := by
  unfold naturalAverageRealizedBehaviorRegret
    naturalCumulativeRealizedBehaviorRegret
  rw [Finset.sum_range_succ]
  by_cases hn : n = 0
  · subst n
    norm_num
  · have hnReal : (n : Real) ≠ 0 := by exact_mod_cast hn
    have hsuccReal : ((n + 1 : Nat) : Real) ≠ 0 := by positivity
    field_simp [hnReal, hsuccReal]

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action] in
/-- A conditional successor-average return MGF also gives its unconditional
sub-Gaussian MGF on the trajectory measure. -/
theorem
    trajectoryMeasure_naturalSuccessorAverageReturnDeviationIncrement_succ_hasSubgaussianMGF
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat -> Nat}
    [StandardBorelSpace State] [StandardBorelSpace Action]
    (source : HeterogeneousAdaptiveStochasticEpisodeBatchSource
      mdp initialState episodes) [source.GlobalReturnMeasurability] (n : Nat)
    [StandardBorelSpace
      (HeterogeneousStochasticEpisodeBatchPrefix mdp episodes n)]
    [Nonempty (HeterogeneousStochasticEpisodeBatchPrefix mdp episodes n)]
    [StandardBorelSpace
      (StochasticEpisodeBatch mdp (episodes (n + 1)))]
    [Nonempty (StochasticEpisodeBatch mdp (episodes (n + 1)))]
    [StandardBorelSpace
      (HeterogeneousStochasticEpisodeBatchTrajectory mdp episodes)]
    (rewardBound rewardVarianceProxy : NNReal)
    (hrewardBound : forall state action,
      |mdp.reward state action| <= (rewardBound : Real))
    (law : source.rewardSource.UniformSubgaussianRewardLaw
      rewardVarianceProxy) :
    HasSubgaussianMGF
      (source.naturalSuccessorAverageReturnDeviationIncrement (n + 1))
      (naturalSuccessorAverageReturnVarianceProxyAt mdp episodes (n + 1)
        rewardBound rewardVarianceProxy)
      source.trajectoryMeasure := by
  let F := Filtration.piLE
    (X := fun k : Nat => StochasticEpisodeBatch mdp (episodes k))
  have hzeroGlobal : HasSubgaussianMGF
      (fun _trajectory : HeterogeneousStochasticEpisodeBatchTrajectory mdp
        episodes => 0) 0 source.trajectoryMeasure := by
    exact HasSubgaussianMGF.fun_zero
  have hzero := HasSubgaussianMGF.trim (F.le n) measurable_const hzeroGlobal
  have hcond :=
    source.naturalSuccessorAverageReturnDeviationIncrement_succ_hasCondSubgaussianMGF
      n rewardBound rewardVarianceProxy hrewardBound law
  have hsum := HasSubgaussianMGF.add_of_hasCondSubgaussianMGF
    (F.le n) hzero hcond
  have hzero_add :
      (fun _trajectory : HeterogeneousStochasticEpisodeBatchTrajectory mdp
          episodes => 0) +
          source.naturalSuccessorAverageReturnDeviationIncrement (n + 1) =
        source.naturalSuccessorAverageReturnDeviationIncrement (n + 1) := by
    funext trajectory
    simp
  rw [hzero_add, zero_add] at hsum
  exact hsum

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- A positive successor batch contributes at most one one-episode return
variance proxy after normalization by its batch size. -/
theorem
    naturalSuccessorAverageReturnVarianceProxyAt_succ_le_globalReturnDeviationPerEpisodeVarianceProxy
    (mdp : MDP State Action) (episodes : Nat -> Nat) (n : Nat)
    (rewardBound rewardVarianceProxy : NNReal)
    (hepisodes : 0 < episodes (n + 1)) :
    naturalSuccessorAverageReturnVarianceProxyAt mdp episodes (n + 1)
        rewardBound rewardVarianceProxy <=
      mdp.globalReturnDeviationPerEpisodeVarianceProxy
        rewardBound rewardVarianceProxy := by
  rw [naturalSuccessorAverageReturnVarianceProxyAt,
    MDP.iidGlobalSampledCumulativeReturnDeviationVarianceProxy_eq]
  have he : (episodes (n + 1) : NNReal) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hepisodes)
  have he_one : (1 : NNReal) <= (episodes (n + 1) : NNReal) := by
    exact_mod_cast hepisodes
  have hinv : (episodes (n + 1) : NNReal)⁻¹ <= 1 :=
    inv_le_one_of_one_le₀ he_one
  calc
    ((episodes (n + 1) : NNReal)⁻¹) ^ 2 *
          ((episodes (n + 1) : NNReal) *
            mdp.globalReturnDeviationPerEpisodeVarianceProxy
              rewardBound rewardVarianceProxy) =
        (episodes (n + 1) : NNReal)⁻¹ *
          mdp.globalReturnDeviationPerEpisodeVarianceProxy
            rewardBound rewardVarianceProxy := by
      field_simp [he]
    _ <= 1 * mdp.globalReturnDeviationPerEpisodeVarianceProxy
          rewardBound rewardVarianceProxy :=
      mul_le_mul_of_nonneg_right hinv (zero_le _)
    _ = mdp.globalReturnDeviationPerEpisodeVarianceProxy
          rewardBound rewardVarianceProxy := one_mul _

/-- Uniform deterministic second-moment envelope for one successor-batch
average realized-regret coordinate. -/
noncomputable def naturalSuccessorBatchAverageRealizedRegretSecondMomentEnvelope
    (mdp : MDP State Action) (rewardVarianceProxy : NNReal) : Real :=
  8 * (mdp.horizon : Real) ^ 2 +
    8 * (mdp.globalReturnDeviationPerEpisodeVarianceProxy 1
      rewardVarianceProxy : Real) * Real.exp (1 / 2 : Real)

/-- Every positive-count successor-batch average realized-regret coordinate
belongs to `L2`. -/
theorem memLp_two_naturalSuccessorBatchAverageRealizedRegret
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat -> Nat}
    [StandardBorelSpace State] [StandardBorelSpace Action]
    [forall n, StandardBorelSpace
      (HeterogeneousStochasticEpisodeBatchPrefix mdp episodes n)]
    [forall n, Nonempty
      (HeterogeneousStochasticEpisodeBatchPrefix mdp episodes n)]
    [forall n, StandardBorelSpace (StochasticEpisodeBatch mdp (episodes n))]
    [forall n, Nonempty (StochasticEpisodeBatch mdp (episodes n))]
    [StandardBorelSpace
      (HeterogeneousStochasticEpisodeBatchTrajectory mdp episodes)]
    (source : HeterogeneousAdaptiveStochasticEpisodeBatchSource
      mdp initialState episodes) [source.GlobalReturnMeasurability]
    (rewardVarianceProxy : NNReal)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (law : source.rewardSource.UniformSubgaussianRewardLaw rewardVarianceProxy)
    (n : Nat) (hepisodes : 0 < episodes (n + 1)) :
    MemLp (fun trajectory =>
      source.naturalSuccessorBatchAverageRealizedRegret trajectory n) 2
      source.trajectoryMeasure := by
  let deviation :=
    source.naturalSuccessorAverageReturnDeviationIncrement (n + 1)
  have hdeviationMGF : HasSubgaussianMGF deviation
      (naturalSuccessorAverageReturnVarianceProxyAt mdp episodes (n + 1)
        1 rewardVarianceProxy) source.trajectoryMeasure := by
    simpa only [deviation] using
      source.trajectoryMeasure_naturalSuccessorAverageReturnDeviationIncrement_succ_hasSubgaussianMGF
        n 1 rewardVarianceProxy hrewardBound law
  have hmajorant : MemLp
      (fun trajectory => 2 * (mdp.horizon : Real) + |deviation trajectory|)
      2 source.trajectoryMeasure :=
    (memLp_const (2 * (mdp.horizon : Real))).add (hdeviationMGF.memLp 2).abs
  refine hmajorant.mono'
    (source.measurable_naturalSuccessorBatchAverageRealizedRegret n
      |>.aestronglyMeasurable) ?_
  exact Filter.Eventually.of_forall fun trajectory => by
    rw [Real.norm_eq_abs,
      source.naturalSuccessorBatchAverageRealizedRegret_eq_expected_sub_deviation
        trajectory n hepisodes]
    calc
      |(source.successorPolicyAt trajectory n).expectedRegret initialState -
          deviation trajectory| <=
          |(source.successorPolicyAt trajectory n).expectedRegret initialState| +
            |deviation trajectory| := abs_sub _ _
      _ = (source.successorPolicyAt trajectory n).expectedRegret initialState +
            |deviation trajectory| := by
        rw [abs_of_nonneg
          ((source.successorPolicyAt trajectory n).expectedRegret_nonneg
            initialState)]
      _ <= 2 * (mdp.horizon : Real) + |deviation trajectory| := by
        gcongr
        exact MarkovPolicy.expectedRegret_le_two_mul_horizon_of_rewardBound
          (source.successorPolicyAt trajectory n) initialState hrewardBound

/-- The second moment of every positive-count successor-batch average
realized-regret coordinate is bounded by the uniform envelope. -/
theorem integral_sq_naturalSuccessorBatchAverageRealizedRegret_le_secondMomentEnvelope
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat -> Nat}
    [StandardBorelSpace State] [StandardBorelSpace Action]
    [forall n, StandardBorelSpace
      (HeterogeneousStochasticEpisodeBatchPrefix mdp episodes n)]
    [forall n, Nonempty
      (HeterogeneousStochasticEpisodeBatchPrefix mdp episodes n)]
    [forall n, StandardBorelSpace (StochasticEpisodeBatch mdp (episodes n))]
    [forall n, Nonempty (StochasticEpisodeBatch mdp (episodes n))]
    [StandardBorelSpace
      (HeterogeneousStochasticEpisodeBatchTrajectory mdp episodes)]
    (source : HeterogeneousAdaptiveStochasticEpisodeBatchSource
      mdp initialState episodes) [source.GlobalReturnMeasurability]
    (rewardVarianceProxy : NNReal)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (law : source.rewardSource.UniformSubgaussianRewardLaw rewardVarianceProxy)
    (n : Nat) (hepisodes : 0 < episodes (n + 1)) :
    integral source.trajectoryMeasure (fun trajectory =>
        source.naturalSuccessorBatchAverageRealizedRegret trajectory n ^ 2) <=
      naturalSuccessorBatchAverageRealizedRegretSecondMomentEnvelope mdp
        rewardVarianceProxy := by
  let deviation :=
    source.naturalSuccessorAverageReturnDeviationIncrement (n + 1)
  let returnProxy :=
    naturalSuccessorAverageReturnVarianceProxyAt mdp episodes (n + 1)
      1 rewardVarianceProxy
  have hdeviationMGF : HasSubgaussianMGF deviation returnProxy
      source.trajectoryMeasure := by
    simpa only [deviation, returnProxy] using
      source.trajectoryMeasure_naturalSuccessorAverageReturnDeviationIncrement_succ_hasSubgaussianMGF
        n 1 rewardVarianceProxy hrewardBound law
  have hdeviationMoment :
      integral source.trajectoryMeasure
          (fun trajectory => deviation trajectory ^ 2) <=
        4 * (returnProxy : Real) * Real.exp (1 / 2 : Real) :=
    Concentration.integral_sq_le_four_mul_proxy_mul_exp_half_of_hasSubgaussianMGF
      source.trajectoryMeasure deviation returnProxy hdeviationMGF
  have hreturnProxy : returnProxy <=
      mdp.globalReturnDeviationPerEpisodeVarianceProxy 1 rewardVarianceProxy := by
    simpa only [returnProxy] using
      naturalSuccessorAverageReturnVarianceProxyAt_succ_le_globalReturnDeviationPerEpisodeVarianceProxy
        mdp episodes n 1 rewardVarianceProxy hepisodes
  have hcoordinateSqIntegrable : Integrable (fun trajectory =>
      source.naturalSuccessorBatchAverageRealizedRegret trajectory n ^ 2)
      source.trajectoryMeasure :=
    (source.memLp_two_naturalSuccessorBatchAverageRealizedRegret
      rewardVarianceProxy hrewardBound law n hepisodes).integrable_sq
  have hdeviationSqIntegrable : Integrable
      (fun trajectory => deviation trajectory ^ 2) source.trajectoryMeasure :=
    (hdeviationMGF.memLp 2).integrable_sq
  have hpoint : forall trajectory,
      source.naturalSuccessorBatchAverageRealizedRegret trajectory n ^ 2 <=
        8 * (mdp.horizon : Real) ^ 2 + 2 * deviation trajectory ^ 2 := by
    intro trajectory
    have hexpected_nonneg : 0 <=
        (source.successorPolicyAt trajectory n).expectedRegret initialState :=
      (source.successorPolicyAt trajectory n).expectedRegret_nonneg initialState
    have hexpected_le :
        (source.successorPolicyAt trajectory n).expectedRegret initialState <=
          2 * (mdp.horizon : Real) :=
      MarkovPolicy.expectedRegret_le_two_mul_horizon_of_rewardBound
        (source.successorPolicyAt trajectory n) initialState hrewardBound
    have hhorizon_nonneg : 0 <= 2 * (mdp.horizon : Real) := by positivity
    have hexpected_sq :
        (source.successorPolicyAt trajectory n).expectedRegret initialState ^ 2 <=
          (2 * (mdp.horizon : Real)) ^ 2 :=
      (sq_le_sq₀ hexpected_nonneg hhorizon_nonneg).2 hexpected_le
    rw [source.naturalSuccessorBatchAverageRealizedRegret_eq_expected_sub_deviation
      trajectory n hepisodes]
    calc
      ((source.successorPolicyAt trajectory n).expectedRegret initialState -
          deviation trajectory) ^ 2 <=
          2 * (source.successorPolicyAt trajectory n).expectedRegret
              initialState ^ 2 + 2 * deviation trajectory ^ 2 := by
        nlinarith [sq_nonneg
          ((source.successorPolicyAt trajectory n).expectedRegret initialState +
            deviation trajectory)]
      _ <= 2 * (2 * (mdp.horizon : Real)) ^ 2 +
          2 * deviation trajectory ^ 2 := by gcongr
      _ = 8 * (mdp.horizon : Real) ^ 2 +
          2 * deviation trajectory ^ 2 := by ring
  have hrhsIntegrable : Integrable (fun trajectory =>
      8 * (mdp.horizon : Real) ^ 2 + 2 * deviation trajectory ^ 2)
      source.trajectoryMeasure :=
    (integrable_const (8 * (mdp.horizon : Real) ^ 2)).add
      (hdeviationSqIntegrable.const_mul 2)
  calc
    integral source.trajectoryMeasure (fun trajectory =>
        source.naturalSuccessorBatchAverageRealizedRegret trajectory n ^ 2) <=
        integral source.trajectoryMeasure (fun trajectory =>
          8 * (mdp.horizon : Real) ^ 2 + 2 * deviation trajectory ^ 2) :=
      integral_mono hcoordinateSqIntegrable hrhsIntegrable hpoint
    _ = 8 * (mdp.horizon : Real) ^ 2 +
        2 * integral source.trajectoryMeasure
          (fun trajectory => deviation trajectory ^ 2) := by
      rw [integral_add (integrable_const (8 * (mdp.horizon : Real) ^ 2))
          (hdeviationSqIntegrable.const_mul 2), integral_const,
        integral_const_mul]
      simp [MeasureTheory.probReal_univ]
    _ <= 8 * (mdp.horizon : Real) ^ 2 +
        2 * (4 * (returnProxy : Real) * Real.exp (1 / 2 : Real)) := by
      gcongr
    _ <= 8 * (mdp.horizon : Real) ^ 2 +
        2 * (4 *
          (mdp.globalReturnDeviationPerEpisodeVarianceProxy 1
            rewardVarianceProxy : Real) * Real.exp (1 / 2 : Real)) := by
      gcongr
    _ = naturalSuccessorBatchAverageRealizedRegretSecondMomentEnvelope mdp
        rewardVarianceProxy := by
      unfold naturalSuccessorBatchAverageRealizedRegretSecondMomentEnvelope
      ring

end HeterogeneousAdaptiveStochasticEpisodeBatchSource

namespace AdaptiveStochasticSampledEmpiricalOptimisticSource

/-- If the previous average is nonnegative, one new coordinate can create at
most its absolute value divided by the new sample count as negative
overshoot. -/
theorem max_neg_natWeightedAverage_succ_le_abs_increment_div
    (n : Nat) (previous increment : Real) (hprevious : 0 <= previous) :
    max (-(((n : Real) * previous + increment) /
        ((n + 1 : Nat) : Real))) 0 <=
      |increment| / ((n + 1 : Nat) : Real) := by
  have hdenom : 0 < ((n + 1 : Nat) : Real) := by positivity
  apply max_le
  · rw [show -(((n : Real) * previous + increment) /
        ((n + 1 : Nat) : Real)) =
      (-((n : Real) * previous + increment)) /
        ((n + 1 : Nat) : Real) by ring]
    apply (div_le_div_iff_of_pos_right hdenom).2
    have hnprev : 0 <= (n : Real) * previous :=
      mul_nonneg (by positivity) hprevious
    nlinarith [neg_le_abs increment]
  · positivity

/-- A delayed finite `hittingAfter` has a predecessor outside the target
lower interval. -/
theorem hittingAfter_predecessor_gt_of_untopA_gt_base
    {Omega : Type*} (process : Nat -> Omega -> Real)
    (threshold : Real) (base : Nat) (omega : Omega)
    (hfinite :
      MeasureTheory.hittingAfter process (Set.Iic threshold) base omega ≠ ⊤)
    (hdelayed :
      base <
        (MeasureTheory.hittingAfter process (Set.Iic threshold) base omega).untopA) :
    threshold <
      process
        ((MeasureTheory.hittingAfter process (Set.Iic threshold) base omega).untopA - 1)
        omega := by
  let tau := MeasureTheory.hittingAfter process (Set.Iic threshold) base omega
  let hit := tau.untopA
  have hhitPos : 0 < hit := lt_of_le_of_lt (Nat.zero_le base) hdelayed
  have hpredLtNat : hit - 1 < hit := Nat.sub_lt hhitPos Nat.one_pos
  have hcoe : (hit : WithTop Nat) = tau := by
    dsimp only [hit]
    rw [WithTop.untopA_eq_untop hfinite]
    exact WithTop.coe_untop _ hfinite
  have hpredLt : ((hit - 1 : Nat) : WithTop Nat) < tau := by
    rw [← hcoe]
    exact_mod_cast hpredLtNat
  have hbasePred : base <= hit - 1 := Nat.le_pred_of_lt hdelayed
  have hnot := MeasureTheory.notMem_of_lt_hittingAfter
    (u := process) (s := Set.Iic threshold) hpredLt hbasePred
  simpa only [tau, hit, Set.mem_Iic, not_le] using hnot

/-- Reciprocal overshoot weight, active only strictly after the scheduled
base. -/
noncomputable def inverseSqrtThresholdUnboundedHittingAfterDelayedReciprocalWeight
    (base n : Nat) : Real :=
  if base < n then (n : Real)⁻¹ else 0

/-- At a finite first hit of a positive lower threshold, the negative part is
bounded by the base absolute value plus the reciprocal-weighted final
increment. -/
theorem
    max_neg_hittingAfter_untopA_le_base_abs_add_abs_stoppedValue_delayedReciprocalIncrement
    {Omega : Type*} (average increment : Nat -> Omega -> Real)
    (threshold : Real) (hthreshold : 0 < threshold) (base : Nat)
    (omega : Omega)
    (hrecursion : forall n,
      average (n + 1) omega =
        ((n : Real) * average n omega + increment n omega) /
          ((n + 1 : Nat) : Real))
    (hfinite : MeasureTheory.hittingAfter average (Set.Iic threshold) base omega ≠ ⊤) :
    max (-average
        (MeasureTheory.hittingAfter average (Set.Iic threshold) base omega).untopA
        omega) 0 <=
      |average base omega| +
        |stoppedValue
          (fun hit trajectory =>
            inverseSqrtThresholdUnboundedHittingAfterDelayedReciprocalWeight
                base hit *
              increment (hit - 1) trajectory)
          (MeasureTheory.hittingAfter average (Set.Iic threshold) base) omega| := by
  let tau := MeasureTheory.hittingAfter average (Set.Iic threshold) base
  let hit := (tau omega).untopA
  have hcoe : (hit : WithTop Nat) = tau omega := by
    dsimp only [hit]
    rw [WithTop.untopA_eq_untop hfinite]
    exact WithTop.coe_untop _ hfinite
  have hbaseLeTop : (base : WithTop Nat) <= tau omega :=
    MeasureTheory.le_hittingAfter omega
  have hbaseLe : base <= hit := by
    rw [← hcoe] at hbaseLeTop
    exact_mod_cast hbaseLeTop
  by_cases hhitBase : hit = base
  · calc
      max (-average hit omega) 0 <= |average hit omega| :=
        max_le (neg_le_abs _) (abs_nonneg _)
      _ = |average base omega| := by rw [hhitBase]
      _ <= |average base omega| +
          |stoppedValue
            (fun hit trajectory =>
              inverseSqrtThresholdUnboundedHittingAfterDelayedReciprocalWeight
                  base hit *
                increment (hit - 1) trajectory)
            tau omega| := le_add_of_nonneg_right (abs_nonneg _)
  · have hdelayed : base < hit :=
      lt_of_le_of_ne hbaseLe (Ne.symm hhitBase)
    have hhitPos : 0 < hit := lt_of_le_of_lt (Nat.zero_le base) hdelayed
    have hpredPositive : 0 <= average (hit - 1) omega := by
      exact le_trans hthreshold.le
        (hittingAfter_predecessor_gt_of_untopA_gt_base average threshold base
          omega hfinite hdelayed).le
    have hsucc := max_neg_natWeightedAverage_succ_le_abs_increment_div
      (hit - 1) (average (hit - 1) omega) (increment (hit - 1) omega)
        hpredPositive
    have hpredSucc : hit - 1 + 1 = hit := Nat.sub_add_cancel
      (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hhitPos))
    have hovershoot :
        max (-average hit omega) 0 <=
          |increment (hit - 1) omega| / (hit : Real) := by
      simpa only [hpredSucc] using
        (show max (-average (hit - 1 + 1) omega) 0 <=
            |increment (hit - 1) omega| /
              (((hit - 1) + 1 : Nat) : Real) by
          rw [hrecursion (hit - 1)]
          exact hsucc)
    have hstopped :
        |stoppedValue
            (fun index trajectory =>
              inverseSqrtThresholdUnboundedHittingAfterDelayedReciprocalWeight
                  base index *
                increment (index - 1) trajectory)
            tau omega| =
          |increment (hit - 1) omega| / (hit : Real) := by
      have huntopA : (tau omega).untopA = hit := rfl
      simp only [stoppedValue, huntopA]
      rw [inverseSqrtThresholdUnboundedHittingAfterDelayedReciprocalWeight,
        if_pos hdelayed, abs_mul, abs_inv, abs_of_nonneg (by positivity :
          0 <= (hit : Real)), div_eq_mul_inv]
      ring
    calc
      max (-average hit omega) 0 <=
          |increment (hit - 1) omega| / (hit : Real) := hovershoot
      _ = |stoppedValue
            (fun index trajectory =>
              inverseSqrtThresholdUnboundedHittingAfterDelayedReciprocalWeight
                  base index *
                increment (index - 1) trajectory)
            tau omega| := hstopped.symm
      _ <= |average base omega| +
          |stoppedValue
            (fun index trajectory =>
              inverseSqrtThresholdUnboundedHittingAfterDelayedReciprocalWeight
                  base index *
                increment (index - 1) trajectory)
            tau omega| := le_add_of_nonneg_left (abs_nonneg _)

/-- The square of the delayed reciprocal weight is dominated by the classical
inverse-square series. -/
theorem summable_inverseSqrtThresholdUnboundedHittingAfterDelayedReciprocalWeight_sq
    (base : Nat) :
    Summable (fun n =>
      inverseSqrtThresholdUnboundedHittingAfterDelayedReciprocalWeight base n ^ 2) := by
  have hseries : Summable (fun n : Nat => 1 / ((n : Real) ^ 2)) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hcongr :
      (fun n =>
        inverseSqrtThresholdUnboundedHittingAfterDelayedReciprocalWeight base n ^ 2) =
        Set.indicator {n | base < n}
          (fun n : Nat => 1 / ((n : Real) ^ 2)) := by
    funext n
    by_cases hn : base < n
    · simp [inverseSqrtThresholdUnboundedHittingAfterDelayedReciprocalWeight,
        hn, inv_pow]
    · simp [inverseSqrtThresholdUnboundedHittingAfterDelayedReciprocalWeight,
        hn]
  rw [hcongr]
  exact hseries.indicator _

/-- The squared reciprocal tail after a growing base tends to zero. -/
theorem
    inverseSqrtThresholdUnboundedHittingAfterDelayedReciprocalWeight_sq_tsum_tendsto_zero :
    Tendsto
      (fun base => ∑' n : Nat,
        inverseSqrtThresholdUnboundedHittingAfterDelayedReciprocalWeight base n ^ 2)
      atTop (nhds 0) := by
  let bound : Nat -> Real := fun n => 1 / ((n : Real) ^ 2)
  have hbound : Summable bound :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have htendsto := tendsto_tsum_of_dominated_convergence
    (f := fun base n =>
      inverseSqrtThresholdUnboundedHittingAfterDelayedReciprocalWeight base n ^ 2)
    (g := fun _ : Nat => (0 : Real)) hbound
    (fun n => by
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop n] with base hbase
      simp [inverseSqrtThresholdUnboundedHittingAfterDelayedReciprocalWeight,
        not_lt_of_ge hbase])
    (by
      filter_upwards with base n
      by_cases hn : base < n
      · simp [inverseSqrtThresholdUnboundedHittingAfterDelayedReciprocalWeight,
          hn, bound]
      · simp [inverseSqrtThresholdUnboundedHittingAfterDelayedReciprocalWeight,
          hn, bound]
      )
  simpa using htendsto

/-- The square root of the squared reciprocal tail also vanishes. -/
theorem
    inverseSqrtThresholdUnboundedHittingAfterDelayedReciprocalWeight_sq_tsum_sqrt_tendsto_zero :
    Tendsto
      (fun base => Real.sqrt (∑' n : Nat,
        inverseSqrtThresholdUnboundedHittingAfterDelayedReciprocalWeight base n ^ 2))
      atTop (nhds 0) := by
  simpa using
    (Real.continuous_sqrt.tendsto 0).comp
      inverseSqrtThresholdUnboundedHittingAfterDelayedReciprocalWeight_sq_tsum_tendsto_zero

/-- Reciprocal-weighted final successor-batch coordinate at the uncapped
inverse-square-root hitting time. -/
noncomputable def
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterDelayedReciprocalSuccessorRegret
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (scheduleIndex : Nat) :
    HeterogeneousStochasticEpisodeBatchTrajectory mdp
        (fun t =>
          AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
            mdp varianceProxy baseVisitFloor t) -> Real :=
  let source := selfConsistentScheduledCausalSource mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor
  let base := explicitHighProbabilityRounds scheduleIndex
  let tau :=
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor scheduleIndex
  stoppedValue
    (fun hit trajectory =>
      inverseSqrtThresholdUnboundedHittingAfterDelayedReciprocalWeight base hit *
        source.naturalSuccessorBatchAverageRealizedRegret trajectory (hit - 1))
    tau

/-- Pathwise negative-part decomposition at a finite uncapped hit: the base
absolute average pays for an immediate hit, while the reciprocal-weighted
successor coordinate pays for a delayed hit. -/
theorem
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfter_stoppedNegativePart_le_baseAbsolute_add_delayedReciprocalSuccessorRegretAbsolute
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (scheduleIndex : Nat)
    (trajectory : HeterogeneousStochasticEpisodeBatchTrajectory mdp
      (fun t =>
        AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
          mdp varianceProxy baseVisitFloor t))
    (hfinite :
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor scheduleIndex trajectory ≠ ⊤) :
    let stoppedProcess :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
          (selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor)
          scheduleIndex
    max (-stoppedProcess trajectory) 0 <=
      |selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor (explicitHighProbabilityRounds scheduleIndex)
            trajectory| +
      |selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterDelayedReciprocalSuccessorRegret
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor scheduleIndex trajectory| := by
  dsimp only
  let source := selfConsistentScheduledCausalSource mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor
  let average :=
    selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor
  let increment := fun n trajectory =>
    source.naturalSuccessorBatchAverageRealizedRegret trajectory n
  let threshold :=
    selfConsistentScheduledNaturalCausalInverseSqrtFirstPassageThreshold
      scheduleIndex
  let base := explicitHighProbabilityRounds scheduleIndex
  have hrecursion (n : Nat) :
      average (n + 1) trajectory =
        ((n : Real) * average n trajectory + increment n trajectory) /
          ((n + 1 : Nat) : Real) := by
    simpa only [average, increment, source,
      selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess] using
      source.naturalAverageRealizedBehaviorRegret_succ_eq trajectory n
  have hgeneric :=
    max_neg_hittingAfter_untopA_le_base_abs_add_abs_stoppedValue_delayedReciprocalIncrement
      average increment threshold
        (selfConsistentScheduledNaturalCausalInverseSqrtFirstPassageThreshold_pos
          scheduleIndex)
        base trajectory hrecursion
        (by
          simpa only [average, threshold, base,
            selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix]
            using hfinite)
  simpa only [average, increment, threshold, base, source,
    selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess_apply,
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix,
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterDelayedReciprocalSuccessorRegret]
    using hgeneric

/-- The reciprocal-weighted final successor coordinate is integrable and its
absolute first moment is controlled by the square root of the reciprocal
square tail. -/
theorem
    selfConsistentScheduledCausalSource_inverseSqrtThresholdUnboundedHittingAfter_delayedReciprocalSuccessorRegret_integrable_and_integral_abs_le
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace State] [StandardBorelSpace Action]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (varianceProxy : NNReal) (hvarianceProxy : 0 < varianceProxy)
    (law : rewardSource.UniformSubgaussianRewardLaw varianceProxy)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State)
    (support : ExploratoryPathSupport mdp initialState)
    (baseVisitFloor : Real)
    (hbaseFloor : ExploratoryPathUniformVisitFloor support 1 baseVisitFloor)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (hhorizon : 0 < mdp.horizon) (hbaseVisitFloor : 0 < baseVisitFloor)
    (scheduleIndex : Nat) :
    let delayedRegret :=
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterDelayedReciprocalSuccessorRegret
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor scheduleIndex
    let mu := (selfConsistentScheduledCausalSource mdp initialState rewardSource
      initialTable defaultState varianceProxy baseVisitFloor).trajectoryMeasure
    Integrable delayedRegret mu /\
      integral mu (fun trajectory => |delayedRegret trajectory|) <=
        Real.sqrt
            (HeterogeneousAdaptiveStochasticEpisodeBatchSource.naturalSuccessorBatchAverageRealizedRegretSecondMomentEnvelope
              mdp varianceProxy) *
          Real.sqrt (∑' hit : Nat,
            inverseSqrtThresholdUnboundedHittingAfterDelayedReciprocalWeight
              (explicitHighProbabilityRounds scheduleIndex) hit ^ 2) := by
  dsimp only
  let episodes := fun t =>
    AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
      mdp varianceProxy baseVisitFloor t
  let source := selfConsistentScheduledCausalSource mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor
  let base := explicitHighProbabilityRounds scheduleIndex
  let tau :=
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor scheduleIndex
  let process := fun hit trajectory =>
    source.naturalSuccessorBatchAverageRealizedRegret trajectory (hit - 1)
  let weight :=
    inverseSqrtThresholdUnboundedHittingAfterDelayedReciprocalWeight base
  letI : source.GlobalReturnMeasurability := by
    dsimp [source, selfConsistentScheduledCausalSource]
    infer_instance
  have hsourceLaw : source.rewardSource.UniformSubgaussianRewardLaw
      varianceProxy := by
    simpa [source, selfConsistentScheduledCausalSource,
      HeterogeneousAdaptiveStochasticEpisodeBatchSource.rewardSource] using law
  have htau : Measurable tau := by
    simpa only [tau] using
      (selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix_isStoppingTime
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor scheduleIndex).measurable'
  have hfinite : ∀ᵐ trajectory ∂source.trajectoryMeasure,
      tau trajectory ≠ ⊤ := by
    simpa only [source, tau] using
      ae_ne_top_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor scheduleIndex
  have hweightSq : Summable (fun hit => weight hit ^ 2) := by
    simpa only [weight] using
      summable_inverseSqrtThresholdUnboundedHittingAfterDelayedReciprocalWeight_sq
        base
  have hprocessMeasurable (hit : Nat) : Measurable (process hit) := by
    simpa only [process] using
      source.measurable_naturalSuccessorBatchAverageRealizedRegret (hit - 1)
  have hstoppedMeasurable : Measurable
      (stoppedValue (fun hit trajectory => weight hit * process hit trajectory)
        tau) := by
    apply BanditRLProof.measurable_stoppedValue_of_measurable_coordinates
      tau htau
    intro hit
    exact measurable_const.mul (hprocessMeasurable hit)
  have hepisodes (t : Nat) : 0 < episodes t := by
    exact
      AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes_pos
        mdp varianceProxy baseVisitFloor t
  have hprocessMemLp (hit : Nat) : MemLp (process hit) 2
      source.trajectoryMeasure := by
    simpa only [process, episodes] using
      source.memLp_two_naturalSuccessorBatchAverageRealizedRegret
        varianceProxy hrewardBound hsourceLaw (hit - 1)
          (hepisodes ((hit - 1) + 1))
  have hprocessSecondMoment (hit : Nat) :
      integral source.trajectoryMeasure
          (fun trajectory => process hit trajectory ^ 2) <=
        HeterogeneousAdaptiveStochasticEpisodeBatchSource.naturalSuccessorBatchAverageRealizedRegretSecondMomentEnvelope
          mdp varianceProxy := by
    simpa only [process, episodes] using
      source.integral_sq_naturalSuccessorBatchAverageRealizedRegret_le_secondMomentEnvelope
        varianceProxy hrewardBound hsourceLaw (hit - 1)
          (hepisodes ((hit - 1) + 1))
  have htransport :=
    BanditRLProof.integrable_and_integral_abs_stoppedValue_weight_mul_le
      source.trajectoryMeasure tau htau hfinite process weight hweightSq
        hstoppedMeasurable
        (HeterogeneousAdaptiveStochasticEpisodeBatchSource.naturalSuccessorBatchAverageRealizedRegretSecondMomentEnvelope
          mdp varianceProxy)
        hprocessMemLp hprocessSecondMoment
  simpa only [source, base, tau, process, weight,
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterDelayedReciprocalSuccessorRegret,
    MeasureTheory.probReal_univ, Real.sqrt_one, mul_one] using htransport

/-- Expected absolute reciprocal-weighted final successor coordinate. -/
noncomputable def
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterDelayedReciprocalSuccessorRegretExpectedAbsolute
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (scheduleIndex : Nat) : Real :=
  let source := selfConsistentScheduledCausalSource mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor
  integral source.trajectoryMeasure (fun trajectory =>
    |selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterDelayedReciprocalSuccessorRegret
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor scheduleIndex trajectory|)

/-- The expected absolute reciprocal-weighted overshoot coordinate vanishes
as the scheduled base tends to infinity. -/
theorem
    selfConsistentScheduledCausalSource_inverseSqrtThresholdUnboundedHittingAfter_delayedReciprocalSuccessorRegretExpectedAbsolute_tendsto_zero
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace State] [StandardBorelSpace Action]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (varianceProxy : NNReal) (hvarianceProxy : 0 < varianceProxy)
    (law : rewardSource.UniformSubgaussianRewardLaw varianceProxy)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State)
    (support : ExploratoryPathSupport mdp initialState)
    (baseVisitFloor : Real)
    (hbaseFloor : ExploratoryPathUniformVisitFloor support 1 baseVisitFloor)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (hhorizon : 0 < mdp.horizon) (hbaseVisitFloor : 0 < baseVisitFloor) :
    Tendsto
      (selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterDelayedReciprocalSuccessorRegretExpectedAbsolute
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor)
      atTop (nhds 0) := by
  let envelope :=
    HeterogeneousAdaptiveStochasticEpisodeBatchSource.naturalSuccessorBatchAverageRealizedRegretSecondMomentEnvelope
      mdp varianceProxy
  let upper : Nat -> Real := fun scheduleIndex =>
    Real.sqrt envelope *
      Real.sqrt (∑' hit : Nat,
        inverseSqrtThresholdUnboundedHittingAfterDelayedReciprocalWeight
          (explicitHighProbabilityRounds scheduleIndex) hit ^ 2)
  have htail : Tendsto (fun scheduleIndex =>
      Real.sqrt (∑' hit : Nat,
        inverseSqrtThresholdUnboundedHittingAfterDelayedReciprocalWeight
          (explicitHighProbabilityRounds scheduleIndex) hit ^ 2))
      atTop (nhds 0) :=
    inverseSqrtThresholdUnboundedHittingAfterDelayedReciprocalWeight_sq_tsum_sqrt_tendsto_zero.comp
      explicitHighProbabilityRounds_tendsto_atTop
  have hupper : Tendsto upper atTop (nhds 0) := by
    simpa only [upper, mul_zero] using tendsto_const_nhds.mul htail
  apply squeeze_zero
  · intro scheduleIndex
    unfold
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterDelayedReciprocalSuccessorRegretExpectedAbsolute
    exact integral_nonneg fun _ => abs_nonneg _
  · intro scheduleIndex
    simpa only [upper, envelope,
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterDelayedReciprocalSuccessorRegretExpectedAbsolute] using
      (selfConsistentScheduledCausalSource_inverseSqrtThresholdUnboundedHittingAfter_delayedReciprocalSuccessorRegret_integrable_and_integral_abs_le
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor scheduleIndex).2
  · exact hupper

/-- Expected negative part of the exact stopped average realized behavior
regret. -/
noncomputable def
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageRealizedBehaviorRegretExpectedNegativePart
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (scheduleIndex : Nat) : Real :=
  let source := selfConsistentScheduledCausalSource mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor
  let stoppingPrefix :=
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor
  let stoppedProcess :=
    selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor stoppingPrefix scheduleIndex
  integral source.trajectoryMeasure
    (fun trajectory => max (-stoppedProcess trajectory) 0)

/-- The expected negative part vanishes: immediate hits are paid by the
summable base-prefix L1 term, and delayed hits by the reciprocal-weighted L2
overshoot term. -/
theorem
    selfConsistentScheduledCausalSource_inverseSqrtThresholdUnboundedHittingAfter_stoppedAverageRealizedBehaviorRegretExpectedNegativePart_tendsto_zero
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace State] [StandardBorelSpace Action]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (varianceProxy : NNReal) (hvarianceProxy : 0 < varianceProxy)
    (law : rewardSource.UniformSubgaussianRewardLaw varianceProxy)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State)
    (support : ExploratoryPathSupport mdp initialState)
    (baseVisitFloor : Real)
    (hbaseFloor : ExploratoryPathUniformVisitFloor support 1 baseVisitFloor)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (hhorizon : 4 < mdp.horizon) (hbaseVisitFloor : 0 < baseVisitFloor) :
    Tendsto
      (selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageRealizedBehaviorRegretExpectedNegativePart
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor)
      atTop (nhds 0) := by
  let source := selfConsistentScheduledCausalSource mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor
  let stoppingPrefix :=
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor
  let stoppedProcess := fun scheduleIndex =>
    selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor stoppingPrefix scheduleIndex
  let baseProcess := fun scheduleIndex =>
    selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor (explicitHighProbabilityRounds scheduleIndex)
  let delayedProcess := fun scheduleIndex =>
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterDelayedReciprocalSuccessorRegret
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor scheduleIndex
  let expectedBase :=
    explicitPolynomialPrefixExpectedAbsoluteAverageRealizedBehaviorRegret
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor
  let expectedDelayed :=
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterDelayedReciprocalSuccessorRegretExpectedAbsolute
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor
  let upper := fun scheduleIndex =>
    expectedBase scheduleIndex + expectedDelayed scheduleIndex
  have hhorizonPos : 0 < mdp.horizon := lt_trans (by norm_num) hhorizon
  have hbaseTendsto : Tendsto expectedBase atTop (nhds 0) := by
    exact
      (summable_explicitPolynomialPrefixExpectedAbsoluteAverageRealizedBehaviorRegret
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizonPos
            hbaseVisitFloor).tendsto_atTop_zero
  have hdelayedTendsto : Tendsto expectedDelayed atTop (nhds 0) := by
    simpa only [expectedDelayed] using
      selfConsistentScheduledCausalSource_inverseSqrtThresholdUnboundedHittingAfter_delayedReciprocalSuccessorRegretExpectedAbsolute_tendsto_zero
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizonPos
            hbaseVisitFloor
  have hupper : Tendsto upper atTop (nhds 0) := by
    simpa only [upper, zero_add] using hbaseTendsto.add hdelayedTendsto
  apply squeeze_zero
  · intro scheduleIndex
    unfold
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageRealizedBehaviorRegretExpectedNegativePart
    exact integral_nonneg fun _ => le_max_right _ _
  · intro scheduleIndex
    have hstopping :=
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix_isStoppingTime
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor scheduleIndex
    have hstop : BanditRLProof.OFUL.SquareIntegrableFiniteStoppingTime
        source.trajectoryMeasure (stoppingPrefix scheduleIndex) := by
      simpa only [source, stoppingPrefix] using
        selfConsistentScheduledCausalSource_inverseSqrtThresholdUnboundedHittingAfter_squareIntegrableFiniteStoppingTime
          mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
            defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
              hbaseVisitFloor scheduleIndex
    have hstoppedIntegrable : Integrable (stoppedProcess scheduleIndex)
        source.trajectoryMeasure := by
      simpa only [stoppedProcess, source, stoppingPrefix] using
        (selfConsistentScheduledCausalSource_inverseSqrtThresholdUnboundedHittingAfter_stoppedAverageRealizedBehaviorRegret_integrable_and_integral_le_threshold
          mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
            defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
              hbaseVisitFloor scheduleIndex).1
    have hstoppedMeasurable : Measurable (stoppedProcess scheduleIndex) := by
      simpa only [stoppedProcess] using
        measurable_selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor stoppingPrefix scheduleIndex hstopping
    have hnegativeIntegrable : Integrable
        (fun trajectory => max (-(stoppedProcess scheduleIndex trajectory)) 0)
        source.trajectoryMeasure := by
      refine hstoppedIntegrable.abs.mono'
        ((hstoppedMeasurable.neg.max measurable_const).aestronglyMeasurable) ?_
      filter_upwards with trajectory
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      exact max_le (neg_le_abs _) (abs_nonneg _)
    have hbaseIntegrable : Integrable
        (fun trajectory => |baseProcess scheduleIndex trajectory|)
        source.trajectoryMeasure := by
      exact
        ((memLp_two_selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
          mdp initialState rewardSource varianceProxy law initialTable defaultState
            baseVisitFloor hrewardBound
              (explicitHighProbabilityRounds scheduleIndex)).integrable
          (by norm_num)).abs
    have hdelayedIntegrable : Integrable (delayedProcess scheduleIndex)
        source.trajectoryMeasure := by
      simpa only [delayedProcess, source] using
        (selfConsistentScheduledCausalSource_inverseSqrtThresholdUnboundedHittingAfter_delayedReciprocalSuccessorRegret_integrable_and_integral_abs_le
          mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
            defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizonPos
              hbaseVisitFloor scheduleIndex).1
    have hrhsIntegrable : Integrable (fun trajectory =>
        |baseProcess scheduleIndex trajectory| +
          |delayedProcess scheduleIndex trajectory|) source.trajectoryMeasure :=
      hbaseIntegrable.add hdelayedIntegrable.abs
    have hpoint : ∀ᵐ trajectory ∂source.trajectoryMeasure,
        max (-(stoppedProcess scheduleIndex trajectory)) 0 <=
          |baseProcess scheduleIndex trajectory| +
            |delayedProcess scheduleIndex trajectory| := by
      filter_upwards [hstop.finite_ae] with trajectory hfinite
      simpa only [stoppedProcess, baseProcess, delayedProcess, source,
        stoppingPrefix] using
        selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfter_stoppedNegativePart_le_baseAbsolute_add_delayedReciprocalSuccessorRegretAbsolute
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor scheduleIndex trajectory hfinite
    calc
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageRealizedBehaviorRegretExpectedNegativePart
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor scheduleIndex =
          integral source.trajectoryMeasure (fun trajectory =>
            max (-(stoppedProcess scheduleIndex trajectory)) 0) := by
        rfl
      _ <= integral source.trajectoryMeasure (fun trajectory =>
          |baseProcess scheduleIndex trajectory| +
            |delayedProcess scheduleIndex trajectory|) :=
        integral_mono_ae hnegativeIntegrable hrhsIntegrable hpoint
      _ = integral source.trajectoryMeasure (fun trajectory =>
            |baseProcess scheduleIndex trajectory|) +
          integral source.trajectoryMeasure (fun trajectory =>
            |delayedProcess scheduleIndex trajectory|) :=
        integral_add hbaseIntegrable hdelayedIntegrable.abs
      _ = upper scheduleIndex := by
        rfl
  · exact hupper

/-- The exact stopped average realized behavior regret at the uncapped
inverse-square-root `hittingAfter` converges to zero in expected absolute
value. -/
theorem
    selfConsistentScheduledCausalSource_inverseSqrtThresholdUnboundedHittingAfter_stoppedAverageRealizedBehaviorRegretExpectedAbsolute_tendsto_zero
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace State] [StandardBorelSpace Action]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (varianceProxy : NNReal) (hvarianceProxy : 0 < varianceProxy)
    (law : rewardSource.UniformSubgaussianRewardLaw varianceProxy)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State)
    (support : ExploratoryPathSupport mdp initialState)
    (baseVisitFloor : Real)
    (hbaseFloor : ExploratoryPathUniformVisitFloor support 1 baseVisitFloor)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (hhorizon : 4 < mdp.horizon) (hbaseVisitFloor : 0 < baseVisitFloor) :
    Tendsto
      (selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageRealizedBehaviorRegretExpectedAbsolute
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor)
      atTop (nhds 0) := by
  let expectedPositive :=
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageRealizedBehaviorRegretExpectedPositivePart
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor
  let expectedNegative :=
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageRealizedBehaviorRegretExpectedNegativePart
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor
  have hpositive : Tendsto expectedPositive atTop (nhds 0) := by
    simpa only [expectedPositive] using
      selfConsistentScheduledCausalSource_inverseSqrtThresholdUnboundedHittingAfter_stoppedAverageRealizedBehaviorRegretExpectedPositivePart_tendsto_zero
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor
  have hnegative : Tendsto expectedNegative atTop (nhds 0) := by
    simpa only [expectedNegative] using
      selfConsistentScheduledCausalSource_inverseSqrtThresholdUnboundedHittingAfter_stoppedAverageRealizedBehaviorRegretExpectedNegativePart_tendsto_zero
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor
  have hsum : Tendsto (fun scheduleIndex =>
      expectedPositive scheduleIndex + expectedNegative scheduleIndex)
      atTop (nhds 0) := by
    simpa only [zero_add] using hpositive.add hnegative
  apply hsum.congr'
  filter_upwards with scheduleIndex
  let source := selfConsistentScheduledCausalSource mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor
  let stoppingPrefix :=
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor
  let stoppedProcess :=
    selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor stoppingPrefix scheduleIndex
  have hstoppedIntegrable : Integrable stoppedProcess source.trajectoryMeasure := by
    simpa only [stoppedProcess, source, stoppingPrefix] using
      (selfConsistentScheduledCausalSource_inverseSqrtThresholdUnboundedHittingAfter_stoppedAverageRealizedBehaviorRegret_integrable_and_integral_le_threshold
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor scheduleIndex).1
  have hstopping :=
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix_isStoppingTime
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor scheduleIndex
  have hstoppedMeasurable : Measurable stoppedProcess := by
    simpa only [stoppedProcess] using
      measurable_selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix scheduleIndex hstopping
  have hpositiveIntegrable : Integrable
      (fun trajectory => max (stoppedProcess trajectory) 0)
      source.trajectoryMeasure := by
    refine hstoppedIntegrable.abs.mono'
      ((hstoppedMeasurable.max measurable_const).aestronglyMeasurable) ?_
    filter_upwards with trajectory
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le (le_abs_self _) (abs_nonneg _)
  have hnegativeIntegrable : Integrable
      (fun trajectory => max (-stoppedProcess trajectory) 0)
      source.trajectoryMeasure := by
    refine hstoppedIntegrable.abs.mono'
      ((hstoppedMeasurable.neg.max measurable_const).aestronglyMeasurable) ?_
    filter_upwards with trajectory
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le (neg_le_abs _) (abs_nonneg _)
  change
    integral source.trajectoryMeasure (fun trajectory =>
          max (stoppedProcess trajectory) 0) +
        integral source.trajectoryMeasure (fun trajectory =>
          max (-stoppedProcess trajectory) 0) =
      integral source.trajectoryMeasure (fun trajectory =>
        |stoppedProcess trajectory|)
  rw [← integral_add hpositiveIntegrable hnegativeIntegrable]
  apply integral_congr_ae
  filter_upwards with trajectory
  by_cases htrajectory : 0 <= stoppedProcess trajectory
  · rw [abs_of_nonneg htrajectory, max_eq_left htrajectory,
      max_eq_right (neg_nonpos.mpr htrajectory), add_zero]
  · have htrajectoryNonpos : stoppedProcess trajectory <= 0 :=
      le_of_not_ge htrajectory
    rw [abs_of_nonpos htrajectoryNonpos, max_eq_right htrajectoryNonpos,
      max_eq_left (neg_nonneg.mpr htrajectoryNonpos), zero_add]

end AdaptiveStochasticSampledEmpiricalOptimisticSource

end BanditRLProof.FiniteHorizonRL
