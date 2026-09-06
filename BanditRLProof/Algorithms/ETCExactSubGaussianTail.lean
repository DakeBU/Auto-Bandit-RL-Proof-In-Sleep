import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import BanditRLProof.Algorithms.ETCExpectedPullCount
import BanditRLProof.Algorithms.ETCFiniteArmRewardLaw

/-!
# Exact common-sub-Gaussian ETC tail constant

This module normalizes the canonical common-proxy ETC pairwise tail to the
closed exponential used by the exact LML theorem route.  It remains over the
project's existing `Rat` reward-law model, with all random variables embedded
in `Real`; transport to native `Real` reward kernels is downstream work.
-/

namespace BanditRLProof
namespace ETC

/--
Over the round-robin exploration horizon, the constant common-proxy pairwise
process charges exactly `m` pulls of the candidate arm and `m` pulls of the
selected best arm.
-/
theorem sum_centeredPairwiseRewardDiffVarianceProxy_const_eq_two_mul
    {K : Nat}
    (spec : ETC.Spec K) (model : FiniteBanditModel K)
    (sigma2 : NNReal) (a : Fin K)
    (hne : a = model.bestArm -> False) :
    (Finset.range (spec.explorationPulls * K)).sum
        (fun t =>
          ETC.centeredPairwiseRewardDiffVarianceProxy
            spec model model.bestArm (fun _ _ => sigma2) a t) =
      (2 : NNReal) * (spec.explorationPulls : NNReal) * sigma2 := by
  classical
  let action : ActionTrace (Fin K) :=
    ETC.actionWithCommit spec model.bestArm
  have hane : a ≠ model.bestArm := by
    intro h
    exact hne h
  have hpoint : forall t : Nat,
      ETC.centeredPairwiseRewardDiffVarianceProxy
          spec model model.bestArm (fun _ _ => sigma2) a t =
        (if action t = a then sigma2 else 0) +
          (if action t = model.bestArm then sigma2 else 0) := by
    intro t
    by_cases ha : action t = a
    · simp [ETC.centeredPairwiseRewardDiffVarianceProxy, action, ha, hane]
    · by_cases hbest : action t = model.bestArm
      · have hbest_ne_a : model.bestArm ≠ a := Ne.symm hane
        simp [ETC.centeredPairwiseRewardDiffVarianceProxy, action, hbest,
          hbest_ne_a]
      · simp [ETC.centeredPairwiseRewardDiffVarianceProxy, action, ha, hbest]
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
            have hcount :=
              pullCount_eq_finset_filter_card
                (action := action) (a := b)
                (t := spec.explorationPulls * K)
            rw [← hcount]
            rw [show action = ETC.actionWithCommit spec model.bestArm by rfl]
            rw [ETC.pullCount_actionWithCommit_explorationPulls_mul_K_eq]
  rw [Finset.sum_congr rfl (fun t _ht => hpoint t)]
  rw [Finset.sum_add_distrib, hselected a, hselected model.bestArm]
  ring

/-- The deterministic centered pairwise threshold is `m` times the model gap. -/
theorem centeredPairwiseGapThreshold_eq_explorationPulls_mul_gap
    {K : Nat}
    (spec : ETC.Spec K) (model : FiniteBanditModel K) (a : Fin K)
    (hne : a = model.bestArm -> False) :
    ETC.centeredPairwiseGapThreshold spec model a =
      (spec.explorationPulls : Real) * ((model.gap a : Rat) : Real) := by
  have hane : a ≠ model.bestArm := by
    intro h
    exact hne h
  rw [ETC.centeredPairwiseGapThreshold, FiniteBanditModel.gap]
  simp [hane, Rat.cast_mul, Rat.cast_sub]

/--
The canonical direct-MGF pairwise tail equals the exact LML exponential
`exp (-m * gap^2 / (4 * sigma2))` for every non-best arm.

Only `m > 0` is needed to cancel the exploration multiplicity.  The
`sigma2 = 0` boundary is handled separately and remains a valid equality in
Lean's total division.
-/
theorem canonicalSubGaussianArmPairwiseTailReal_eq_exp_neg_explorationPulls_mul_gap_sq_div_four_mul
    {K : Nat}
    (spec : ETC.Spec K) (model : FiniteBanditModel K)
    (sigma2 : NNReal) (a : Fin K)
    (hexplorationPulls_pos : 0 < spec.explorationPulls)
    (hne : a = model.bestArm -> False) :
    ETC.canonicalSubGaussianArmPairwiseTailReal spec model sigma2 a =
      Real.exp
        (-(spec.explorationPulls : Real) *
          ((model.gap a : Rat) : Real) ^ 2 /
            (4 * (sigma2 : Real))) := by
  let pairwiseProxy :=
    ETC.centeredPairwiseRewardDiffVarianceProxy
      spec model model.bestArm (fun _ _ => sigma2)
  have hproxyNNReal :
      (Finset.range (spec.explorationPulls * K)).sum (pairwiseProxy a) =
        (2 : NNReal) * (spec.explorationPulls : NNReal) * sigma2 := by
    exact
      ETC.sum_centeredPairwiseRewardDiffVarianceProxy_const_eq_two_mul
        spec model sigma2 a hne
  have hproxyReal :
      (((Finset.range (spec.explorationPulls * K)).sum (pairwiseProxy a) : NNReal) :
          Real) =
        2 * (spec.explorationPulls : Real) * (sigma2 : Real) := by
    rw [hproxyNNReal]
    norm_num
  have hthreshold :=
    ETC.centeredPairwiseGapThreshold_eq_explorationPulls_mul_gap
      spec model a hne
  rw [ETC.canonicalSubGaussianArmPairwiseTailReal]
  rw [ETC.centeredDiffSubGaussianTail]
  rw [ENNReal.toReal_ofReal (le_of_lt (Real.exp_pos _))]
  rw [show
    ETC.centeredPairwiseRewardDiffVarianceProxy
        spec model model.bestArm (fun _ _ => sigma2) = pairwiseProxy by rfl]
  rw [hthreshold, hproxyReal]
  congr 1
  have hm_ne : (spec.explorationPulls : Real) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hexplorationPulls_pos)
  by_cases hsigma : (sigma2 : Real) = 0
  · simp [hsigma]
  · field_simp [hm_ne, hsigma]
    ring

/--
Exact-LML-constant form of the canonical single-arm commit-fiber probability
bound under the existing common-sub-Gaussian `Rat` arm laws.

This is a genuine concentration producer, but not yet the native `Real`
reward-kernel theorem: the arm laws are measures on `Rat`, their centered casts
have a common `NNReal` proxy, and the generated trajectory is the local
canonical history process.
-/
theorem real_measure_explorationArgmaxCommit_eq_arm_le_exp_neg_explorationPulls_mul_gap_sq_div_four_mul_of_armLaws
    {K : Nat} {Context : Type}
    [MeasurableSpace Context]
    (spec : ETC.Spec K) (model : FiniteBanditModel K)
    (armLaw : Fin K -> MeasureTheory.Measure Rat)
    (hprob : forall arm, MeasureTheory.IsProbabilityMeasure (armLaw arm))
    (sigma2 : NNReal)
    (hmean : forall arm, MeasureTheory.integral (armLaw arm)
      (fun reward : Rat => (((reward : Rat) : Real))) =
        (((model.mean arm : Rat) : Real)))
    (hsubG : forall arm, ProbabilityTheory.HasSubgaussianMGF
      (fun reward : Rat =>
        ((reward : Rat) : Real) - (((model.mean arm : Rat) : Real)))
      sigma2 (armLaw arm))
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (hcontext : forall n : Nat, Measurable (context n))
    (hexplorationPulls_pos : 0 < spec.explorationPulls)
    (a : Fin K)
    (hne : a = model.bestArm -> False) :
    let defaultAction := ETC.exploreArm spec 0
    let rewardKernel := RewardKernel.contextIndependentOfActionLaws
      (Context := Context) armLaw hprob
    let policy := fun t => ETC.explorationArgmaxHistoryPolicy spec model t
    let state := fun t history => ETC.explorationArgmaxHistoryState t history
    let stepKernel :=
      RewardKernel.historyStepKernelFamily rewardKernel policy context state
        hcontext (fun t => ETC.measurable_explorationArgmaxHistoryState t)
    let trajMeasure := ProbabilityTheory.Kernel.trajMeasure
      (X := fun _ : Nat => Rat) (armLaw defaultAction) stepKernel
    trajMeasure.real
        {trajectory : RewardTrace Rat |
          ETC.explorationArgmaxCommit spec model trajectory = a} <=
      Real.exp
        (-(spec.explorationPulls : Real) *
          ((model.gap a : Rat) : Real) ^ 2 /
            (4 * (sigma2 : Real))) := by
  rw [←
    ETC.canonicalSubGaussianArmPairwiseTailReal_eq_exp_neg_explorationPulls_mul_gap_sq_div_four_mul
      spec model sigma2 a hexplorationPulls_pos hne]
  exact
    ETC.real_measure_explorationArgmaxCommit_eq_arm_le_canonicalSubGaussianArmPairwiseTailReal
      spec model armLaw hprob sigma2 hmean hsubG context hcontext
      hexplorationPulls_pos a hne

/--
Canonical generated-history per-arm expected pull-count bound with the exact
LML exponential constant, under the existing common-sub-Gaussian `Rat` arm
laws.

This theorem composes the concrete commit-fiber concentration producer with
the generic Real/Bochner `actionWithCommit` expected-count consumer.  It is the
first local theorem with the full `m + (n - K*m) * exp (...)` per-arm shape.
Native `Real` reward-kernel transport and external algorithm/environment-law
alignment remain downstream.
-/
theorem integral_real_pullCount_explorationArgmaxAction_le_exploration_add_remaining_mul_exp_of_armLaws
    {K : Nat} {Context : Type}
    [MeasurableSpace Context]
    (spec : ETC.Spec K) (model : FiniteBanditModel K)
    (armLaw : Fin K -> MeasureTheory.Measure Rat)
    (hprob : forall arm, MeasureTheory.IsProbabilityMeasure (armLaw arm))
    (sigma2 : NNReal)
    (hmean : forall arm, MeasureTheory.integral (armLaw arm)
      (fun reward : Rat => (((reward : Rat) : Real))) =
        (((model.mean arm : Rat) : Real)))
    (hsubG : forall arm, ProbabilityTheory.HasSubgaussianMGF
      (fun reward : Rat =>
        ((reward : Rat) : Real) - (((model.mean arm : Rat) : Real)))
      sigma2 (armLaw arm))
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (hcontext : forall n : Nat, Measurable (context n))
    (hexplorationPulls_pos : 0 < spec.explorationPulls)
    (a : Fin K) (n : Nat)
    (hn : K * spec.explorationPulls <= n)
    (hne : a = model.bestArm -> False) :
    let defaultAction := ETC.exploreArm spec 0
    let rewardKernel := RewardKernel.contextIndependentOfActionLaws
      (Context := Context) armLaw hprob
    let policy := fun t => ETC.explorationArgmaxHistoryPolicy spec model t
    let state := fun t history => ETC.explorationArgmaxHistoryState t history
    let stepKernel :=
      RewardKernel.historyStepKernelFamily rewardKernel policy context state
        hcontext (fun t => ETC.measurable_explorationArgmaxHistoryState t)
    let trajMeasure := ProbabilityTheory.Kernel.trajMeasure
      (X := fun _ : Nat => Rat) (armLaw defaultAction) stepKernel
    MeasureTheory.integral trajMeasure
        (fun trajectory : RewardTrace Rat =>
          ((pullCount
            (ETC.explorationArgmaxAction spec model trajectory) a n : Nat) :
              Real)) <=
      (spec.explorationPulls : Real) +
        ((n - K * spec.explorationPulls : Nat) : Real) *
          Real.exp
            (-(spec.explorationPulls : Real) *
              ((model.gap a : Rat) : Real) ^ 2 /
                (4 * (sigma2 : Real))) := by
  let defaultAction := ETC.exploreArm spec 0
  let rewardKernel := RewardKernel.contextIndependentOfActionLaws
    (Context := Context) armLaw hprob
  let policy := fun t => ETC.explorationArgmaxHistoryPolicy spec model t
  let state := fun t history => ETC.explorationArgmaxHistoryState t history
  let stepKernel :=
    RewardKernel.historyStepKernelFamily rewardKernel policy context state
      hcontext (fun t => ETC.measurable_explorationArgmaxHistoryState t)
  letI : MeasureTheory.IsProbabilityMeasure (armLaw defaultAction) :=
    hprob defaultAction
  let trajMeasure := ProbabilityTheory.Kernel.trajMeasure
    (X := fun _ : Nat => Rat) (armLaw defaultAction) stepKernel
  let commit : RewardTrace Rat -> Fin K :=
    fun trajectory => ETC.explorationArgmaxCommit spec model trajectory
  have hmeas_coord : forall b : Fin K,
      Measurable (fun trajectory : RewardTrace Rat =>
        ETC.empMeanAtExploration spec model.bestArm trajectory b) := by
    exact ETC.measurable_empMeanAtExploration_coordinates
      (spec := spec)
      (commitArm := model.bestArm)
      (reward := fun trajectory : RewardTrace Rat => trajectory)
      (hreward := fun t => measurable_pi_apply t)
  have hmeas_commit : Measurable commit := by
    simpa [commit, ETC.explorationArgmaxCommit,
      ETC.fixedProductArgmaxCommit] using
      (ETC.measurable_commitOracle_choose_of_forall_measurable_empMean
        (oracle := ETC.argmaxCommitOracle model.hK)
        (empMean := fun trajectory : RewardTrace Rat => fun b : Fin K =>
          ETC.empMeanAtExploration spec model.bestArm trajectory b)
        hmeas_coord)
  have hprob_arm :
      trajMeasure.real
          {trajectory : RewardTrace Rat | commit trajectory = a} <=
        Real.exp
          (-(spec.explorationPulls : Real) *
            ((model.gap a : Rat) : Real) ^ 2 /
              (4 * (sigma2 : Real))) := by
    simpa [commit] using
      (ETC.real_measure_explorationArgmaxCommit_eq_arm_le_exp_neg_explorationPulls_mul_gap_sq_div_four_mul_of_armLaws
        spec model armLaw hprob sigma2 hmean hsubG context hcontext
        hexplorationPulls_pos a hne)
  have hcount :=
    ETC.integral_real_pullCount_actionWithCommit_choice_le_exploration_add_remaining_mul_of_commit_prob_le
      trajMeasure spec commit a n
      (Real.exp
        (-(spec.explorationPulls : Real) *
          ((model.gap a : Rat) : Real) ^ 2 /
            (4 * (sigma2 : Real))))
      hn hmeas_commit hprob_arm
  simpa [commit, ETC.explorationArgmaxAction,
    ETC.fixedProductArgmaxAction] using hcount

end ETC
end BanditRLProof
