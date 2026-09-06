import BanditRLProof.Algorithms.UCBArmStreamSource
import Mathlib.Probability.ProductMeasure

/-!
# Recursive UCB process on a latent arm-stream space

This module mirrors the deterministic part of the pinned LML array model. It
recursively builds the inclusive action/reward history, uses round-robin
initialization followed by the native Real history-index selector, and reads
the selected arm's next unused latent reward coordinate.
-/

namespace BanditRLProof

open MeasureTheory ProbabilityTheory

namespace UCB

/-- Round-robin arm at an absolute time coordinate. -/
def initializationArm {K : Nat} (hK : 0 < K) (t : Nat) : Fin K :=
  ⟨t % K, Nat.mod_lt t hK⟩

@[simp]
theorem initializationArm_zero {K : Nat} (hK : 0 < K) :
    initializationArm hK 0 = Fin.mk 0 hK := by
  rfl

/--
LML-shaped next action after an inclusive history through time `n`.

The first `K` actions are round robin. Once that prefix is complete, the
native Real UCB history index selects a least-encoded maximizing arm.
-/
noncomputable def realHistoryNextArm
    {K : Nat} (hK : 0 < K) (c : Real) (n : Nat)
    (history : History.FinitePairHistory (Fin K) Real n) : Fin K :=
  if n < K - 1 then
    initializationArm hK (n + 1)
  else
    realHistoryIndexAction hK c n history

/-- The next-arm selector is measurable on the finite history space. -/
theorem measurable_realHistoryNextArm
    {K : Nat} (hK : 0 < K) (c : Real) (n : Nat) :
    Measurable (fun history : History.FinitePairHistory (Fin K) Real n =>
      realHistoryNextArm hK c n history) := by
  by_cases hn : n < K - 1
  · simp [realHistoryNextArm, hn]
  · simpa [realHistoryNextArm, hn] using
      (measurable_realHistoryIndexAction hK c n)

/-- Joint evaluation of an arm stream at countable random coordinates. -/
theorem measurable_armRewardStream_apply {K : Nat} :
    Measurable
      (fun input : ArmRewardStream K × (Nat × Fin K) =>
        input.1 input.2.1 input.2.2) := by
  apply measurable_from_prod_countable_left
  intro index
  exact (measurable_pi_apply index.2).comp
    (measurable_pi_apply index.1)

/--
Inclusive pair history of the deterministic UCB process driven by a latent
arm-reward stream.
-/
noncomputable def armStreamHistory
    {K : Nat} (hK : 0 < K) (c : Real)
    (stream : ArmRewardStream K) :
    (n : Nat) -> History.FinitePairHistory (Fin K) Real n
  | 0 =>
      let arm := initializationArm hK 0
      fun _ => (arm, stream 0 arm)
  | n + 1 =>
      let history := armStreamHistory hK c stream n
      let arm := realHistoryNextArm hK c n history
      let count := ETC.realHistoryPullCount n history arm
      History.extendPairHistorySucc history (arm, stream count arm)

/-- Action trace extracted from the recursive inclusive histories. -/
noncomputable def armStreamAction
    {K : Nat} (hK : 0 < K) (c : Real) :
    ArmRewardStream K -> ActionTrace (Fin K) :=
  fun stream t =>
    (armStreamHistory hK c stream t
      ⟨t, Finset.mem_Iic.mpr le_rfl⟩).1

/-- Reward trace obtained by reading each selected arm's next unused value. -/
noncomputable def armStreamReward
    {K : Nat} (hK : 0 < K) (c : Real) :
    ArmRewardStream K -> RewardTrace Real :=
  rewardFromArmStream (armStreamAction hK c) id

@[simp]
theorem armStreamAction_zero
    {K : Nat} (hK : 0 < K) (c : Real) (stream : ArmRewardStream K) :
    armStreamAction hK c stream 0 = initializationArm hK 0 := by
  rfl

@[simp]
theorem armStreamAction_succ
    {K : Nat} (hK : 0 < K) (c : Real)
    (stream : ArmRewardStream K) (n : Nat) :
    armStreamAction hK c stream (n + 1) =
      realHistoryNextArm hK c n (armStreamHistory hK c stream n) := by
  simp [armStreamAction, armStreamHistory]

/--
The recursively maintained history is exactly the finite pair history of the
extracted action and next-unused-coordinate reward traces.
-/
theorem armStreamHistory_eq_finitePairHistoryOfTrace
    {K : Nat} (hK : 0 < K) (c : Real)
    (stream : ArmRewardStream K) (n : Nat) :
    armStreamHistory hK c stream n =
      History.finitePairHistoryOfTrace
        (armStreamAction hK c stream)
        (armStreamReward hK c stream) n := by
  induction n with
  | zero =>
      funext i
      have hi : i.1 = 0 := Nat.eq_zero_of_le_zero (Finset.mem_Iic.mp i.2)
      have hi_subtype : i = ⟨0, Finset.mem_Iic.mpr le_rfl⟩ := Subtype.ext hi
      subst i
      simp [armStreamHistory, armStreamAction, armStreamReward,
        rewardFromArmStream]
  | succ n ih =>
      rw [armStreamHistory]
      rw [History.finitePairHistoryOfTrace_succ]
      rw [← ih]
      apply congrArg (History.extendPairHistorySucc (t := n)
        (armStreamHistory hK c stream n))
      apply Prod.ext
      · simp [armStreamAction_succ]
      · simp only [armStreamReward, rewardFromArmStream]
        rw [armStreamAction_succ]
        rw [ih]
        rw [ETC.realHistoryPullCount_finitePairHistoryOfTrace]
        rfl

/-- Every recursively generated inclusive history is measurable in the stream. -/
theorem measurable_armStreamHistory
    {K : Nat} (hK : 0 < K) (c : Real) (n : Nat) :
    Measurable (fun stream : ArmRewardStream K =>
      armStreamHistory hK c stream n) := by
  induction n with
  | zero =>
      have hcoord : Measurable (fun stream : ArmRewardStream K =>
          stream 0 (initializationArm hK 0)) :=
        (measurable_pi_apply (initializationArm hK 0)).comp
          (measurable_pi_apply 0)
      refine measurable_pi_lambda _ ?_
      intro _i
      show Measurable (fun stream : ArmRewardStream K =>
        (initializationArm hK 0, stream 0 (initializationArm hK 0)))
      exact measurable_const.prodMk hcoord
  | succ n ih =>
      have harm : Measurable (fun stream : ArmRewardStream K =>
          realHistoryNextArm hK c n (armStreamHistory hK c stream n)) :=
        (measurable_realHistoryNextArm hK c n).comp ih
      have hcountEval : Measurable
          (fun input :
              History.FinitePairHistory (Fin K) Real n × Fin K =>
            ETC.realHistoryPullCount n input.1 input.2) := by
        apply measurable_from_prod_countable_left
        intro arm
        exact measurable_realHistoryPullCount n arm
      have hhistoryArm : Measurable (fun stream : ArmRewardStream K =>
          (armStreamHistory hK c stream n,
            realHistoryNextArm hK c n
              (armStreamHistory hK c stream n))) :=
        ih.prodMk harm
      have hcount : Measurable (fun stream : ArmRewardStream K =>
          ETC.realHistoryPullCount n (armStreamHistory hK c stream n)
            (realHistoryNextArm hK c n
              (armStreamHistory hK c stream n))) :=
        by simpa only [Function.comp_apply] using
          hcountEval.comp hhistoryArm
      have hcountArm : Measurable (fun stream : ArmRewardStream K =>
          (ETC.realHistoryPullCount n (armStreamHistory hK c stream n)
              (realHistoryNextArm hK c n
                (armStreamHistory hK c stream n)),
            realHistoryNextArm hK c n
              (armStreamHistory hK c stream n))) :=
        hcount.prodMk harm
      have hstreamCountArm : Measurable (fun stream : ArmRewardStream K =>
          (stream,
            (ETC.realHistoryPullCount n (armStreamHistory hK c stream n)
                (realHistoryNextArm hK c n
                  (armStreamHistory hK c stream n)),
              realHistoryNextArm hK c n
                (armStreamHistory hK c stream n)))) :=
        measurable_id.prodMk hcountArm
      have hreward : Measurable (fun stream : ArmRewardStream K =>
          stream
            (ETC.realHistoryPullCount n (armStreamHistory hK c stream n)
              (realHistoryNextArm hK c n
                (armStreamHistory hK c stream n)))
            (realHistoryNextArm hK c n
              (armStreamHistory hK c stream n))) :=
        by simpa only [Function.comp_apply] using
          measurable_armRewardStream_apply.comp hstreamCountArm
      have hnext : Measurable (fun stream : ArmRewardStream K =>
          (realHistoryNextArm hK c n
              (armStreamHistory hK c stream n),
            stream
              (ETC.realHistoryPullCount n (armStreamHistory hK c stream n)
                (realHistoryNextArm hK c n
                  (armStreamHistory hK c stream n)))
              (realHistoryNextArm hK c n
                (armStreamHistory hK c stream n)))) :=
        harm.prodMk hreward
      simpa only [armStreamHistory] using
        History.measurable_extendPairHistorySucc.comp
          (ih.prodMk hnext)

/-- Every action coordinate of the recursive arm-stream process is measurable. -/
theorem measurable_armStreamAction
    {K : Nat} (hK : 0 < K) (c : Real) (t : Nat) :
    Measurable (fun stream : ArmRewardStream K =>
      armStreamAction hK c stream t) := by
  exact (measurable_fst.comp
    (measurable_pi_apply
      (⟨t, Finset.mem_Iic.mpr le_rfl⟩ : Finset.Iic t))).comp
        (measurable_armStreamHistory hK c t)

/-- Every reward coordinate of the recursive arm-stream process is measurable. -/
theorem measurable_armStreamReward
    {K : Nat} (hK : 0 < K) (c : Real) (t : Nat) :
    Measurable (fun stream : ArmRewardStream K =>
      armStreamReward hK c stream t) := by
  have heq :
      (fun stream : ArmRewardStream K => armStreamReward hK c stream t) =
        (fun stream : ArmRewardStream K =>
          (armStreamHistory hK c stream t
            ⟨t, Finset.mem_Iic.mpr le_rfl⟩).2) := by
    funext stream
    rw [armStreamHistory_eq_finitePairHistoryOfTrace]
    rfl
  rw [heq]
  exact (measurable_snd.comp
    (measurable_pi_apply
      (⟨t, Finset.mem_Iic.mpr le_rfl⟩ : Finset.Iic t))).comp
        (measurable_armStreamHistory hK c t)

/-- The action after time `n` is the LML-shaped selector on its actual history. -/
theorem armStreamAction_succ_eq_realHistoryNextArm_actualHistory
    {K : Nat} (hK : 0 < K) (c : Real)
    (stream : ArmRewardStream K) (n : Nat) :
    armStreamAction hK c stream (n + 1) =
      realHistoryNextArm hK c n
        (History.finitePairHistoryOfTrace
          (armStreamAction hK c stream)
          (armStreamReward hK c stream) n) := by
  rw [armStreamAction_succ, armStreamHistory_eq_finitePairHistoryOfTrace]

/-- After initialization, the generated action is the native Real UCB index action. -/
theorem armStreamAction_succ_eq_realHistoryIndexAction_of_not_lt
    {K : Nat} (hK : 0 < K) (c : Real)
    (stream : ArmRewardStream K) (n : Nat) (hn : ¬ n < K - 1) :
    armStreamAction hK c stream (n + 1) =
      realHistoryIndexAction hK c n
        (History.finitePairHistoryOfTrace
          (armStreamAction hK c stream)
          (armStreamReward hK c stream) n) := by
  rw [armStreamAction_succ_eq_realHistoryNextArm_actualHistory]
  simp [realHistoryNextArm, hn]

/-- The recursive process satisfies the fixed-arm latent-prefix source. -/
noncomputable def armStreamUCBFixedArmPrefixSource
    {K : Nat} (hK : 0 < K) (c : Real) :
    FixedArmPrefixSource (armStreamAction hK c) (armStreamReward hK c) := by
  simpa [armStreamReward] using
    (canonicalFixedArmPrefixSource (armStreamAction hK c))

/-- Stationary product law: one independent time stream for every arm law. -/
noncomputable def armStreamMeasure
    {K : Nat} (nu : Kernel (Fin K) Real) [IsMarkovKernel nu] :
    Measure (ArmRewardStream K) :=
  Measure.infinitePi fun _ : Nat => Measure.infinitePi fun arm : Fin K => nu arm

instance instIsProbabilityMeasureArmStreamMeasure
    {K : Nat} (nu : Kernel (Fin K) Real) [IsMarkovKernel nu] :
    IsProbabilityMeasure (armStreamMeasure nu) := by
  unfold armStreamMeasure
  infer_instance

/--
Fixed-count peeling for the actual recursive UCB process under the stationary
product arm-stream law.
-/
theorem measure_pullCount_prod_sumRewards_armStreamUCB_mem_le
    {K : Nat} (hK : 0 < K) (c : Real)
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu]
    (arm : Fin K) (n : Nat) (s : Set (Nat × Real))
    [DecidablePred (fun k : Nat => k ∈ Prod.fst '' s)] :
    armStreamMeasure nu {stream |
        (pullCount (armStreamAction hK c stream) arm n,
          sumRewards (armStreamAction hK c stream)
            (armStreamReward hK c stream) arm n) ∈ s} ≤
      ((Finset.range (n + 1)).filter
        (fun k => k ∈ Prod.fst '' s)).sum (fun k =>
          armStreamMeasure nu {stream |
            armPrefixSum arm k stream ∈ Prod.mk k ⁻¹' s}) := by
  simpa [armStreamReward] using
    (measure_pullCount_prod_sumRewards_rewardFromCanonicalArmStream_mem_le
      (armStreamMeasure nu) (armStreamAction hK c) arm n s)

end UCB
end BanditRLProof
