import BanditRLProof.Algorithms.UCBArmStreamExpectedPullCount

/-!
# Native Real UCB LML field compatibility surface

The pinned LML source currently uses a newer Lean/mathlib toolchain, so ABRL
cannot import its `IsAlgEnvSeq` declaration directly. This module packages the
exact measurable action/feedback and split conditional-law consequences used
by the local UCB trajectory and regret route. It is a local compatibility
structure, not an imported LML proof.
-/

namespace BanditRLProof
namespace UCB

open MeasureTheory ProbabilityTheory

/--
The exact `IsAlgEnvSeq`-shaped fields consumed by the local stationary Real UCB
route.

The law fields correspond to the pinned source's initial action law, initial
feedback law, successor action law given finite observable history, and
successor feedback law given history and the new action. They are stated as
Mathlib `condDistrib` equalities because LML's `HasCondDistrib` symbol is not a
local dependency.
-/
structure RealStationaryUCBSequence
    {Omega : Type u} {K : Nat} [NeZero K] [MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (hK : 0 < K) (c : Real) (sigma2 : NNReal)
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu]
    (action : Omega -> ActionTrace (Fin K))
    (reward : Omega -> RewardTrace Real) : Prop where
  measurable_action : forall t, Measurable (fun omega => action omega t)
  measurable_reward : forall t, Measurable (fun omega => reward omega t)
  hasLaw_action_zero :
    Measure.map (fun omega => action omega 0) mu =
      Measure.map
        (fun stream : ArmRewardStream K =>
          armStreamAction hK (c * (sigma2 : Real)) stream 0)
        (armStreamMeasure nu)
  hasCondDistrib_feedback_zero :
    condDistrib (fun omega => reward omega 0)
        (fun omega => action omega 0) mu =ᵐ[
          mu.map (fun omega => action omega 0)]
      condDistrib
        (fun stream : ArmRewardStream K =>
          armStreamReward hK (c * (sigma2 : Real)) stream 0)
        (fun stream : ArmRewardStream K =>
          armStreamAction hK (c * (sigma2 : Real)) stream 0)
        (armStreamMeasure nu)
  hasCondDistrib_action : forall i,
    condDistrib (fun omega => action omega (i + 1))
        (fun omega => History.finitePairHistoryOfTrace
          (action omega) (reward omega) i) mu =ᵐ[
          mu.map (fun omega => History.finitePairHistoryOfTrace
            (action omega) (reward omega) i)]
      condDistrib
        (fun stream : ArmRewardStream K =>
          armStreamAction hK (c * (sigma2 : Real)) stream (i + 1))
        (fun stream : ArmRewardStream K =>
          History.finitePairHistoryOfTrace
            (armStreamAction hK (c * (sigma2 : Real)) stream)
            (armStreamReward hK (c * (sigma2 : Real)) stream) i)
        (armStreamMeasure nu)
  hasCondDistrib_feedback : forall i,
    condDistrib (fun omega => reward omega (i + 1))
        (fun omega =>
          (History.finitePairHistoryOfTrace
              (action omega) (reward omega) i,
            action omega (i + 1))) mu =ᵐ[
          mu.map (fun omega =>
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
        (armStreamMeasure nu)

/-- The canonical arm-stream process satisfies the local UCB field bundle. -/
theorem realStationaryUCBSequence_armStream
    {K : Nat} [NeZero K] (hK : 0 < K) (c : Real) (sigma2 : NNReal)
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu] :
    RealStationaryUCBSequence (armStreamMeasure nu) hK c sigma2 nu
      (armStreamAction hK (c * (sigma2 : Real)))
      (armStreamReward hK (c * (sigma2 : Real))) := by
  refine
    { measurable_action := measurable_armStreamAction hK (c * (sigma2 : Real))
      measurable_reward := measurable_armStreamReward hK (c * (sigma2 : Real))
      hasLaw_action_zero := rfl
      hasCondDistrib_feedback_zero :=
        Filter.Eventually.of_forall (fun _action => rfl)
      hasCondDistrib_action := fun _i =>
        Filter.Eventually.of_forall (fun _history => rfl)
      hasCondDistrib_feedback := fun _i =>
        Filter.Eventually.of_forall (fun _historyAction => rfl) }

/--
The complete external observable trajectory has the canonical arm-stream UCB
law whenever the local stationary sequence field bundle holds.
-/
theorem identDistrib_actionRewardTrace_of_realStationaryUCBSequence
    {Omega : Type u} {K : Nat} [NeZero K] [MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (hK : 0 < K) (c : Real) (sigma2 : NNReal)
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu]
    (action : Omega -> ActionTrace (Fin K))
    (reward : Omega -> RewardTrace Real)
    (h : RealStationaryUCBSequence mu hK c sigma2 nu action reward) :
    IdentDistrib
      (fun omega t => (action omega t, reward omega t))
      (fun stream t =>
        (armStreamAction hK (c * (sigma2 : Real)) stream t,
          armStreamReward hK (c * (sigma2 : Real)) stream t))
      mu (armStreamMeasure nu) := by
  exact
    identDistrib_actionRewardTrace_of_split_condDistrib_eq_armStream
      hK c sigma2 mu nu action reward h.measurable_action h.measurable_reward
      h.hasLaw_action_zero h.hasCondDistrib_feedback_zero
      h.hasCondDistrib_action h.hasCondDistrib_feedback

/--
Exact native Real UCB regret from the bundled stationary sequence fields.

This is the local theorem corresponding to the mathematical route of pinned
LML `Bandits.UCB.regret_le`. A theorem about the imported LML `IsAlgEnvSeq`
symbol still requires a common Lean/mathlib toolchain.
-/
theorem regret_le_of_realStationaryUCBSequence
    {Omega : Type u} {K : Nat} [NeZero K] [MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (hK : 0 < K) (c : Real) (sigma2 : NNReal)
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu]
    (action : Omega -> ActionTrace (Fin K))
    (reward : Omega -> RewardTrace Real)
    (h : RealStationaryUCBSequence mu hK c sigma2 nu action reward)
    (n : Nat) (hc : 0 < c) (hsigma2 : sigma2 ≠ 0)
    (hsubG : forall arm : Fin K, HasSubgaussianMGF
      (fun x => x - realKernelMean nu arm) sigma2 (nu arm)) :
    integral mu (fun omega => realKernelRegret nu (action omega) n) <=
      (Finset.univ : Finset (Fin K)).sum (fun arm =>
        8 * c * (sigma2 : Real) * Real.log ((n + 1 : Nat) : Real) /
            realKernelGap nu arm +
          realKernelGap nu arm * (2 + 2 * (constSum c n).toReal)) := by
  exact
    integral_realKernelRegret_externalAction_le_lml_sum_of_split_condDistrib_eq_armStream
      hK c sigma2 mu nu action reward h.measurable_action h.measurable_reward
      h.hasLaw_action_zero h.hasCondDistrib_feedback_zero
      h.hasCondDistrib_action h.hasCondDistrib_feedback n hc hsigma2 hsubG

end UCB
end BanditRLProof
