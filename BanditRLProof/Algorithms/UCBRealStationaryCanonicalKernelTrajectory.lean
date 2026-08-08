import BanditRLProof.Algorithms.ThompsonCanonicalTrajectory
import BanditRLProof.Algorithms.UCBRealStationaryFiniteArmRewardLaws

/-!
# Canonical-kernel trajectory source for stationary UCB

This module packages the canonical arm-stream UCB split conditional laws as a
history algorithm and environment, then independently regenerates their
observable action/reward pair process with Mathlib's Ionescu-Tulcea
`Kernel.trajMeasure`. The resulting coordinate process supplies every field of
`RealStationaryUCBSequence` without a caller-provided sample space or law.
-/

namespace BanditRLProof

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace UCB

/-- Canonical arm-stream initial and successor action laws as a history algorithm. -/
noncomputable def canonicalArmStreamHistoryAlgorithm
    {K : Nat} [NeZero K]
    (hK : 0 < K) (c : Real) (sigma2 : NNReal)
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu] :
    Thompson.HistoryAlgorithm (Fin K) Real where
  policy n := condDistrib
    (fun stream : ArmRewardStream K =>
      armStreamAction hK (c * (sigma2 : Real)) stream (n + 1))
    (fun stream : ArmRewardStream K =>
      History.finitePairHistoryOfTrace
        (armStreamAction hK (c * (sigma2 : Real)) stream)
        (armStreamReward hK (c * (sigma2 : Real)) stream) n)
    (armStreamMeasure nu)
  initialAction := Measure.map
    (fun stream : ArmRewardStream K =>
      armStreamAction hK (c * (sigma2 : Real)) stream 0)
    (armStreamMeasure nu)
  initialAction_isProbability := Measure.isProbabilityMeasure_map
    (measurable_armStreamAction hK (c * (sigma2 : Real)) 0).aemeasurable

/-- Canonical arm-stream initial and successor reward laws as a history environment. -/
noncomputable def canonicalArmStreamHistoryEnvironment
    {K : Nat} [NeZero K]
    (hK : 0 < K) (c : Real) (sigma2 : NNReal)
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu] :
    Thompson.HistoryEnvironment (Fin K) Real where
  feedback n := condDistrib
    (fun stream : ArmRewardStream K =>
      armStreamReward hK (c * (sigma2 : Real)) stream (n + 1))
    (fun stream : ArmRewardStream K =>
      (History.finitePairHistoryOfTrace
          (armStreamAction hK (c * (sigma2 : Real)) stream)
          (armStreamReward hK (c * (sigma2 : Real)) stream) n,
        armStreamAction hK (c * (sigma2 : Real)) stream (n + 1)))
    (armStreamMeasure nu)
  initialFeedback := condDistrib
    (fun stream : ArmRewardStream K =>
      armStreamReward hK (c * (sigma2 : Real)) stream 0)
    (fun stream : ArmRewardStream K =>
      armStreamAction hK (c * (sigma2 : Real)) stream 0)
    (armStreamMeasure nu)

/-- Independently regenerated pair trajectory from the canonical UCB split kernels. -/
noncomputable def canonicalKernelTrajectoryMeasure
    {K : Nat} [NeZero K]
    (hK : 0 < K) (c : Real) (sigma2 : NNReal)
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu] :
    Measure ((n : Nat) -> Fin K × Real) :=
  Thompson.canonicalHistoryTrajectoryMeasure
    (canonicalArmStreamHistoryAlgorithm hK c sigma2 nu)
    (canonicalArmStreamHistoryEnvironment hK c sigma2 nu)

instance instCanonicalKernelTrajectoryMeasureIsProbability
    {K : Nat} [NeZero K]
    (hK : 0 < K) (c : Real) (sigma2 : NNReal)
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu] :
    IsProbabilityMeasure
      (canonicalKernelTrajectoryMeasure hK c sigma2 nu) := by
  unfold canonicalKernelTrajectoryMeasure
  infer_instance

/-- Finite-arm-law specialization of the canonical-kernel trajectory measure. -/
noncomputable def finiteArmCanonicalKernelTrajectoryMeasure
    {K : Nat} [NeZero K]
    (hK : 0 < K) (c : Real) (sigma2 : NNReal)
    (armLaw : Fin K -> Measure Real)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm)) :
    Measure ((n : Nat) -> Fin K × Real) :=
  let nu := finiteArmRealRewardKernel armLaw
  letI : IsMarkovKernel nu :=
    finiteArmRealRewardKernel_isMarkov armLaw hprob
  canonicalKernelTrajectoryMeasure hK c sigma2 nu

instance instFiniteArmCanonicalKernelTrajectoryMeasureIsProbability
    {K : Nat} [NeZero K]
    (hK : 0 < K) (c : Real) (sigma2 : NNReal)
    (armLaw : Fin K -> Measure Real)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm)) :
    IsProbabilityMeasure
      (finiteArmCanonicalKernelTrajectoryMeasure
        hK c sigma2 armLaw hprob) := by
  unfold finiteArmCanonicalKernelTrajectoryMeasure
  letI : IsMarkovKernel (finiteArmRealRewardKernel armLaw) :=
    finiteArmRealRewardKernel_isMarkov armLaw hprob
  infer_instance

/-- Action coordinates of the canonical-kernel pair trajectory. -/
def canonicalKernelTrajectoryAction
    {K : Nat} : ((n : Nat) -> Fin K × Real) -> ActionTrace (Fin K) :=
  Thompson.canonicalHistoryTrajectoryAction

/-- Reward coordinates of the canonical-kernel pair trajectory. -/
def canonicalKernelTrajectoryReward
    {K : Nat} : ((n : Nat) -> Fin K × Real) -> RewardTrace Real :=
  Thompson.canonicalHistoryTrajectoryReward

/--
The independently generated canonical-kernel trajectory satisfies all local
stationary UCB split conditional-law fields.
-/
theorem realStationaryUCBSequence_canonicalKernelTrajectory
    {K : Nat} [NeZero K]
    (hK : 0 < K) (c : Real) (sigma2 : NNReal)
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu] :
    RealStationaryUCBSequence
      (canonicalKernelTrajectoryMeasure hK c sigma2 nu)
      hK c sigma2 nu
      canonicalKernelTrajectoryAction canonicalKernelTrajectoryReward := by
  let algorithm := canonicalArmStreamHistoryAlgorithm hK c sigma2 nu
  let environment := canonicalArmStreamHistoryEnvironment hK c sigma2 nu
  let source :=
    Thompson.canonicalHistoryAlgorithmEnvironmentSplitSource
      algorithm environment
  exact
    { measurable_action := source.measurable_action
      measurable_reward := source.measurable_reward
      hasLaw_action_zero := by
        simpa [canonicalKernelTrajectoryMeasure,
          canonicalKernelTrajectoryAction, algorithm,
          canonicalArmStreamHistoryAlgorithm] using
          source.initialAction_map_eq
      hasCondDistrib_feedback_zero := by
        simpa [canonicalKernelTrajectoryMeasure,
          canonicalKernelTrajectoryAction, canonicalKernelTrajectoryReward,
          algorithm, environment, canonicalArmStreamHistoryAlgorithm,
          canonicalArmStreamHistoryEnvironment] using
          source.initialFeedback_condDistrib
      hasCondDistrib_action := by
        intro n
        simpa [canonicalKernelTrajectoryMeasure,
          canonicalKernelTrajectoryAction, canonicalKernelTrajectoryReward,
          algorithm, environment, canonicalArmStreamHistoryAlgorithm,
          canonicalArmStreamHistoryEnvironment] using
          source.policy_condDistrib n
      hasCondDistrib_feedback := by
        intro n
        simpa [canonicalKernelTrajectoryMeasure,
          canonicalKernelTrajectoryAction, canonicalKernelTrajectoryReward,
          algorithm, environment, canonicalArmStreamHistoryAlgorithm,
          canonicalArmStreamHistoryEnvironment] using
          source.feedback_condDistrib n }

/--
Armwise-bounded laws give the logarithmic expected-regret envelope on the
independently regenerated canonical-kernel trajectory.
-/
theorem canonicalKernelTrajectoryArmwiseBoundedFiniteArmExpectedRegret_nonneg_and_le
    {K : Nat} [NeZero K]
    (hK : 0 < K)
    (armLaw : Fin K -> Measure Real)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (lo hi : Fin K -> Real)
    (hbound : forall arm,
      Filter.Eventually
        (fun x : Real => Set.Icc (lo arm) (hi arm) x) (ae (armLaw arm)))
    (n : Nat) :
    let sigma2 := Concentration.finiteArmPositiveVarianceProxy
      (fun arm => Concentration.intervalVarianceProxy (lo arm) (hi arm))
    0 <= realStationaryArmwiseBoundedFiniteArmExpectedRegret
        (finiteArmCanonicalKernelTrajectoryMeasure
          hK 4 sigma2 armLaw hprob) armLaw
        canonicalKernelTrajectoryAction n /\
      realStationaryArmwiseBoundedFiniteArmExpectedRegret
          (finiteArmCanonicalKernelTrajectoryMeasure
            hK 4 sigma2 armLaw hprob) armLaw
          canonicalKernelTrajectoryAction n <=
        realStationaryArmwiseBoundedFiniteArmModelCoefficient
            armLaw hprob lo hi *
          (1 + Real.log ((n + 1 : Nat) : Real)) := by
  dsimp only
  let nu := finiteArmRealRewardKernel armLaw
  let sigma2 := Concentration.finiteArmPositiveVarianceProxy
    (fun arm => Concentration.intervalVarianceProxy (lo arm) (hi arm))
  letI : IsMarkovKernel nu :=
    finiteArmRealRewardKernel_isMarkov armLaw hprob
  change
    0 <= realStationaryArmwiseBoundedFiniteArmExpectedRegret
        (canonicalKernelTrajectoryMeasure hK 4 sigma2 nu) armLaw
        canonicalKernelTrajectoryAction n /\
      realStationaryArmwiseBoundedFiniteArmExpectedRegret
          (canonicalKernelTrajectoryMeasure hK 4 sigma2 nu) armLaw
          canonicalKernelTrajectoryAction n <=
        realStationaryArmwiseBoundedFiniteArmModelCoefficient
            armLaw hprob lo hi *
          (1 + Real.log ((n + 1 : Nat) : Real))
  exact realStationaryArmwiseBoundedFiniteArmExpectedRegret_nonneg_and_le
    (canonicalKernelTrajectoryMeasure hK 4 sigma2 nu) hK
    armLaw hprob lo hi canonicalKernelTrajectoryAction
    canonicalKernelTrajectoryReward hbound
    (realStationaryUCBSequence_canonicalKernelTrajectory
      hK 4 sigma2 nu) n

/--
The expected regret per round of the independently regenerated
canonical-kernel UCB trajectory tends to zero.
-/
theorem
    canonicalKernelTrajectoryArmwiseBoundedFiniteArmExpectedAverageRegret_tendsto_zero
    {K : Nat} [NeZero K]
    (hK : 0 < K)
    (armLaw : Fin K -> Measure Real)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (lo hi : Fin K -> Real)
    (hbound : forall arm,
      Filter.Eventually
        (fun x : Real => Set.Icc (lo arm) (hi arm) x) (ae (armLaw arm))) :
    let sigma2 := Concentration.finiteArmPositiveVarianceProxy
      (fun arm => Concentration.intervalVarianceProxy (lo arm) (hi arm))
    Tendsto
      (realStationaryArmwiseBoundedFiniteArmExpectedAverageRegret
        (finiteArmCanonicalKernelTrajectoryMeasure
          hK 4 sigma2 armLaw hprob) armLaw
        canonicalKernelTrajectoryAction)
      atTop (nhds 0) := by
  dsimp only
  let nu := finiteArmRealRewardKernel armLaw
  let sigma2 := Concentration.finiteArmPositiveVarianceProxy
    (fun arm => Concentration.intervalVarianceProxy (lo arm) (hi arm))
  letI : IsMarkovKernel nu :=
    finiteArmRealRewardKernel_isMarkov armLaw hprob
  change Tendsto
    (realStationaryArmwiseBoundedFiniteArmExpectedAverageRegret
      (canonicalKernelTrajectoryMeasure hK 4 sigma2 nu) armLaw
      canonicalKernelTrajectoryAction) atTop (nhds 0)
  exact
    realStationaryArmwiseBoundedFiniteArmExpectedAverageRegret_tendsto_zero
      (canonicalKernelTrajectoryMeasure hK 4 sigma2 nu) hK
      armLaw hprob lo hi canonicalKernelTrajectoryAction
      canonicalKernelTrajectoryReward hbound
      (realStationaryUCBSequence_canonicalKernelTrajectory
        hK 4 sigma2 nu)

end UCB
end BanditRLProof
