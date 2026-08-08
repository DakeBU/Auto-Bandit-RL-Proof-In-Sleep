import BanditRLProof.Algorithms.UCBRealLMLCompat
import BanditRLProof.Algorithms.UCBArmStreamFiniteArmRewardLaws

/-!
# External stationary UCB expected consistency

This module transports the canonical one-policy arm-stream asymptotics through
the complete observable law supplied by `RealStationaryUCBSequence`. The final
endpoint instantiates the route from armwise-bounded Real reward laws.
-/

namespace BanditRLProof

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace UCB

/-- Expected Real pseudo-regret of one fixed external action process. -/
noncomputable def realStationaryExpectedRegret
    {Omega : Type u} {K : Nat} [MeasurableSpace Omega]
    (mu : Measure Omega) (nu : Kernel (Fin K) Real)
    (action : Omega -> ActionTrace (Fin K)) (n : Nat) : Real :=
  integral mu (fun omega => realKernelRegret nu (action omega) n)

/--
The stationary UCB field bundle identifies each external expected-regret term
exactly with the corresponding canonical arm-stream term at `c = 4`.
-/
theorem realStationaryExpectedRegret_eq_armStreamExpectedRegret
    {Omega : Type u} {K : Nat} [NeZero K] [MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (hK : 0 < K) (sigma2 : NNReal)
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu]
    (action : Omega -> ActionTrace (Fin K))
    (reward : Omega -> RewardTrace Real)
    (h : RealStationaryUCBSequence mu hK 4 sigma2 nu action reward)
    (n : Nat) :
    realStationaryExpectedRegret mu nu action n =
      armStreamExpectedRegret hK sigma2 nu n := by
  have htrajectory :=
    identDistrib_actionRewardTrace_of_realStationaryUCBSequence
      mu hK 4 sigma2 nu action reward h
  have haction :=
    identDistrib_action_of_identDistrib_actionRewardTrace
      mu (armStreamMeasure nu) action reward
      (armStreamAction hK (4 * (sigma2 : Real)))
      (armStreamReward hK (4 * (sigma2 : Real))) htrajectory
  have hregret :=
    (haction.comp (measurable_realKernelRegret_actionTrace nu n)).integral_eq
  simpa [realStationaryExpectedRegret, armStreamExpectedRegret] using hregret

/-- External expected regret normalized by `n + 1`. -/
noncomputable def realStationaryExpectedAverageRegret
    {Omega : Type u} {K : Nat} [MeasurableSpace Omega]
    (mu : Measure Omega) (nu : Kernel (Fin K) Real)
    (action : Omega -> ActionTrace (Fin K)) (n : Nat) : Real :=
  realStationaryExpectedRegret mu nu action n / ((n + 1 : Nat) : Real)

/--
Any fixed external process satisfying the stationary UCB field bundle inherits
the canonical sub-Gaussian expected-average consistency theorem.
-/
theorem realStationaryExpectedAverageRegret_tendsto_zero
    {Omega : Type u} {K : Nat} [NeZero K] [MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (hK : 0 < K) (sigma2 : NNReal)
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu]
    (action : Omega -> ActionTrace (Fin K))
    (reward : Omega -> RewardTrace Real)
    (h : RealStationaryUCBSequence mu hK 4 sigma2 nu action reward)
    (hsigma2 : Ne sigma2 0)
    (hsubG : forall arm : Fin K, HasSubgaussianMGF
      (fun x => x - realKernelMean nu arm) sigma2 (nu arm)) :
    Tendsto (realStationaryExpectedAverageRegret mu nu action)
      atTop (nhds 0) := by
  have heq : realStationaryExpectedAverageRegret mu nu action =
      armStreamExpectedAverageRegret hK sigma2 nu := by
    funext n
    simp only [realStationaryExpectedAverageRegret,
      armStreamExpectedAverageRegret]
    rw [realStationaryExpectedRegret_eq_armStreamExpectedRegret
      mu hK sigma2 nu action reward h n]
  rw [heq]
  exact armStreamExpectedAverageRegret_tendsto_zero
    hK sigma2 nu hsigma2 hsubG

/-- Expected regret of an external process over finite Real arm laws. -/
noncomputable def realStationaryArmwiseBoundedFiniteArmExpectedRegret
    {Omega : Type u} {K : Nat} [MeasurableSpace Omega]
    (mu : Measure Omega) (armLaw : Fin K -> Measure Real)
    (action : Omega -> ActionTrace (Fin K)) (n : Nat) : Real :=
  realStationaryExpectedRegret mu (finiteArmRealRewardKernel armLaw) action n

/-- Canonical logarithmic-envelope coefficient for armwise-bounded laws. -/
noncomputable def realStationaryArmwiseBoundedFiniteArmModelCoefficient
    {K : Nat} (armLaw : Fin K -> Measure Real)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (lo hi : Fin K -> Real) : Real :=
  let nu := finiteArmRealRewardKernel armLaw
  let sigma2 := Concentration.finiteArmPositiveVarianceProxy
    (fun arm => Concentration.intervalVarianceProxy (lo arm) (hi arm))
  letI : IsMarkovKernel nu :=
    finiteArmRealRewardKernel_isMarkov armLaw hprob
  armStreamAsymptoticModelCoefficient nu sigma2

/-- External armwise-bounded laws inherit the canonical logarithmic envelope. -/
theorem realStationaryArmwiseBoundedFiniteArmExpectedRegret_nonneg_and_le
    {Omega : Type u} {K : Nat} [NeZero K] [MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (hK : 0 < K)
    (armLaw : Fin K -> Measure Real)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (lo hi : Fin K -> Real)
    (action : Omega -> ActionTrace (Fin K))
    (reward : Omega -> RewardTrace Real)
    (hbound : forall arm,
      Filter.Eventually
        (fun x : Real => Set.Icc (lo arm) (hi arm) x) (ae (armLaw arm)))
    (h : @RealStationaryUCBSequence Omega K _ _ mu _ hK 4
      (Concentration.finiteArmPositiveVarianceProxy
        (fun arm => Concentration.intervalVarianceProxy (lo arm) (hi arm)))
      (finiteArmRealRewardKernel armLaw)
      (finiteArmRealRewardKernel_isMarkov armLaw hprob)
      action reward)
    (n : Nat) :
    0 <= realStationaryArmwiseBoundedFiniteArmExpectedRegret
        mu armLaw action n /\
      realStationaryArmwiseBoundedFiniteArmExpectedRegret
          mu armLaw action n <=
        realStationaryArmwiseBoundedFiniteArmModelCoefficient
            armLaw hprob lo hi *
          (1 + Real.log ((n + 1 : Nat) : Real)) := by
  let nu := finiteArmRealRewardKernel armLaw
  let sigma2 := Concentration.finiteArmPositiveVarianceProxy
    (fun arm => Concentration.intervalVarianceProxy (lo arm) (hi arm))
  letI : IsMarkovKernel nu :=
    finiteArmRealRewardKernel_isMarkov armLaw hprob
  have heq :
      realStationaryArmwiseBoundedFiniteArmExpectedRegret
          mu armLaw action n =
        armStreamArmwiseBoundedFiniteArmExpectedRegret
          hK armLaw hprob lo hi n := by
    simp only [realStationaryArmwiseBoundedFiniteArmExpectedRegret,
      armStreamArmwiseBoundedFiniteArmExpectedRegret,
      armStreamFiniteArmSubgaussianExpectedRegret]
    rw [realStationaryExpectedRegret_eq_armStreamExpectedRegret
      mu hK sigma2 nu action reward h n]
  rw [heq]
  simpa [realStationaryArmwiseBoundedFiniteArmModelCoefficient,
    nu, sigma2] using
      (armStreamArmwiseBoundedFiniteArmExpectedRegret_nonneg_and_le
        hK armLaw hprob lo hi hbound n)

/-- External finite-arm expected regret normalized by `n + 1`. -/
noncomputable def realStationaryArmwiseBoundedFiniteArmExpectedAverageRegret
    {Omega : Type u} {K : Nat} [MeasurableSpace Omega]
    (mu : Measure Omega) (armLaw : Fin K -> Measure Real)
    (action : Omega -> ActionTrace (Fin K)) (n : Nat) : Real :=
  realStationaryArmwiseBoundedFiniteArmExpectedRegret
      mu armLaw action n / ((n + 1 : Nat) : Real)

/--
An external stationary UCB process driven by armwise-bounded finite Real laws
has vanishing expected average regret. The same external measure, action trace,
and reward trace are used at every horizon.
-/
theorem realStationaryArmwiseBoundedFiniteArmExpectedAverageRegret_tendsto_zero
    {Omega : Type u} {K : Nat} [NeZero K] [MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (hK : 0 < K)
    (armLaw : Fin K -> Measure Real)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (lo hi : Fin K -> Real)
    (action : Omega -> ActionTrace (Fin K))
    (reward : Omega -> RewardTrace Real)
    (hbound : forall arm,
      Filter.Eventually
        (fun x : Real => Set.Icc (lo arm) (hi arm) x) (ae (armLaw arm)))
    (h : @RealStationaryUCBSequence Omega K _ _ mu _ hK 4
      (Concentration.finiteArmPositiveVarianceProxy
        (fun arm => Concentration.intervalVarianceProxy (lo arm) (hi arm)))
      (finiteArmRealRewardKernel armLaw)
      (finiteArmRealRewardKernel_isMarkov armLaw hprob)
      action reward) :
    Tendsto
      (realStationaryArmwiseBoundedFiniteArmExpectedAverageRegret
        mu armLaw action)
      atTop (nhds 0) := by
  let nu := finiteArmRealRewardKernel armLaw
  let sigma2 := Concentration.finiteArmPositiveVarianceProxy
    (fun arm => Concentration.intervalVarianceProxy (lo arm) (hi arm))
  letI : IsMarkovKernel nu :=
    finiteArmRealRewardKernel_isMarkov armLaw hprob
  have heq :
      realStationaryArmwiseBoundedFiniteArmExpectedAverageRegret
          mu armLaw action =
        armStreamArmwiseBoundedFiniteArmExpectedAverageRegret
          hK armLaw hprob lo hi := by
    funext n
    simp only [realStationaryArmwiseBoundedFiniteArmExpectedAverageRegret,
      realStationaryArmwiseBoundedFiniteArmExpectedRegret,
      armStreamArmwiseBoundedFiniteArmExpectedAverageRegret,
      armStreamArmwiseBoundedFiniteArmExpectedRegret,
      armStreamFiniteArmSubgaussianExpectedRegret]
    rw [realStationaryExpectedRegret_eq_armStreamExpectedRegret
      mu hK sigma2 nu action reward h n]
  rw [heq]
  exact armStreamArmwiseBoundedFiniteArmExpectedAverageRegret_tendsto_zero
    hK armLaw hprob lo hi hbound

end UCB
end BanditRLProof
