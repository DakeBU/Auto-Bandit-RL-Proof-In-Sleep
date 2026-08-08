import BanditRLProof.Algorithms.UCBRealStationaryCanonicalKernelTrajectory

/-!
# Explicit policy semantics for the canonical-kernel stationary UCB trajectory

This module identifies the canonical arm-stream successor action kernel with
the deterministic `realHistoryNextArm` kernel. It then transports the complete
explicit-policy graph to the independently generated canonical pair trajectory
and pairs that graph with the existing expected-average consistency theorem.
-/

namespace BanditRLProof

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace UCB

/-- The explicit finite-history selector encoded by the canonical arm-stream policy. -/
noncomputable def canonicalRealUCBHistorySelector
    {K : Nat} (hK : 0 < K) (c : Real) (sigma2 : NNReal) (n : Nat) :
    History.FinitePairHistory (Fin K) Real n -> Fin K :=
  realHistoryNextArm hK (c * (sigma2 : Real)) n

/-- The explicit deterministic successor-action kernel for stationary Real UCB. -/
noncomputable def canonicalRealUCBPolicyKernel
    {K : Nat} (hK : 0 < K) (c : Real) (sigma2 : NNReal) (n : Nat) :
    Kernel (History.FinitePairHistory (Fin K) Real n) (Fin K) :=
  Kernel.deterministic
    (canonicalRealUCBHistorySelector hK c sigma2 n)
    (measurable_realHistoryNextArm hK (c * (sigma2 : Real)) n)

/-- The explicit canonical selector is measurable on every finite history. -/
theorem measurable_canonicalRealUCBHistorySelector
    {K : Nat} (hK : 0 < K) (c : Real) (sigma2 : NNReal) (n : Nat) :
    Measurable (canonicalRealUCBHistorySelector hK c sigma2 n) := by
  exact measurable_realHistoryNextArm hK (c * (sigma2 : Real)) n

/-- Every explicit policy-kernel section is the corresponding Dirac law. -/
@[simp]
theorem canonicalRealUCBPolicyKernel_apply
    {K : Nat} (hK : 0 < K) (c : Real) (sigma2 : NNReal) (n : Nat)
    (history : History.FinitePairHistory (Fin K) Real n) :
    canonicalRealUCBPolicyKernel hK c sigma2 n history =
      Measure.dirac (canonicalRealUCBHistorySelector hK c sigma2 n history) := by
  rw [canonicalRealUCBPolicyKernel, Kernel.deterministic_apply]

/-- The canonical arm-stream initial-action package is the fixed initial arm. -/
theorem canonicalArmStreamHistoryAlgorithm_initialAction_eq_dirac
    {K : Nat} [NeZero K]
    (hK : 0 < K) (c : Real) (sigma2 : NNReal)
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu] :
    (canonicalArmStreamHistoryAlgorithm hK c sigma2 nu).initialAction =
      Measure.dirac (initializationArm hK 0) := by
  simp [canonicalArmStreamHistoryAlgorithm]

/--
The canonical arm-stream successor action conditional law is the explicit
deterministic UCB policy kernel on its finite-history marginal.
-/
theorem canonicalArmStreamHistoryAlgorithm_policy_ae_eq_explicitPolicyKernel
    {K : Nat} [NeZero K]
    (hK : 0 < K) (c : Real) (sigma2 : NNReal)
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu] (n : Nat) :
    Filter.EventuallyEq
      (ae ((armStreamMeasure nu).map (fun stream : ArmRewardStream K =>
        History.finitePairHistoryOfTrace
          (armStreamAction hK (c * (sigma2 : Real)) stream)
          (armStreamReward hK (c * (sigma2 : Real)) stream) n)))
      ((canonicalArmStreamHistoryAlgorithm hK c sigma2 nu).policy n)
      (canonicalRealUCBPolicyKernel hK c sigma2 n) := by
  let history := fun stream : ArmRewardStream K =>
    History.finitePairHistoryOfTrace
      (armStreamAction hK (c * (sigma2 : Real)) stream)
      (armStreamReward hK (c * (sigma2 : Real)) stream) n
  have haction :
      (fun stream : ArmRewardStream K =>
        armStreamAction hK (c * (sigma2 : Real)) stream (n + 1)) =
        Function.comp (canonicalRealUCBHistorySelector hK c sigma2 n)
          history := by
    funext stream
    exact armStreamAction_succ_eq_realHistoryNextArm_actualHistory
      hK (c * (sigma2 : Real)) stream n
  have hdet := ProbabilityTheory.condDistrib_comp_self
    (μ := armStreamMeasure nu) history
    (measurable_canonicalRealUCBHistorySelector hK c sigma2 n)
  rw [← haction] at hdet
  simpa [canonicalArmStreamHistoryAlgorithm,
    canonicalRealUCBPolicyKernel, history] using hdet

/--
Every generated finite-pair-history marginal agrees with the corresponding
canonical arm-stream history marginal.
-/
theorem canonicalKernelTrajectory_finitePairHistory_map_eq_armStream
    {K : Nat} [NeZero K]
    (hK : 0 < K) (c : Real) (sigma2 : NNReal)
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu] (n : Nat) :
    Measure.map
        (fun trajectory => History.finitePairHistoryOfTrace
          (canonicalKernelTrajectoryAction trajectory)
          (canonicalKernelTrajectoryReward trajectory) n)
        (canonicalKernelTrajectoryMeasure hK c sigma2 nu) =
      Measure.map
        (fun stream : ArmRewardStream K => History.finitePairHistoryOfTrace
          (armStreamAction hK (c * (sigma2 : Real)) stream)
          (armStreamReward hK (c * (sigma2 : Real)) stream) n)
        (armStreamMeasure nu) := by
  let pairHistory := fun trajectory : (t : Nat) -> Prod (Fin K) Real =>
    History.finitePairHistoryOfTrace
      (fun t => (trajectory t).1) (fun t => (trajectory t).2) n
  have hpairHistory : Measurable pairHistory :=
    History.measurable_finitePairHistoryOfTrace
      (fun trajectory : (t : Nat) -> Prod (Fin K) Real =>
        fun t => (trajectory t).1)
      (fun trajectory : (t : Nat) -> Prod (Fin K) Real =>
        fun t => (trajectory t).2)
      (fun t => measurable_fst.comp (measurable_pi_apply t))
      (fun t => measurable_snd.comp (measurable_pi_apply t)) n
  have htrajectory :=
    identDistrib_actionRewardTrace_of_realStationaryUCBSequence
      (canonicalKernelTrajectoryMeasure hK c sigma2 nu)
      hK c sigma2 nu canonicalKernelTrajectoryAction
      canonicalKernelTrajectoryReward
      (realStationaryUCBSequence_canonicalKernelTrajectory
        hK c sigma2 nu)
  have hhistory := htrajectory.comp hpairHistory
  simpa [pairHistory, Function.comp_def,
    canonicalKernelTrajectoryAction, canonicalKernelTrajectoryReward,
    Thompson.canonicalHistoryTrajectoryAction,
    Thompson.canonicalHistoryTrajectoryReward] using hhistory.map_eq

/--
The generated successor action conditional law is the explicit deterministic
UCB policy kernel on the generated finite-history marginal.
-/
theorem canonicalKernelTrajectoryAction_condDistrib_ae_eq_explicitPolicyKernel
    {K : Nat} [NeZero K]
    (hK : 0 < K) (c : Real) (sigma2 : NNReal)
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu] (n : Nat) :
    condDistrib
        (fun trajectory => canonicalKernelTrajectoryAction trajectory (n + 1))
        (fun trajectory => History.finitePairHistoryOfTrace
          (canonicalKernelTrajectoryAction trajectory)
          (canonicalKernelTrajectoryReward trajectory) n)
        (canonicalKernelTrajectoryMeasure hK c sigma2 nu) =ᵐ[
      (canonicalKernelTrajectoryMeasure hK c sigma2 nu).map
        (fun trajectory => History.finitePairHistoryOfTrace
          (canonicalKernelTrajectoryAction trajectory)
          (canonicalKernelTrajectoryReward trajectory) n)]
      canonicalRealUCBPolicyKernel hK c sigma2 n := by
  have hgenerated :=
    (realStationaryUCBSequence_canonicalKernelTrajectory
      hK c sigma2 nu).hasCondDistrib_action n
  have hcanonical :=
    canonicalArmStreamHistoryAlgorithm_policy_ae_eq_explicitPolicyKernel
      hK c sigma2 nu n
  have hhistory :=
    canonicalKernelTrajectory_finitePairHistory_map_eq_armStream
      hK c sigma2 nu n
  rw [← hhistory] at hcanonical
  exact hgenerated.trans <| by
    simpa [canonicalArmStreamHistoryAlgorithm] using hcanonical

/-- The generated initial action is almost surely the canonical initial arm. -/
theorem canonicalKernelTrajectoryAction_zero_ae_eq_initializationArm
    {K : Nat} [NeZero K]
    (hK : 0 < K) (c : Real) (sigma2 : NNReal)
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu] :
    Filter.EventuallyEq
      (ae (canonicalKernelTrajectoryMeasure hK c sigma2 nu))
      (fun trajectory => canonicalKernelTrajectoryAction trajectory 0)
      (fun _trajectory => initializationArm hK 0) := by
  have hmap :=
    (realStationaryUCBSequence_canonicalKernelTrajectory
      hK c sigma2 nu).hasLaw_action_zero
  have hcanonical :
      Measure.map
          (fun stream : ArmRewardStream K =>
            armStreamAction hK (c * (sigma2 : Real)) stream 0)
          (armStreamMeasure nu) =
        Measure.dirac (initializationArm hK 0) := by
    change
      (canonicalArmStreamHistoryAlgorithm hK c sigma2 nu).initialAction =
        Measure.dirac (initializationArm hK 0)
    exact canonicalArmStreamHistoryAlgorithm_initialAction_eq_dirac
      hK c sigma2 nu
  rw [hcanonical] at hmap
  exact
    ConditionalExpectationReward.eventuallyEq_const_of_map_eq_dirac
      (canonicalKernelTrajectoryMeasure hK c sigma2 nu)
      (fun trajectory => canonicalKernelTrajectoryAction trajectory 0)
      (initializationArm hK 0)
      (Thompson.measurable_canonicalHistoryTrajectoryAction_apply 0)
      hmap

/-- Every generated successor action follows the explicit UCB selector a.s. -/
theorem canonicalKernelTrajectoryAction_succ_ae_eq_realHistoryNextArm
    {K : Nat} [NeZero K]
    (hK : 0 < K) (c : Real) (sigma2 : NNReal)
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu] (n : Nat) :
    Filter.Eventually
      (fun trajectory =>
        canonicalKernelTrajectoryAction trajectory (n + 1) =
          canonicalRealUCBHistorySelector hK c sigma2 n
            (History.finitePairHistoryOfTrace
              (canonicalKernelTrajectoryAction trajectory)
              (canonicalKernelTrajectoryReward trajectory) n))
      (ae (canonicalKernelTrajectoryMeasure hK c sigma2 nu)) := by
  let pairTrace := fun trajectory : (t : Nat) -> Prod (Fin K) Real =>
    fun t => (canonicalKernelTrajectoryAction trajectory t,
      canonicalKernelTrajectoryReward trajectory t)
  let canonicalPairTrace := fun stream : ArmRewardStream K =>
    fun t => (armStreamAction hK (c * (sigma2 : Real)) stream t,
      armStreamReward hK (c * (sigma2 : Real)) stream t)
  let policyGraph := {trace : (t : Nat) -> Prod (Fin K) Real |
    (trace (n + 1)).1 =
      canonicalRealUCBHistorySelector hK c sigma2 n
        (History.finitePairHistoryOfTrace
          (fun t => (trace t).1) (fun t => (trace t).2) n)}
  have hhistory : Measurable
      (fun trace : (t : Nat) -> Prod (Fin K) Real =>
        History.finitePairHistoryOfTrace
          (fun t => (trace t).1) (fun t => (trace t).2) n) :=
    History.measurable_finitePairHistoryOfTrace
      (fun trace : (t : Nat) -> Prod (Fin K) Real =>
        fun t => (trace t).1)
      (fun trace : (t : Nat) -> Prod (Fin K) Real =>
        fun t => (trace t).2)
      (fun t => measurable_fst.comp (measurable_pi_apply t))
      (fun t => measurable_snd.comp (measurable_pi_apply t)) n
  have hpolicyGraph : MeasurableSet policyGraph := by
    exact measurableSet_eq_fun
      (measurable_fst.comp (measurable_pi_apply (n + 1)))
      ((measurable_canonicalRealUCBHistorySelector hK c sigma2 n).comp
        hhistory)
  have hcanonical :
      Filter.Eventually
        (fun stream : ArmRewardStream K => canonicalPairTrace stream ∈ policyGraph)
        (ae (armStreamMeasure nu)) := by
    filter_upwards [] with stream
    exact armStreamAction_succ_eq_realHistoryNextArm_actualHistory
      hK (c * (sigma2 : Real)) stream n
  have htrajectory :=
    identDistrib_actionRewardTrace_of_realStationaryUCBSequence
      (canonicalKernelTrajectoryMeasure hK c sigma2 nu)
      hK c sigma2 nu canonicalKernelTrajectoryAction
      canonicalKernelTrajectoryReward
      (realStationaryUCBSequence_canonicalKernelTrajectory
        hK c sigma2 nu)
  have hgenerated := htrajectory.symm.ae_mem_snd hpolicyGraph hcanonical
  simpa [pairTrace, canonicalPairTrace, policyGraph] using hgenerated

/-- One full-measure event carries every successor explicit-policy equality. -/
theorem canonicalKernelTrajectoryAction_succ_ae_eq_realHistoryNextArm_all
    {K : Nat} [NeZero K]
    (hK : 0 < K) (c : Real) (sigma2 : NNReal)
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu] :
    Filter.Eventually
      (fun trajectory => forall n : Nat,
        canonicalKernelTrajectoryAction trajectory (n + 1) =
          canonicalRealUCBHistorySelector hK c sigma2 n
            (History.finitePairHistoryOfTrace
              (canonicalKernelTrajectoryAction trajectory)
              (canonicalKernelTrajectoryReward trajectory) n))
      (ae (canonicalKernelTrajectoryMeasure hK c sigma2 nu)) := by
  rw [ae_all_iff]
  exact canonicalKernelTrajectoryAction_succ_ae_eq_realHistoryNextArm
    hK c sigma2 nu

/-- The complete generated action trace follows the explicit UCB policy a.s. -/
theorem canonicalKernelTrajectoryAction_follows_realHistoryNextArm_ae
    {K : Nat} [NeZero K]
    (hK : 0 < K) (c : Real) (sigma2 : NNReal)
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu] :
    Filter.Eventually
      (fun trajectory =>
        canonicalKernelTrajectoryAction trajectory 0 =
            initializationArm hK 0 /\
          forall n : Nat,
            canonicalKernelTrajectoryAction trajectory (n + 1) =
              canonicalRealUCBHistorySelector hK c sigma2 n
                (History.finitePairHistoryOfTrace
                  (canonicalKernelTrajectoryAction trajectory)
                  (canonicalKernelTrajectoryReward trajectory) n))
      (ae (canonicalKernelTrajectoryMeasure hK c sigma2 nu)) := by
  filter_upwards [
    canonicalKernelTrajectoryAction_zero_ae_eq_initializationArm
      hK c sigma2 nu,
    canonicalKernelTrajectoryAction_succ_ae_eq_realHistoryNextArm_all
      hK c sigma2 nu] with trajectory hzero hsucc
  exact ⟨hzero, hsucc⟩

/--
Armwise-bounded finite-arm laws give one fixed generated process whose actions
follow explicit Real UCB almost surely and whose expected average pseudo-regret
tends to zero.
-/
theorem
    canonicalKernelTrajectoryArmwiseBoundedFiniteArmExpectedAverageRegret_tendsto_zero_and_explicitPolicy
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
        atTop (nhds 0) /\
      Filter.Eventually
        (fun trajectory =>
          canonicalKernelTrajectoryAction trajectory 0 =
              initializationArm hK 0 /\
            forall n : Nat,
              canonicalKernelTrajectoryAction trajectory (n + 1) =
                realHistoryNextArm hK (4 * (sigma2 : Real)) n
                  (History.finitePairHistoryOfTrace
                    (canonicalKernelTrajectoryAction trajectory)
                    (canonicalKernelTrajectoryReward trajectory) n))
        (ae (finiteArmCanonicalKernelTrajectoryMeasure
          hK 4 sigma2 armLaw hprob)) := by
  dsimp only
  let nu := finiteArmRealRewardKernel armLaw
  let sigma2 := Concentration.finiteArmPositiveVarianceProxy
    (fun arm => Concentration.intervalVarianceProxy (lo arm) (hi arm))
  letI : IsMarkovKernel nu :=
    finiteArmRealRewardKernel_isMarkov armLaw hprob
  constructor
  · exact
      canonicalKernelTrajectoryArmwiseBoundedFiniteArmExpectedAverageRegret_tendsto_zero
        hK armLaw hprob lo hi hbound
  · change Filter.Eventually _
      (ae (canonicalKernelTrajectoryMeasure hK 4 sigma2 nu))
    simpa [canonicalRealUCBHistorySelector] using
      (canonicalKernelTrajectoryAction_follows_realHistoryNextArm_ae
        hK 4 sigma2 nu)

end UCB
end BanditRLProof
