import BanditRLProof.Algorithms.UCBArmStreamConditionalReward

/-!
# Selected reward laws and consistency for canonical stationary UCB

This module transports the stationary selected-reward laws from the latent
arm-stream process to the independently regenerated canonical kernel trajectory,
then pairs those laws with the compiled explicit-policy expected-average result.
-/

namespace BanditRLProof

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace UCB

/--
The generated history/action condition marginal agrees with its canonical
arm-stream counterpart.
-/
theorem canonicalKernelTrajectory_historyAction_map_eq_armStream
    {K : Nat} [NeZero K]
    (hK : 0 < K) (c : Real) (sigma2 : NNReal)
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu] (n : Nat) :
    Measure.map
        (fun trajectory =>
          (History.finitePairHistoryOfTrace
              (canonicalKernelTrajectoryAction trajectory)
              (canonicalKernelTrajectoryReward trajectory) n,
            canonicalKernelTrajectoryAction trajectory (n + 1)))
        (canonicalKernelTrajectoryMeasure hK c sigma2 nu) =
      Measure.map
        (armStreamHistoryAction hK (c * (sigma2 : Real)) n)
        (armStreamMeasure nu) := by
  let pairTrace := fun trajectory : (t : Nat) -> Fin K × Real =>
    fun t => (canonicalKernelTrajectoryAction trajectory t,
      canonicalKernelTrajectoryReward trajectory t)
  let armPairTrace := fun stream : ArmRewardStream K =>
    fun t => (armStreamAction hK (c * (sigma2 : Real)) stream t,
      armStreamReward hK (c * (sigma2 : Real)) stream t)
  let condition := fun trace : (t : Nat) -> Fin K × Real =>
    (History.finitePairHistoryOfTrace
        (fun t => (trace t).1) (fun t => (trace t).2) n,
      (trace (n + 1)).1)
  have hhistory : Measurable
      (fun trace : (t : Nat) -> Fin K × Real =>
        History.finitePairHistoryOfTrace
          (fun t => (trace t).1) (fun t => (trace t).2) n) :=
    History.measurable_finitePairHistoryOfTrace
      (fun trace : (t : Nat) -> Fin K × Real => fun t => (trace t).1)
      (fun trace : (t : Nat) -> Fin K × Real => fun t => (trace t).2)
      (fun t => measurable_fst.comp (measurable_pi_apply t))
      (fun t => measurable_snd.comp (measurable_pi_apply t)) n
  have hcondition : Measurable condition :=
    hhistory.prodMk (measurable_fst.comp (measurable_pi_apply (n + 1)))
  have htrace :=
    identDistrib_actionRewardTrace_of_realStationaryUCBSequence
      (canonicalKernelTrajectoryMeasure hK c sigma2 nu)
      hK c sigma2 nu canonicalKernelTrajectoryAction
      canonicalKernelTrajectoryReward
      (realStationaryUCBSequence_canonicalKernelTrajectory
        hK c sigma2 nu)
  have hmarginal := htrace.comp hcondition
  have harmCondition :
      (fun stream : ArmRewardStream K =>
        (History.finitePairHistoryOfTrace
            (armStreamAction hK (c * (sigma2 : Real)) stream)
            (armStreamReward hK (c * (sigma2 : Real)) stream) n,
          armStreamAction hK (c * (sigma2 : Real)) stream (n + 1))) =
        armStreamHistoryAction hK (c * (sigma2 : Real)) n := by
    funext stream
    rw [armStreamAction_succ]
    simp [armStreamHistoryAction,
      armStreamHistory_eq_finitePairHistoryOfTrace]
  have hgeneratedComp :
      condition ∘ pairTrace =
        (fun trajectory =>
          (History.finitePairHistoryOfTrace
              (canonicalKernelTrajectoryAction trajectory)
              (canonicalKernelTrajectoryReward trajectory) n,
            canonicalKernelTrajectoryAction trajectory (n + 1))) := by
    rfl
  have harmComp :
      condition ∘ armPairTrace =
        armStreamHistoryAction hK (c * (sigma2 : Real)) n := by
    simpa only [condition, armPairTrace, Function.comp_apply] using
      harmCondition
  rw [hgeneratedComp, harmComp] at hmarginal
  exact hmarginal.map_eq

/-- The generated initial reward has the stationary law of its selected arm. -/
theorem canonicalKernelTrajectoryReward_zero_condDistrib_ae_eq_nu
    {K : Nat} [NeZero K]
    (hK : 0 < K) (c : Real) (sigma2 : NNReal)
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu] :
    condDistrib
        (fun trajectory => canonicalKernelTrajectoryReward trajectory 0)
        (fun trajectory => canonicalKernelTrajectoryAction trajectory 0)
        (canonicalKernelTrajectoryMeasure hK c sigma2 nu) =ᵐ[
      (canonicalKernelTrajectoryMeasure hK c sigma2 nu).map
        (fun trajectory => canonicalKernelTrajectoryAction trajectory 0)]
      nu := by
  have hsequence :=
    realStationaryUCBSequence_canonicalKernelTrajectory hK c sigma2 nu
  have hcanonical :=
    canonicalArmStreamHistoryEnvironment_initialFeedback_ae_eq_nu
      hK c sigma2 nu
  have hcanonical' :
      condDistrib
          (fun stream : ArmRewardStream K =>
            armStreamReward hK (c * (sigma2 : Real)) stream 0)
          (fun stream : ArmRewardStream K =>
            armStreamAction hK (c * (sigma2 : Real)) stream 0)
          (armStreamMeasure nu) =ᵐ[
        (armStreamMeasure nu).map
          (fun stream : ArmRewardStream K =>
            armStreamAction hK (c * (sigma2 : Real)) stream 0)]
        nu := by
    simpa [canonicalArmStreamHistoryAlgorithm,
      canonicalArmStreamHistoryEnvironment] using hcanonical
  rw [← hsequence.hasLaw_action_zero] at hcanonical'
  exact hsequence.hasCondDistrib_feedback_zero.trans hcanonical'

/-- Every generated successor reward has the stationary law of the selected arm. -/
theorem canonicalKernelTrajectoryReward_succ_condDistrib_ae_eq_nu
    {K : Nat} [NeZero K]
    (hK : 0 < K) (c : Real) (sigma2 : NNReal)
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu] (n : Nat) :
    condDistrib
        (fun trajectory => canonicalKernelTrajectoryReward trajectory (n + 1))
        (fun trajectory =>
          (History.finitePairHistoryOfTrace
              (canonicalKernelTrajectoryAction trajectory)
              (canonicalKernelTrajectoryReward trajectory) n,
            canonicalKernelTrajectoryAction trajectory (n + 1)))
        (canonicalKernelTrajectoryMeasure hK c sigma2 nu) =ᵐ[
      (canonicalKernelTrajectoryMeasure hK c sigma2 nu).map
        (fun trajectory =>
          (History.finitePairHistoryOfTrace
              (canonicalKernelTrajectoryAction trajectory)
              (canonicalKernelTrajectoryReward trajectory) n,
            canonicalKernelTrajectoryAction trajectory (n + 1)))]
      armStreamSelectedRewardKernel n nu := by
  have hsequence :=
    realStationaryUCBSequence_canonicalKernelTrajectory hK c sigma2 nu
  have hcanonical :=
    canonicalArmStreamHistoryEnvironment_feedback_ae_eq_nu
      hK c sigma2 nu n
  have hmarginal :=
    canonicalKernelTrajectory_historyAction_map_eq_armStream
      hK c sigma2 nu n
  rw [← hmarginal] at hcanonical
  exact hsequence.hasCondDistrib_feedback n |>.trans <| by
    simpa [canonicalArmStreamHistoryEnvironment] using hcanonical

/--
The fresh canonical trajectory simultaneously exposes its stationary selected
reward laws, explicit UCB policy graph, and expected-average consistency.
-/
theorem
    canonicalKernelTrajectoryArmwiseBoundedFiniteArmExpectedAverageRegret_tendsto_zero_and_explicitPolicy_and_selectedRewardLaws
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
    let nu := finiteArmRealRewardKernel armLaw
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
          hK 4 sigma2 armLaw hprob)) /\
      condDistrib
          (fun trajectory => canonicalKernelTrajectoryReward trajectory 0)
          (fun trajectory => canonicalKernelTrajectoryAction trajectory 0)
          (finiteArmCanonicalKernelTrajectoryMeasure
            hK 4 sigma2 armLaw hprob) =ᵐ[
        (finiteArmCanonicalKernelTrajectoryMeasure
          hK 4 sigma2 armLaw hprob).map
            (fun trajectory => canonicalKernelTrajectoryAction trajectory 0)]
        nu /\
      forall n : Nat,
        condDistrib
            (fun trajectory =>
              canonicalKernelTrajectoryReward trajectory (n + 1))
            (fun trajectory =>
              (History.finitePairHistoryOfTrace
                  (canonicalKernelTrajectoryAction trajectory)
                  (canonicalKernelTrajectoryReward trajectory) n,
                canonicalKernelTrajectoryAction trajectory (n + 1)))
            (finiteArmCanonicalKernelTrajectoryMeasure
              hK 4 sigma2 armLaw hprob) =ᵐ[
          (finiteArmCanonicalKernelTrajectoryMeasure
            hK 4 sigma2 armLaw hprob).map
              (fun trajectory =>
                (History.finitePairHistoryOfTrace
                    (canonicalKernelTrajectoryAction trajectory)
                    (canonicalKernelTrajectoryReward trajectory) n,
                  canonicalKernelTrajectoryAction trajectory (n + 1)))]
          armStreamSelectedRewardKernel n nu := by
  dsimp only
  let sigma2 := Concentration.finiteArmPositiveVarianceProxy
    (fun arm => Concentration.intervalVarianceProxy (lo arm) (hi arm))
  let nu := finiteArmRealRewardKernel armLaw
  letI : IsMarkovKernel nu :=
    finiteArmRealRewardKernel_isMarkov armLaw hprob
  have hterminal :=
    canonicalKernelTrajectoryArmwiseBoundedFiniteArmExpectedAverageRegret_tendsto_zero_and_explicitPolicy
      hK armLaw hprob lo hi hbound
  refine ⟨hterminal.1, hterminal.2, ?_, ?_⟩
  · simpa [finiteArmCanonicalKernelTrajectoryMeasure, nu] using
      canonicalKernelTrajectoryReward_zero_condDistrib_ae_eq_nu
        hK 4 sigma2 nu
  · intro n
    simpa [finiteArmCanonicalKernelTrajectoryMeasure, nu] using
      canonicalKernelTrajectoryReward_succ_condDistrib_ae_eq_nu
        hK 4 sigma2 nu n

end UCB
end BanditRLProof
