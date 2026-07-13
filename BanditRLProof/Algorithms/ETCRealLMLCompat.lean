import BanditRLProof.Algorithms.ETCRealHistoryScore

/-!
# Native Real ETC LML field compatibility surface

The pinned LML source currently uses a newer Lean/mathlib toolchain, so ABRL
cannot import its `IsAlgEnvSeq` declaration directly. This module packages the
exact measurable-action, measurable-feedback, action-behavior, and stationary
feedback-law consequences consumed by the local ETC theorem. It is a local
compatibility structure, not an imported LML proof.
-/

namespace BanditRLProof
namespace ETC

open MeasureTheory ProbabilityTheory

/--
The exact consequences of a stationary Real ETC algorithm-environment sequence
used by the local regret route.

The fields correspond to the pinned source's `IsAlgEnvSeq` measurability and
feedback fields together with `ETC.arm_of_lt`, `ETC.arm_mul`, and
`ETC.arm_of_ge`. Conditional laws are stated as `condDistrib` equalities, which
is the Mathlib-facing form consumed by ABRL.
-/
structure RealStationaryETCSequence
    {Omega : Type u} {K : Nat} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu] (spec : ETC.Spec K)
    (nu : ProbabilityTheory.Kernel (Fin K) Real)
    [ProbabilityTheory.IsMarkovKernel nu]
    (action : Omega -> ActionTrace (Fin K))
    (reward : Omega -> RewardTrace Real) : Prop where
  measurable_action : forall t, Measurable (fun omega => action omega t)
  measurable_reward : forall t, Measurable (fun omega => reward omega t)
  arm_of_lt : forall t, t < K * spec.explorationPulls ->
    Filter.EventuallyEq (ae mu)
      (fun omega => action omega t)
      (fun _omega => ETC.exploreArm spec t)
  arm_mul : Filter.EventuallyEq (ae mu)
    (fun omega => action omega (K * spec.explorationPulls))
    (fun omega => ETC.realLeastEncodedArgmax spec.hK
      (fun arm => ETC.realHistoryEmpMean
        (K * spec.explorationPulls - 1)
        (History.finitePairHistoryOfTrace (action omega) (reward omega)
          (K * spec.explorationPulls - 1)) arm))
  arm_of_ge : forall t, K * spec.explorationPulls <= t ->
    Filter.EventuallyEq (ae mu)
      (fun omega => action omega t)
      (fun omega => action omega (K * spec.explorationPulls))
  hasCondDistrib_feedback_zero : ProbabilityTheory.condDistrib
      (fun omega => reward omega 0)
      (fun omega => action omega 0) mu =ᵐ[mu.map (fun omega => action omega 0)]
    ProbabilityTheory.Kernel.ofFunOfCountable (fun arm : Fin K => nu arm)
  hasCondDistrib_feedback : forall i,
    let fullCondition := fun omega : Omega =>
      (History.finitePairHistoryOfTrace
          (action omega) (reward omega) i,
        action omega (i + 1))
    ProbabilityTheory.condDistrib
        (fun omega => reward omega (i + 1))
        fullCondition mu =ᵐ[mu.map fullCondition]
      (RewardKernel.contextIndependentOfActionLaws
        (Context := History.FinitePairHistory (Fin K) Real i)
        (fun arm : Fin K => nu arm)
        (fun _arm => inferInstance)).kernel

/--
Exact native Real ETC regret from the bundled stationary sequence fields.

This is the local theorem corresponding to the mathematical statement of the
pinned LML `Bandits.ETC.regret_le`. A direct theorem about the imported LML
`IsAlgEnvSeq` symbol still requires a common Lean/mathlib toolchain.
-/
theorem regret_le_of_realStationaryETCSequence
    {Omega : Type u} {K : Nat} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (spec : ETC.Spec K)
    (nu : ProbabilityTheory.Kernel (Fin K) Real)
    [ProbabilityTheory.IsMarkovKernel nu]
    (action : Omega -> ActionTrace (Fin K))
    (reward : Omega -> RewardTrace Real)
    (h : ETC.RealStationaryETCSequence mu spec nu action reward)
    (sigma2 : NNReal)
    (hsubG : forall arm, ProbabilityTheory.HasSubgaussianMGF
      (fun x => x - realKernelMean nu arm) sigma2 (nu arm))
    (hm : 0 < spec.explorationPulls) (n : Nat)
    (hn : K * spec.explorationPulls <= n) :
    integral mu (fun omega => realKernelRegret nu (action omega) n) <=
      (Finset.univ : Finset (Fin K)).sum (fun arm =>
        realKernelGap nu arm *
          ((spec.explorationPulls : Real) +
            ((n - K * spec.explorationPulls : Nat) : Real) *
              Real.exp
                (-(spec.explorationPulls : Real) *
                  (realKernelGap nu arm) ^ 2 /
                    (4 * (sigma2 : Real))))) := by
  exact
    ETC.integral_realKernelRegret_externalAction_le_exact_sum_of_actionDependent_actionRewardHistory_condDistrib_of_historyLeastEncodedCommit_persist
      mu spec nu sigma2 hsubG hm n hn action reward
        h.measurable_action h.measurable_reward h.arm_of_lt h.arm_mul
        h.arm_of_ge h.hasCondDistrib_feedback_zero
        (fun i _hi => h.hasCondDistrib_feedback i)

end ETC
end BanditRLProof
