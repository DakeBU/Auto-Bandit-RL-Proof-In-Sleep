import BanditRLProof.Algorithms.ETCRealPrefixLawTransport

/-!
# Native Real ETC source-law adapter

This module converts the action-selected feedback-law fields exposed by an
algorithm/environment sequence into the reward-only scheduled laws consumed by
the native Real exact ETC regret theorem. It does not import LML: the theorem
statement mirrors the relevant `IsAlgEnvSeq` fields so the remaining upstream
wrapper is limited to source-name and action/tie alignment.
-/

namespace BanditRLProof
namespace ETC

open MeasureTheory ProbabilityTheory

/--
External native Real exact ETC regret from action-selected initial and
full-history successor feedback laws.

The exploration action identities turn each action-selected kernel into the
constant law of the scheduled round-robin arm. The complete action/reward
history is then projected to the reward-only prefix expected by the compiled
finite-prefix uniqueness theorem.
-/
theorem integral_realKernelRegret_externalAction_le_exact_sum_of_actionDependent_actionRewardHistory_condDistrib
    {Omega : Type u} {K : Nat} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (spec : ETC.Spec K)
    (nu : ProbabilityTheory.Kernel (Fin K) Real)
    [ProbabilityTheory.IsMarkovKernel nu]
    (sigma2 : NNReal)
    (hsubG : forall arm, ProbabilityTheory.HasSubgaussianMGF
      (fun reward => reward - realKernelMean nu arm) sigma2 (nu arm))
    (hm : 0 < spec.explorationPulls) (n : Nat)
    (hn : K * spec.explorationPulls <= n)
    (action : Omega -> ActionTrace (Fin K))
    (reward : Omega -> RewardTrace Real)
    (haction : forall t, Measurable (fun omega => action omega t))
    (hreward : forall t, Measurable (fun omega => reward omega t))
    (hactionExplore : forall t, t < spec.explorationPulls * K ->
      (fun omega => action omega t) =ᵐ[mu]
        fun _omega => ETC.exploreArm spec t)
    (hzero : ProbabilityTheory.condDistrib
        (fun omega => reward omega 0)
        (fun omega => action omega 0) mu =ᵐ[
          mu.map (fun omega => action omega 0)]
      ProbabilityTheory.Kernel.ofFunOfCountable (fun arm : Fin K => nu arm))
    (hcond : forall i, i < spec.explorationPulls * K - 1 ->
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
          (fun _arm => inferInstance)).kernel)
    (hactionETC : Filter.Eventually
      (fun omega => forall t, t < n ->
        action omega t =
          ETC.realExplorationArgmaxAction spec
            (ETC.realKernelBestArm spec.hK nu) (reward omega) t)
      (ae mu)) :
    integral mu (fun omega => realKernelRegret nu (action omega) n) <=
      (Finset.univ : Finset (Fin K)).sum (fun arm =>
        realKernelGap nu arm *
          ((spec.explorationPulls : Real) +
            ((n - K * spec.explorationPulls : Nat) : Real) *
              Real.exp
                (-(spec.explorationPulls : Real) *
                  (realKernelGap nu arm) ^ 2 /
                    (4 * (sigma2 : Real))))) := by
  apply
    ETC.integral_realKernelRegret_externalAction_le_exact_sum_of_initial_map_eq_condDistrib
      mu spec nu sigma2 hsubG hm n hn action reward hreward
  · have hzeroExplore :
        (fun omega => action omega 0) =ᵐ[mu]
          fun _omega => ETC.exploreArm spec 0 := by
      exact hactionExplore 0 (Nat.mul_pos hm spec.hK)
    have hzeroConst :=
      RewardKernel.condDistrib_ae_eq_const_of_ae_eq_selected
        mu (fun omega => action omega 0) (haction 0)
        (fun omega => reward omega 0)
        id measurable_id
        (ProbabilityTheory.Kernel.ofFunOfCountable
          (fun arm : Fin K => nu arm))
        (fun arm : Fin K => nu arm) (ETC.exploreArm spec 0)
        (by simpa using hzeroExplore) (fun _value => rfl) hzero
    exact RewardKernel.map_eq_of_condDistrib_ae_eq_const
      mu (fun omega => action omega 0) (haction 0)
      (fun omega => reward omega 0) (hreward 0)
      (nu (ETC.exploreArm spec 0)) hzeroConst
  · intro i hi
    let fullCondition : Omega ->
        History.FinitePairHistory (Fin K) Real i × Fin K :=
      fun omega =>
        (History.finitePairHistoryOfTrace
            (action omega) (reward omega) i,
          action omega (i + 1))
    have hfullCondition : Measurable fullCondition :=
      (History.measurable_finitePairHistoryOfTrace
        action reward haction hreward i).prod (haction (i + 1))
    have hselectedConst :=
      RewardKernel.condDistrib_ae_eq_const_of_ae_eq_selected
        mu fullCondition hfullCondition
        (fun omega => reward omega (i + 1))
        Prod.snd measurable_snd
        (RewardKernel.contextIndependentOfActionLaws
          (Context := History.FinitePairHistory (Fin K) Real i)
          (fun arm : Fin K => nu arm)
          (fun _arm => inferInstance)).kernel
        (fun arm : Fin K => nu arm) (ETC.exploreArm spec (i + 1))
        (by
          simpa [fullCondition] using
            hactionExplore (i + 1) (by omega))
        (fun _value => rfl) (hcond i hi)
    let coarse : Omega -> History.FiniteRewardHistory Real i :=
      fun omega => History.finiteRewardHistoryOfTrace (reward omega) i
    let project :
        History.FinitePairHistory (Fin K) Real i × Fin K ->
          History.FiniteRewardHistory Real i :=
      fun value => History.pairHistoryRewardProjection value.1
    have hproject : Measurable project :=
      (History.measurable_pairHistoryRewardProjection
        (Action := Fin K) (Reward := Real) i).comp measurable_fst
    have hcomp : coarse = project ∘ fullCondition := by rfl
    have hcoarsened := RewardKernel.condDistrib_ae_eq_const_of_comp
      mu fullCondition hfullCondition coarse
      (fun omega => reward omega (i + 1)) (hreward (i + 1))
      project hproject hcomp
      (nu (ETC.exploreArm spec (i + 1))) hselectedConst
    simpa [coarse, ProbabilityTheory.Kernel.const_apply] using hcoarsened
  · exact hactionETC

end ETC
end BanditRLProof
