import BanditRLProof.RL.FiniteHorizonStochasticRewardCumulativeConcentration

/-!
# Finite-horizon mean Bellman innovation concentration

This module controls the policy and transition randomness in the mean Bellman
return `r(s, a) + V(s')`. Sampled reward noise is deliberately left to the
separate cumulative reward-deviation theorem.
-/

open MeasureTheory
open scoped ProbabilityTheory BigOperators

universe u v

namespace BanditRLProof
namespace Concentration

/-- A symmetric interval with NNReal radius has variance proxy equal to its square. -/
theorem intervalVarianceProxy_neg_coe (bound : NNReal) :
    intervalVarianceProxy (-(bound : Real)) (bound : Real) = bound ^ 2 := by
  apply NNReal.eq
  simp [intervalVarianceProxy, Real.nnnorm_of_nonneg]

end Concentration

namespace FiniteHorizonRL

variable {State : Type u} {Action : Type v}
    [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action]

/-- Hoeffding proxy for the mean Bellman return with `remaining` decisions. -/
noncomputable def meanBellmanInnovationStepVarianceProxy
    (rewardBound : NNReal) (remaining : Nat) : NNReal :=
  (((remaining : Nat) : NNReal) * rewardBound) ^ 2

/-- Sum of the stage-dependent mean Bellman innovation proxies. -/
noncomputable def meanBellmanInnovationVarianceProxy
    (rewardBound : NNReal) (remaining : Nat) : NNReal :=
  ∑ k ∈ Finset.range remaining,
    meanBellmanInnovationStepVarianceProxy rewardBound (k + 1)

@[simp]
theorem meanBellmanInnovationVarianceProxy_zero (rewardBound : NNReal) :
    meanBellmanInnovationVarianceProxy rewardBound 0 = 0 := by
  simp [meanBellmanInnovationVarianceProxy]

theorem meanBellmanInnovationVarianceProxy_succ
    (rewardBound : NNReal) (remaining : Nat) :
    meanBellmanInnovationVarianceProxy rewardBound (remaining + 1) =
      meanBellmanInnovationStepVarianceProxy rewardBound (remaining + 1) +
        meanBellmanInnovationVarianceProxy rewardBound remaining := by
  simp [meanBellmanInnovationVarianceProxy, Finset.sum_range_succ, add_comm]

theorem meanBellmanInnovationVarianceProxy_pos
    {rewardBound : NNReal} {remaining : Nat}
    (hrewardBound : 0 < rewardBound) (hremaining : 0 < remaining) :
    0 < meanBellmanInnovationVarianceProxy rewardBound remaining := by
  obtain ⟨remaining, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hremaining)
  rw [meanBellmanInnovationVarianceProxy_succ]
  have hstep : 0 < meanBellmanInnovationStepVarianceProxy rewardBound (remaining + 1) := by
    simp [meanBellmanInnovationStepVarianceProxy]
    positivity
  exact add_pos_of_pos_of_nonneg hstep (zero_le _)

namespace MarkovPolicy

/-- Every bounded-mean-reward policy value lies in its remaining reward envelope. -/
theorem valueRemaining_abs_le_of_rewardBound
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (rewardBound : NNReal)
    (hrewardBound : ∀ state action,
      |mdp.reward state action| ≤ (rewardBound : Real))
    (remaining : Nat) (hremaining : remaining ≤ mdp.horizon) (state : State) :
    |policy.valueRemaining remaining hremaining state| ≤
      (remaining : Real) * (rewardBound : Real) := by
  induction remaining generalizing state with
  | zero =>
      simp [valueRemaining]
  | succ remaining ih =>
      rw [valueRemaining]
      rw [← Real.norm_eq_abs]
      have hnorm := norm_integral_le_of_norm_le_const
        (μ := policy.actionKernel
          ⟨mdp.horizon - (remaining + 1), by omega⟩ state)
        (C := ((remaining + 1 : Nat) : Real) * (rewardBound : Real))
        (Filter.Eventually.of_forall fun action => by
          rw [Real.norm_eq_abs]
          have htransition :
              |mdp.transitionValue
                  (policy.valueRemaining remaining (by omega)) state action| ≤
                (remaining : Real) * (rewardBound : Real) := by
            rw [← Real.norm_eq_abs]
            have hinner := norm_integral_le_of_norm_le_const
              (μ := mdp.transition (state, action))
              (C := (remaining : Real) * (rewardBound : Real))
              (Filter.Eventually.of_forall fun nextState => by
                rw [Real.norm_eq_abs]
                exact ih (by omega) nextState)
            simpa [MDP.transitionValue] using hinner
          calc
            |mdp.bellmanQ
                (policy.valueRemaining remaining (by omega)) state action| ≤
                |mdp.reward state action| +
                  |mdp.transitionValue
                    (policy.valueRemaining remaining (by omega)) state action| :=
              abs_add_le _ _
            _ ≤ (rewardBound : Real) +
                (remaining : Real) * (rewardBound : Real) :=
              add_le_add (hrewardBound state action) htransition
            _ = ((remaining + 1 : Nat) : Real) * (rewardBound : Real) := by
              push_cast
              ring)
      simpa [MarkovPolicy.bellman] using hnorm

end MarkovPolicy

namespace MDP

/-- Sum of policy-action and transition innovations in the mean Bellman return. -/
noncomputable def sampledCumulativeMeanBellmanInnovationFrom
    (mdp : MDP State Action) (policy : MarkovPolicy mdp) :
    (remaining : Nat) → remaining ≤ mdp.horizon → State →
      RewardStepTrace Action State remaining → Real
  | 0, _, _, _ => 0
  | remaining + 1, hremaining, state, trace =>
      (mdp.reward state (trace 0).1 +
          policy.valueRemaining remaining (by omega) (trace 0).2.2 -
            policy.valueRemaining (remaining + 1) hremaining state) +
        sampledCumulativeMeanBellmanInnovationFrom mdp policy remaining
          (by omega) (trace 0).2.2 (Fin.tail trace)

/-- The recursive mean Bellman innovation is jointly measurable in start state and trace. -/
theorem measurable_sampledCumulativeMeanBellmanInnovationFrom
    (mdp : MDP State Action) (policy : MarkovPolicy mdp)
    (remaining : Nat) (hremaining : remaining ≤ mdp.horizon) :
    Measurable (fun p : State × RewardStepTrace Action State remaining =>
      mdp.sampledCumulativeMeanBellmanInnovationFrom policy remaining
        hremaining p.1 p.2) := by
  induction remaining with
  | zero =>
      simp [sampledCumulativeMeanBellmanInnovationFrom]
  | succ remaining ih =>
      let head : State × RewardStepTrace Action State (remaining + 1) →
          Action × (Real × State) := fun p => p.2 0
      have hhead : Measurable head := (measurable_pi_apply 0).comp measurable_snd
      have htail : Measurable
          (fun p : State × RewardStepTrace Action State (remaining + 1) =>
            ((head p).2.2, Fin.tail p.2)) :=
        hhead.snd.snd.prodMk
          ((RewardStepTrace.measurable_tail remaining).comp measurable_snd)
      have hheadInnovation : Measurable
          (fun p : State × RewardStepTrace Action State (remaining + 1) =>
            mdp.reward p.1 (head p).1 +
                policy.valueRemaining remaining (by omega) (head p).2.2 -
              policy.valueRemaining (remaining + 1) hremaining p.1) :=
        ((mdp.measurable_reward.comp (measurable_fst.prodMk hhead.fst)).add
          ((policy.measurable_valueRemaining remaining (by omega)).comp
            hhead.snd.snd)).sub
          ((policy.measurable_valueRemaining (remaining + 1) hremaining).comp
            measurable_fst)
      simpa only [sampledCumulativeMeanBellmanInnovationFrom] using
        hheadInnovation.add ((ih (by omega)).comp htail)

end MDP

namespace MDP.MeanCompatibleRewardKernel

variable {mdp : MDP State Action}

/-- Dropping the sampled reward recovers the ordinary action/next-state kernel. -/
theorem actionRewardStateKernel_map_dropReward
    (source : MeanCompatibleRewardKernel mdp)
    (policy : MarkovPolicy mdp) (stage : Fin mdp.horizon) :
    (source.actionRewardStateKernel policy stage).map
        (fun head : Action × (Real × State) => (head.1, head.2.2)) =
      policy.actionStateKernel stage := by
  let dropReward : Action × (Real × State) → Action × State :=
    fun head => (head.1, head.2.2)
  have hdropReward : Measurable dropReward :=
    measurable_fst.prodMk measurable_snd.snd
  apply ProbabilityTheory.Kernel.ext
  intro state
  apply Measure.ext_prod
  intro actionSet stateSet hactionSet hstateSet
  rw [ProbabilityTheory.Kernel.map_apply _ hdropReward]
  rw [Measure.map_apply hdropReward (hactionSet.prod hstateSet)]
  have hpreimage :
      dropReward ⁻¹' (actionSet ×ˢ stateSet) =
        actionSet ×ˢ ((Set.univ : Set Real) ×ˢ stateSet) := by
    ext head
    simp [dropReward]
  rw [hpreimage, actionRewardStateKernel,
    ProbabilityTheory.Kernel.compProd_apply_prod hactionSet
      (MeasurableSet.univ.prod hstateSet)]
  simp_rw [rewardNextStateKernel,
    ProbabilityTheory.Kernel.prod_apply_prod]
  rw [MarkovPolicy.actionStateKernel,
    ProbabilityTheory.Kernel.compProd_apply_prod hactionSet hstateSet]
  simp

/-- The one-step mean Bellman return integrates to the recursive policy value. -/
theorem integral_meanBellmanReturn_actionStateKernel_eq_valueRemaining
    (policy : MarkovPolicy mdp)
    (remaining : Nat) (hremaining : remaining + 1 ≤ mdp.horizon)
    (state : State) :
    ∫ head : Action × State,
        (mdp.reward state head.1 +
          policy.valueRemaining remaining (by omega) head.2)
      ∂ policy.actionStateKernel
          ⟨mdp.horizon - (remaining + 1), by omega⟩ state =
      policy.valueRemaining (remaining + 1) hremaining state := by
  let stage : Fin mdp.horizon :=
    ⟨mdp.horizon - (remaining + 1), by omega⟩
  have hintegrable : Integrable
      (fun head : Action × State =>
        mdp.reward state head.1 +
          policy.valueRemaining remaining (by omega) head.2)
      (policy.actionStateKernel stage state) := by
    apply integrable_of_fintype
    exact (mdp.measurable_reward.comp
        (measurable_const.prodMk measurable_fst)).add
      ((policy.measurable_valueRemaining remaining (by omega)).comp measurable_snd)
  unfold MarkovPolicy.actionStateKernel at hintegrable ⊢
  rw [ProbabilityTheory.integral_compProd hintegrable]
  rw [MarkovPolicy.valueRemaining]
  change (∫ action, ∫ nextState,
      mdp.reward state action +
          policy.valueRemaining remaining (by omega) nextState
        ∂ mdp.transition (state, action)
      ∂ policy.actionKernel stage state) =
    policy.bellman stage
      (policy.valueRemaining remaining (by omega)) state
  unfold MarkovPolicy.bellman
  apply integral_congr_ae
  filter_upwards [] with action
  rw [integral_add (integrable_const _)
    (integrable_of_fintype _ _
      (policy.measurable_valueRemaining remaining (by omega)))]
  simp [MDP.bellmanQ, MDP.transitionValue]

/-- A one-step mean Bellman innovation is sub-Gaussian at its stage envelope. -/
theorem actionStateKernel_meanBellmanInnovation_hasSubgaussianMGF
    (policy : MarkovPolicy mdp)
    (rewardBound : NNReal)
    (hrewardBound : ∀ state action,
      |mdp.reward state action| ≤ (rewardBound : Real))
    (remaining : Nat) (hremaining : remaining + 1 ≤ mdp.horizon)
    (state : State) :
    ProbabilityTheory.HasSubgaussianMGF
      (fun head : Action × State =>
        mdp.reward state head.1 +
          policy.valueRemaining remaining (by omega) head.2 -
            policy.valueRemaining (remaining + 1) hremaining state)
      (meanBellmanInnovationStepVarianceProxy rewardBound (remaining + 1))
      (policy.actionStateKernel
        ⟨mdp.horizon - (remaining + 1), by omega⟩ state) := by
  let bound : NNReal := ((remaining + 1 : Nat) : NNReal) * rewardBound
  let X : Action × State → Real := fun head =>
    mdp.reward state head.1 +
      policy.valueRemaining remaining (by omega) head.2
  have hX : Measurable X :=
    (mdp.measurable_reward.comp
      (measurable_const.prodMk measurable_fst)).add
      ((policy.measurable_valueRemaining remaining (by omega)).comp measurable_snd)
  have hbound : ∀ head, |X head| ≤ (bound : Real) := by
    intro head
    calc
      |X head| ≤ |mdp.reward state head.1| +
          |policy.valueRemaining remaining (by omega) head.2| := abs_add_le _ _
      _ ≤ (rewardBound : Real) +
          (remaining : Real) * (rewardBound : Real) :=
        add_le_add (hrewardBound state head.1)
          (policy.valueRemaining_abs_le_of_rewardBound rewardBound
            hrewardBound remaining (by omega) head.2)
      _ = (bound : Real) := by
        simp [bound]
        ring
  have hsub := Concentration.boundedCentered_hasSubgaussianMGF_of_mem_Icc_integral_eq
    (policy.actionStateKernel
      ⟨mdp.horizon - (remaining + 1), by omega⟩ state)
    hX.aemeasurable
    (Filter.Eventually.of_forall fun head => (abs_le.mp (hbound head)))
    (integral_meanBellmanReturn_actionStateKernel_eq_valueRemaining
      policy remaining hremaining state)
  have hproxy :
      Concentration.intervalVarianceProxy (-(bound : Real)) (bound : Real) =
        meanBellmanInnovationStepVarianceProxy rewardBound (remaining + 1) := by
    rw [Concentration.intervalVarianceProxy_neg_coe]
    rfl
  rw [hproxy] at hsub
  simpa [X] using hsub

/-- The reward-bearing head has the same mean Bellman innovation MGF. -/
theorem actionRewardStateKernel_meanBellmanInnovation_hasSubgaussianMGF
    (source : MeanCompatibleRewardKernel mdp)
    (policy : MarkovPolicy mdp)
    (rewardBound : NNReal)
    (hrewardBound : ∀ state action,
      |mdp.reward state action| ≤ (rewardBound : Real))
    (remaining : Nat) (hremaining : remaining + 1 ≤ mdp.horizon)
    (state : State) :
    ProbabilityTheory.HasSubgaussianMGF
      (fun head : Action × (Real × State) =>
        mdp.reward state head.1 +
          policy.valueRemaining remaining (by omega) head.2.2 -
            policy.valueRemaining (remaining + 1) hremaining state)
      (meanBellmanInnovationStepVarianceProxy rewardBound (remaining + 1))
      (source.actionRewardStateKernel policy
        ⟨mdp.horizon - (remaining + 1), by omega⟩ state) := by
  let dropReward : Action × (Real × State) → Action × State :=
    fun head => (head.1, head.2.2)
  let X : Action × State → Real := fun head =>
    mdp.reward state head.1 +
      policy.valueRemaining remaining (by omega) head.2 -
        policy.valueRemaining (remaining + 1) hremaining state
  have hdropReward : Measurable dropReward :=
    measurable_fst.prodMk measurable_snd.snd
  have hX : Measurable X :=
    ((mdp.measurable_reward.comp
      (measurable_const.prodMk measurable_fst)).add
      ((policy.measurable_valueRemaining remaining (by omega)).comp measurable_snd)).sub
        measurable_const
  have hbase := actionStateKernel_meanBellmanInnovation_hasSubgaussianMGF
    policy rewardBound hrewardBound remaining hremaining state
  have hdropLaw :
      Measure.map dropReward
          (source.actionRewardStateKernel policy
            ⟨mdp.horizon - (remaining + 1), by omega⟩ state) =
        policy.actionStateKernel
          ⟨mdp.horizon - (remaining + 1), by omega⟩ state := by
    rw [← ProbabilityTheory.Kernel.map_apply _ hdropReward]
    rw [source.actionRewardStateKernel_map_dropReward policy]
  apply hbase.congr_identDistrib
  refine
    { aemeasurable_fst := hX.aemeasurable
      aemeasurable_snd := (hX.comp hdropReward).aemeasurable
      map_eq := ?_ }
  calc
    Measure.map X
        (policy.actionStateKernel
          ⟨mdp.horizon - (remaining + 1), by omega⟩ state) =
      Measure.map X
        ((source.actionRewardStateKernel policy
          ⟨mdp.horizon - (remaining + 1), by omega⟩ state).map dropReward) := by
            change Measure.map X
              (policy.actionStateKernel
                ⟨mdp.horizon - (remaining + 1), by omega⟩ state) =
              Measure.map X
                (Measure.map dropReward
                  (source.actionRewardStateKernel policy
                    ⟨mdp.horizon - (remaining + 1), by omega⟩ state))
            rw [hdropLaw]
    _ = Measure.map (X ∘ dropReward)
        (source.actionRewardStateKernel policy
          ⟨mdp.horizon - (remaining + 1), by omega⟩ state) := by
            rw [Measure.map_map hX hdropReward]

/-- The cumulative mean Bellman innovation has the sum of its stage proxies. -/
theorem stochasticTrajectoryKernelRemaining_sampledCumulativeMeanBellmanInnovationFrom_hasSubgaussianMGF
    [StandardBorelSpace State] [StandardBorelSpace Action]
    [Nonempty Action]
    (source : MeanCompatibleRewardKernel mdp)
    (policy : MarkovPolicy mdp)
    (rewardBound : NNReal)
    (hrewardBound : ∀ state action,
      |mdp.reward state action| ≤ (rewardBound : Real))
    (remaining : Nat) (hremaining : remaining ≤ mdp.horizon)
    (state : State) :
    ProbabilityTheory.HasSubgaussianMGF
      (mdp.sampledCumulativeMeanBellmanInnovationFrom policy remaining
        hremaining state)
      (meanBellmanInnovationVarianceProxy rewardBound remaining)
      (source.stochasticTrajectoryKernelRemaining policy
        remaining hremaining state) := by
  induction remaining generalizing state with
  | zero =>
      simpa [MDP.sampledCumulativeMeanBellmanInnovationFrom] using
        (ProbabilityTheory.HasSubgaussianMGF.fun_zero
          (μ := source.stochasticTrajectoryKernelRemaining policy
            0 hremaining state))
  | succ remaining ih =>
      let stage : Fin mdp.horizon :=
        ⟨mdp.horizon - (remaining + 1), by omega⟩
      let headKernel : ProbabilityTheory.Kernel State
          (Action × (Real × State)) :=
        source.actionRewardStateKernel policy stage
      let tailKernel : ProbabilityTheory.Kernel
          (State × (Action × (Real × State)))
          (RewardStepTrace Action State remaining) :=
        (source.stochasticTrajectoryKernelRemaining policy remaining (by omega)).comap
          (fun p : State × (Action × (Real × State)) => p.2.2.2)
          measurable_snd.snd.snd
      let retainNext :
          ((State × (Action × (Real × State))) ×
            RewardStepTrace Action State remaining) →
            State × RewardStepTrace Action State remaining :=
        fun p => (p.1.2.2.2, p.2)
      have hretainNext : Measurable retainNext :=
        measurable_fst.snd.snd.snd.prodMk measurable_snd
      let tailStateKernel : ProbabilityTheory.Kernel
          (State × (Action × (Real × State)))
          (State × RewardStepTrace Action State remaining) :=
        (ProbabilityTheory.Kernel.id ×ₖ tailKernel).map retainNext
      let X : Action × (Real × State) → Real := fun head =>
        mdp.reward state head.1 +
            policy.valueRemaining remaining (by omega) head.2.2 -
          policy.valueRemaining (remaining + 1) hremaining state
      have hX : Measurable X :=
        ((mdp.measurable_reward.comp
          (measurable_const.prodMk measurable_fst)).add
          ((policy.measurable_valueRemaining remaining (by omega)).comp
            measurable_snd.snd)).sub measurable_const
      let Y : State × RewardStepTrace Action State remaining → Real :=
        fun p => mdp.sampledCumulativeMeanBellmanInnovationFrom policy
          remaining (by omega) p.1 p.2
      have hY : Measurable Y :=
        mdp.measurable_sampledCumulativeMeanBellmanInnovationFrom
          policy remaining (by omega)
      have hXkernel : ProbabilityTheory.Kernel.HasSubgaussianMGF
          X (meanBellmanInnovationStepVarianceProxy rewardBound (remaining + 1))
          headKernel (Measure.dirac state) := by
        apply Concentration.kernel_hasSubgaussianMGF_of_ae
          (Measure.dirac state) headKernel X
          (meanBellmanInnovationStepVarianceProxy rewardBound (remaining + 1)) hX
        rw [ae_dirac_eq]
        simpa [X, headKernel, stage] using
          source.actionRewardStateKernel_meanBellmanInnovation_hasSubgaussianMGF
            policy rewardBound hrewardBound remaining hremaining state
      have hYkernel : ProbabilityTheory.Kernel.HasSubgaussianMGF
          Y (meanBellmanInnovationVarianceProxy rewardBound remaining)
          tailStateKernel (Measure.dirac state ⊗ₘ headKernel) := by
        apply Concentration.kernel_hasSubgaussianMGF_of_ae
          (Measure.dirac state ⊗ₘ headKernel) tailStateKernel Y
          (meanBellmanInnovationVarianceProxy rewardBound remaining) hY
        exact Filter.Eventually.of_forall fun input => by
          let nextState : State := input.2.2.2
          have htail := ih (by omega) nextState
          have htailMeas : Measurable
              (mdp.sampledCumulativeMeanBellmanInnovationFrom policy remaining
                (by omega) nextState) :=
            (mdp.measurable_sampledCumulativeMeanBellmanInnovationFrom
              policy remaining (by omega)).comp
              (measurable_const.prodMk measurable_id)
          have htailStateApply : tailStateKernel input =
              (source.stochasticTrajectoryKernelRemaining policy remaining
                (by omega) nextState).map (fun tail => (nextState, tail)) := by
            dsimp [tailStateKernel]
            rw [ProbabilityTheory.Kernel.map_apply _ hretainNext]
            rw [ProbabilityTheory.Kernel.prod_apply,
              ProbabilityTheory.Kernel.id_apply, Measure.dirac_prod]
            rw [Measure.map_map hretainNext measurable_prodMk_left]
            rfl
          apply htail.congr_identDistrib
          refine
            { aemeasurable_fst := htailMeas.aemeasurable
              aemeasurable_snd := hY.aemeasurable
              map_eq := ?_ }
          rw [htailStateApply]
          let embed : RewardStepTrace Action State remaining →
              State × RewardStepTrace Action State remaining :=
            fun tail => (nextState, tail)
          have hembed : Measurable embed := measurable_const.prodMk measurable_id
          calc
            _ = Measure.map (Y ∘ embed)
                (source.stochasticTrajectoryKernelRemaining policy remaining
                  (by omega) nextState) := by rfl
            _ = _ := (Measure.map_map hY hembed).symm
      have hcombinedKernel := hXkernel.add_compProd hYkernel
      have hcombined : ProbabilityTheory.HasSubgaussianMGF
          (fun p => X p.1 + Y p.2)
          (meanBellmanInnovationStepVarianceProxy rewardBound (remaining + 1) +
            meanBellmanInnovationVarianceProxy rewardBound remaining)
          ((headKernel ⊗ₖ tailStateKernel) state) :=
        Concentration.hasSubgaussianMGF_apply_of_kernel_dirac
          (headKernel ⊗ₖ tailStateKernel) state
          (fun p => X p.1 + Y p.2)
          (meanBellmanInnovationStepVarianceProxy rewardBound (remaining + 1) +
            meanBellmanInnovationVarianceProxy rewardBound remaining)
          hcombinedKernel
      let assemble :
          (Action × (Real × State)) ×
              (State × RewardStepTrace Action State remaining) →
            RewardStepTrace Action State (remaining + 1) :=
        fun p => @Fin.cons remaining (fun _ => Action × (Real × State))
          (p.1.1, (p.1.2.1, p.2.1)) p.2.2
      have hassemble : Measurable assemble := by
        have hpair : Measurable
            (fun p : (Action × (Real × State)) ×
                (State × RewardStepTrace Action State remaining) =>
              ((p.1.1, (p.1.2.1, p.2.1)), p.2.2)) :=
          (measurable_fst.fst.prodMk
              (measurable_fst.snd.fst.prodMk measurable_snd.fst)).prodMk
            measurable_snd.snd
        simpa [assemble, Function.comp_def] using
          (RewardStepTrace.measurable_cons remaining).comp hpair
      have hgenerated :
          ((headKernel ⊗ₖ tailStateKernel) state).map assemble =
            source.stochasticTrajectoryKernelRemaining policy
              (remaining + 1) hremaining state := by
        rw [stochasticTrajectoryKernelRemaining]
        rw [ProbabilityTheory.Kernel.map_apply _
          (RewardStepTrace.measurable_cons remaining)]
        ext rewardSet hrewardSet
        rw [Measure.map_apply hassemble hrewardSet]
        rw [ProbabilityTheory.Kernel.compProd_apply
          (hrewardSet.preimage hassemble)]
        rw [Measure.map_apply (RewardStepTrace.measurable_cons remaining)
          hrewardSet]
        rw [ProbabilityTheory.Kernel.compProd_apply
          (hrewardSet.preimage (RewardStepTrace.measurable_cons remaining))]
        congr 1
        funext head
        have hbaseSet : MeasurableSet
            (Prod.mk head ⁻¹' (assemble ⁻¹' rewardSet)) :=
          (hrewardSet.preimage hassemble).preimage measurable_prodMk_left
        have hinnerSet : MeasurableSet
            (retainNext ⁻¹' (Prod.mk head ⁻¹' (assemble ⁻¹' rewardSet))) :=
          hbaseSet.preimage hretainNext
        dsimp [tailStateKernel]
        rw [ProbabilityTheory.Kernel.map_apply _ hretainNext]
        rw [Measure.map_apply hretainNext hbaseSet]
        rw [ProbabilityTheory.Kernel.id_prod_apply' _ _ hinnerSet]
        rfl
      have hstateAgree :
          ∀ᵐ p ∂ ((headKernel ⊗ₖ tailStateKernel) state),
            p.2.1 = p.1.2.2 := by
        apply ProbabilityTheory.Kernel.ae_compProd_of_ae_ae
          (measurableSet_eq_fun measurable_snd.fst measurable_fst.snd.snd)
        filter_upwards [] with head
        let nextState : State := head.2.2
        have htailStateApply : tailStateKernel (state, head) =
            (source.stochasticTrajectoryKernelRemaining policy remaining
              (by omega) nextState).map (fun tail => (nextState, tail)) := by
          dsimp [tailStateKernel]
          rw [ProbabilityTheory.Kernel.map_apply _ hretainNext]
          rw [ProbabilityTheory.Kernel.prod_apply,
            ProbabilityTheory.Kernel.id_apply, Measure.dirac_prod]
          rw [Measure.map_map hretainNext measurable_prodMk_left]
          rfl
        rw [htailStateApply]
        let embed : RewardStepTrace Action State remaining →
            State × RewardStepTrace Action State remaining :=
          fun tail => (nextState, tail)
        have hembed : Measurable embed := measurable_const.prodMk measurable_id
        have heqSet : MeasurableSet
            {p : State × RewardStepTrace Action State remaining |
              p.1 = nextState} :=
          measurableSet_eq_fun measurable_fst measurable_const
        exact (ae_map_iff hembed.aemeasurable heqSet).2
          (Filter.Eventually.of_forall fun tail => rfl)
      have hident : ProbabilityTheory.IdentDistrib
          (fun p => X p.1 + Y p.2)
          (mdp.sampledCumulativeMeanBellmanInnovationFrom policy
            (remaining + 1) hremaining state)
          ((headKernel ⊗ₖ tailStateKernel) state)
          (source.stochasticTrajectoryKernelRemaining policy
            (remaining + 1) hremaining state) := by
        refine
          { aemeasurable_fst := (hX.comp measurable_fst).add
              (hY.comp measurable_snd) |>.aemeasurable
            aemeasurable_snd :=
              (mdp.measurable_sampledCumulativeMeanBellmanInnovationFrom
                policy (remaining + 1) hremaining).comp
                (measurable_const.prodMk measurable_id) |>.aemeasurable
            map_eq := ?_ }
        have hfinal : Measurable
            (mdp.sampledCumulativeMeanBellmanInnovationFrom policy
              (remaining + 1) hremaining state) :=
          (mdp.measurable_sampledCumulativeMeanBellmanInnovationFrom
            policy (remaining + 1) hremaining).comp
            (measurable_const.prodMk measurable_id)
        have hfunction :
            (fun p => X p.1 + Y p.2) =ᵐ[
              (headKernel ⊗ₖ tailStateKernel) state]
              (mdp.sampledCumulativeMeanBellmanInnovationFrom policy
                (remaining + 1) hremaining state) ∘ assemble := by
          filter_upwards [hstateAgree] with p hp
          simp [X, Y, assemble,
            MDP.sampledCumulativeMeanBellmanInnovationFrom, hp]
        rw [Measure.map_congr hfunction]
        calc
          _ = Measure.map
              (mdp.sampledCumulativeMeanBellmanInnovationFrom policy
                (remaining + 1) hremaining state)
              (((headKernel ⊗ₖ tailStateKernel) state).map assemble) := by
                rw [Measure.map_map hfinal hassemble]
          _ = _ := by rw [hgenerated]
      have htarget := hcombined.congr_identDistrib hident
      simpa [meanBellmanInnovationVarianceProxy_succ] using htarget

/-- Fixed-horizon two-sided tail for the cumulative mean Bellman innovation. -/
theorem stochasticTrajectoryKernelRemaining_sampledCumulativeMeanBellmanInnovationFrom_abs_tail_le
    [StandardBorelSpace State] [StandardBorelSpace Action]
    [Nonempty Action]
    (source : MeanCompatibleRewardKernel mdp)
    (policy : MarkovPolicy mdp)
    (rewardBound : NNReal)
    (hrewardBound : ∀ state action,
      |mdp.reward state action| ≤ (rewardBound : Real))
    (remaining : Nat) (hremaining : remaining ≤ mdp.horizon)
    (state : State)
    (htotal : 0 <
      ((meanBellmanInnovationVarianceProxy rewardBound remaining : NNReal) : Real))
    (delta : Real) (hdelta : 0 < delta) (hdelta_le_one : delta ≤ 1) :
    (source.stochasticTrajectoryKernelRemaining policy remaining hremaining state)
      {trace |
        Concentration.subGaussianSumConfidenceRadius
            (meanBellmanInnovationVarianceProxy rewardBound remaining) delta ≤
          |mdp.sampledCumulativeMeanBellmanInnovationFrom policy remaining
            hremaining state trace|} ≤
      ENNReal.ofReal delta := by
  let mu := source.stochasticTrajectoryKernelRemaining policy
    remaining hremaining state
  let F : Filtration Nat
      (inferInstance : MeasurableSpace (RewardStepTrace Action State remaining)) :=
    Filtration.const Nat inferInstance le_rfl
  let Y : Nat → RewardStepTrace Action State remaining → Real :=
    fun _ => mdp.sampledCumulativeMeanBellmanInnovationFrom policy
      remaining hremaining state
  let cY : Nat → NNReal :=
    fun _ => meanBellmanInnovationVarianceProxy rewardBound remaining
  have hstateMeas : Measurable
      (mdp.sampledCumulativeMeanBellmanInnovationFrom policy remaining
        hremaining state) :=
    (mdp.measurable_sampledCumulativeMeanBellmanInnovationFrom
      policy remaining hremaining).comp
      (measurable_const.prodMk measurable_id)
  have hadapted : StronglyAdapted F Y := by
    intro i
    simpa [F, Y] using hstateMeas.stronglyMeasurable
  have hzero : ProbabilityTheory.HasSubgaussianMGF (Y 0) (cY 0) mu := by
    simpa [Y, cY, mu] using
      source.stochasticTrajectoryKernelRemaining_sampledCumulativeMeanBellmanInnovationFrom_hasSubgaussianMGF
        policy rewardBound hrewardBound remaining hremaining state
  have hsucc : ∀ i, i < 1 - 1 →
      ProbabilityTheory.HasCondSubgaussianMGF
        (F i) (F.le i) (Y (i + 1)) (cY (i + 1)) mu := by
    intro i hi
    omega
  have hvarianceSum :
      0 < ((((Finset.range 1).sum cY : NNReal) : Real)) := by
    simpa [cY] using htotal
  simpa [mu, Y, cY] using
    (Concentration.condSubGaussian_sum_abs_tail_ennreal_delta_of_stronglyAdapted
      hadapted hzero 1 hsucc hvarianceSum delta hdelta hdelta_le_one)

end MDP.MeanCompatibleRewardKernel
end FiniteHorizonRL
end BanditRLProof
