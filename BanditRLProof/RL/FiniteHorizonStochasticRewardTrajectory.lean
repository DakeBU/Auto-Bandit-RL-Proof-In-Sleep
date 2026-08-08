import BanditRLProof.RL.FiniteHorizonStochasticRewardBellman
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# Finite-horizon stochastic reward trajectory value identity

This module generates finite policy trajectories whose coordinates retain the
sampled action, sampled Real reward, and next state.  Selected rewards need
only the `L1` mean-compatibility contract from the stochastic Bellman layer.
The cumulative sampled reward is proved integrable recursively and its
expectation is identified with both stochastic and mean policy evaluation.
-/

open MeasureTheory

universe u v

namespace BanditRLProof
namespace FiniteHorizonRL

variable {State : Type u} {Action : Type v}
    [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action]

/-- A finite trace of sampled action, reward, and resulting next state. -/
abbrev RewardStepTrace (Action : Type v) (State : Type u) (n : Nat) :=
  Fin n -> Prod Action (Prod Real State)

namespace RewardStepTrace

omit [Fintype State] [Fintype Action] in
/-- Prepending a sampled action-reward-state coordinate is measurable. -/
theorem measurable_cons (n : Nat) :
    Measurable
      (fun p : Prod (Prod Action (Prod Real State))
          (RewardStepTrace Action State n) =>
        @Fin.cons n (fun _ => Prod Action (Prod Real State)) p.1 p.2) := by
  apply measurable_pi_lambda
  intro i
  refine Fin.cases measurable_fst
    (fun j => (measurable_pi_apply j).comp measurable_snd) i

omit [Fintype State] [Fintype Action] in
/-- Removing the first sampled coordinate is measurable. -/
theorem measurable_tail (n : Nat) :
    Measurable
      (fun trace : RewardStepTrace Action State (n + 1) => Fin.tail trace) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_pi_apply i.succ

end RewardStepTrace

/-- An a.e. strongly measurable Real function on a finite type is integrable. -/
theorem integrable_of_fintype_aestronglyMeasurable
    {Omega : Type*} [Fintype Omega] [MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (f : Omega -> Real) (hf : AEStronglyMeasurable f mu) : Integrable f mu := by
  apply Integrable.of_bound hf
    (Finset.sum Finset.univ (fun x => |f x|))
  exact Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs]
    exact Finset.single_le_sum
      (fun y _ => abs_nonneg (f y)) (Finset.mem_univ x)

namespace MDP
namespace MeanCompatibleRewardKernel

variable {mdp : MDP State Action}

/-- One policy action followed by its sampled reward and next state. -/
noncomputable def actionRewardStateKernel
    (source : MeanCompatibleRewardKernel mdp)
    (policy : MarkovPolicy mdp) (stage : Fin mdp.horizon) :
    ProbabilityTheory.Kernel State
      (Prod Action (Prod Real State)) :=
  ProbabilityTheory.Kernel.compProd
    (policy.actionKernel stage) source.rewardNextStateKernel

instance instActionRewardStateKernelIsMarkovKernel
    (source : MeanCompatibleRewardKernel mdp)
    (policy : MarkovPolicy mdp) (stage : Fin mdp.horizon) :
    ProbabilityTheory.IsMarkovKernel
      (source.actionRewardStateKernel policy stage) := by
  unfold actionRewardStateKernel
  infer_instance

/--
Kernel of the next `remaining` sampled action-reward-state coordinates.
The first chronological stage is `mdp.horizon - remaining`.
-/
noncomputable def stochasticTrajectoryKernelRemaining
    (source : MeanCompatibleRewardKernel mdp)
    (policy : MarkovPolicy mdp) :
    (remaining : Nat) -> remaining <= mdp.horizon ->
      ProbabilityTheory.Kernel State
        (RewardStepTrace Action State remaining)
  | 0, _ =>
      ProbabilityTheory.Kernel.deterministic
        (fun _ => fun i => Fin.elim0 i) measurable_const
  | remaining + 1, hremaining =>
      let stage : Fin mdp.horizon :=
        ⟨mdp.horizon - (remaining + 1), by omega⟩
      let tailKernel : ProbabilityTheory.Kernel
          (Prod State (Prod Action (Prod Real State)))
          (RewardStepTrace Action State remaining) :=
        (source.stochasticTrajectoryKernelRemaining policy remaining (by omega)).comap
          (fun p : Prod State (Prod Action (Prod Real State)) => p.2.2.2)
          (show Measurable
              (fun p : Prod State (Prod Action (Prod Real State)) => p.2.2.2) from
            measurable_snd.snd.snd)
      ((source.actionRewardStateKernel policy stage).compProd tailKernel).map
        (fun p =>
          @Fin.cons remaining (fun _ => Prod Action (Prod Real State)) p.1 p.2)

instance instStochasticTrajectoryKernelRemainingIsMarkovKernel
    (source : MeanCompatibleRewardKernel mdp)
    (policy : MarkovPolicy mdp)
    (remaining : Nat) (hremaining : remaining <= mdp.horizon) :
    ProbabilityTheory.IsMarkovKernel
      (source.stochasticTrajectoryKernelRemaining policy remaining hremaining) := by
  induction remaining with
  | zero =>
      unfold stochasticTrajectoryKernelRemaining
      infer_instance
  | succ remaining ih =>
      rw [stochasticTrajectoryKernelRemaining]
      apply ProbabilityTheory.Kernel.IsMarkovKernel.map
      exact RewardStepTrace.measurable_cons remaining

end MeanCompatibleRewardKernel

/-- Sum of the actual sampled rewards in a reward-bearing finite trace. -/
def sampledCumulativeRewardFrom :
    (remaining : Nat) -> RewardStepTrace Action State remaining -> Real
  | 0, _ => 0
  | remaining + 1, trace =>
      (trace 0).2.1 + sampledCumulativeRewardFrom remaining (Fin.tail trace)

omit [Fintype State] [Fintype Action] in
/-- The sampled finite cumulative reward is measurable. -/
theorem measurable_sampledCumulativeRewardFrom (remaining : Nat) :
    Measurable
      (sampledCumulativeRewardFrom (Action := Action) (State := State) remaining) := by
  induction remaining with
  | zero =>
      simp [sampledCumulativeRewardFrom]
  | succ remaining ih =>
      rw [show remaining + 1 = Nat.succ remaining by rfl]
      simp only [sampledCumulativeRewardFrom]
      exact
        (((measurable_pi_apply (0 : Fin (remaining + 1))).snd.fst).add
          (ih.comp (RewardStepTrace.measurable_tail remaining)))

end MDP

namespace MDP.MeanCompatibleRewardKernel

variable {mdp : MDP State Action}

/--
The sampled cumulative reward is `L1` under every statewise stochastic
trajectory law.  No boundedness or second-moment hypothesis is used.
-/
theorem integrable_sampledCumulativeRewardFrom_stochasticTrajectoryKernelRemaining
    (source : MeanCompatibleRewardKernel mdp)
    (policy : MarkovPolicy mdp)
    (remaining : Nat) (hremaining : remaining <= mdp.horizon)
    (state : State) :
    Integrable
      (MDP.sampledCumulativeRewardFrom (Action := Action) (State := State) remaining)
      (source.stochasticTrajectoryKernelRemaining policy remaining hremaining state) := by
  induction remaining generalizing state with
  | zero =>
      rw [stochasticTrajectoryKernelRemaining,
        ProbabilityTheory.Kernel.deterministic_apply]
      exact integrable_dirac'
        (MDP.measurable_sampledCumulativeRewardFrom
          (Action := Action) (State := State) 0).stronglyMeasurable
        (by simp)
  | succ remaining ih =>
      let stage : Fin mdp.horizon :=
        ⟨mdp.horizon - (remaining + 1), by omega⟩
      let tailKernel : ProbabilityTheory.Kernel
          (Prod State (Prod Action (Prod Real State)))
          (RewardStepTrace Action State remaining) :=
        (source.stochasticTrajectoryKernelRemaining policy remaining (by omega)).comap
          (fun p : Prod State (Prod Action (Prod Real State)) => p.2.2.2)
          (show Measurable
              (fun p : Prod State (Prod Action (Prod Real State)) => p.2.2.2) from
            measurable_snd.snd.snd)
      let consStep :=
        fun p : Prod (Prod Action (Prod Real State))
            (RewardStepTrace Action State remaining) =>
          @Fin.cons remaining (fun _ => Prod Action (Prod Real State)) p.1 p.2
      let sampledTail :=
        MDP.sampledCumulativeRewardFrom
          (Action := Action) (State := State) remaining
      let tailNorm : State -> Real := fun nextState =>
        integral
          (source.stochasticTrajectoryKernelRemaining policy remaining
            (by omega) nextState)
          (fun tail => ‖sampledTail tail‖)
      have hcons : Measurable consStep := RewardStepTrace.measurable_cons remaining
      have hreturn : Measurable
          (MDP.sampledCumulativeRewardFrom
            (Action := Action) (State := State) (remaining + 1)) :=
        MDP.measurable_sampledCumulativeRewardFrom (remaining + 1)
      have htailNorm : Measurable tailNorm := by
        exact
          (MDP.measurable_sampledCumulativeRewardFrom
            (Action := Action) (State := State) remaining).norm.stronglyMeasurable
            |>.integral_kernel.measurable
      have hheadBound : Integrable
          (fun head : Prod Action (Prod Real State) =>
            |head.2.1| + tailNorm head.2.2)
          (source.actionRewardStateKernel policy stage state) := by
        let bound := fun head : Prod Action (Prod Real State) =>
          |head.2.1| + tailNorm head.2.2
        have hbound : StronglyMeasurable bound :=
          (measurable_snd.fst.abs.add (htailNorm.comp measurable_snd.snd)).stronglyMeasurable
        unfold actionRewardStateKernel
        apply (ProbabilityTheory.integrable_compProd_iff
          hbound.aestronglyMeasurable).2
        constructor
        · exact Filter.Eventually.of_forall fun action => by
            haveI : IsProbabilityMeasure
                (source.rewardKernel.kernel (state, action)) :=
              RewardKernel.isProbabilityMeasure_apply source.rewardKernel (state, action)
            haveI : IsProbabilityMeasure (mdp.transition (state, action)) := by
              infer_instance
            rw [rewardNextStateKernel, ProbabilityTheory.Kernel.prod_apply]
            have hrewardAbs : Integrable (fun reward : Real => |reward|)
                (source.rewardKernel.kernel (state, action)) := by
              simpa [Real.norm_eq_abs] using
                (source.integrable_reward state action).norm
            exact
              (hrewardAbs.comp_fst (mdp.transition (state, action))).add
                ((integrable_of_fintype (mdp.transition (state, action))
                  tailNorm htailNorm).comp_snd
                    (source.rewardKernel.kernel (state, action)))
        · have hboundAE : AEStronglyMeasurable bound
              (((policy.actionKernel stage).compProd
                source.rewardNextStateKernel) state) :=
            hbound.aestronglyMeasurable
          exact integrable_of_fintype_aestronglyMeasurable
            (policy.actionKernel stage state)
            (fun action =>
              integral (source.rewardNextStateKernel (state, action))
                (fun rewardState => ‖bound (action, rewardState)‖))
            hboundAE.norm.integral_kernel_compProd
      rw [stochasticTrajectoryKernelRemaining]
      rw [ProbabilityTheory.Kernel.map_apply _ hcons]
      apply (integrable_map_measure hreturn.aestronglyMeasurable
        hcons.aemeasurable).2
      have hpreMeas : AEStronglyMeasurable
          (fun p =>
            MDP.sampledCumulativeRewardFrom
              (Action := Action) (State := State) (remaining + 1) (consStep p))
          (((source.actionRewardStateKernel policy stage).compProd tailKernel) state) :=
        (hreturn.comp hcons).aestronglyMeasurable
      apply (ProbabilityTheory.integrable_compProd_iff hpreMeas).2
      constructor
      · exact Filter.Eventually.of_forall fun head => by
          rw [ProbabilityTheory.Kernel.comap_apply]
          change Integrable
            (fun tail => head.2.1 + sampledTail tail)
            (source.stochasticTrajectoryKernelRemaining policy remaining
              (by omega) head.2.2)
          exact (integrable_const _).add (ih (by omega) head.2.2)
      · have hinnerNormAE : AEStronglyMeasurable
            (fun head =>
              integral (tailKernel (state, head))
                (fun tail =>
                  ‖MDP.sampledCumulativeRewardFrom
                    (Action := Action) (State := State) (remaining + 1)
                      (consStep (head, tail))‖))
            (source.actionRewardStateKernel policy stage state) :=
          hpreMeas.norm.integral_kernel_compProd
        refine hheadBound.mono' hinnerNormAE ?_
        exact Filter.Eventually.of_forall fun head => by
          rw [Real.norm_eq_abs,
            abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
          rw [ProbabilityTheory.Kernel.comap_apply]
          change
            integral
                (source.stochasticTrajectoryKernelRemaining policy remaining
                  (by omega) head.2.2)
                (fun tail => ‖head.2.1 + sampledTail tail‖) <=
              |head.2.1| + tailNorm head.2.2
          calc
            _ <= integral
                (source.stochasticTrajectoryKernelRemaining policy remaining
                  (by omega) head.2.2)
                (fun tail => |head.2.1| + ‖sampledTail tail‖) := by
              apply integral_mono_ae
              · exact ((integrable_const _).add
                  (ih (by omega) head.2.2)).norm
              · exact (integrable_const _).add (ih (by omega) head.2.2).norm
              · exact Filter.Eventually.of_forall fun tail => by
                  simpa [Real.norm_eq_abs] using
                    norm_add_le head.2.1 (sampledTail tail)
            _ = |head.2.1| + tailNorm head.2.2 := by
              rw [integral_add (integrable_const _)
                (ih (by omega) head.2.2).norm]
              simp [tailNorm, sampledTail]

/--
Statewise stochastic trajectory identity: expected sampled cumulative reward
equals the independently defined stochastic backward policy value.
-/
theorem integral_sampledCumulativeRewardFrom_stochasticTrajectoryKernelRemaining_eq_stochasticValueRemaining
    (source : MeanCompatibleRewardKernel mdp)
    (policy : MarkovPolicy mdp)
    (remaining : Nat) (hremaining : remaining <= mdp.horizon)
    (state : State) :
    integral
        (source.stochasticTrajectoryKernelRemaining policy remaining hremaining state)
        (MDP.sampledCumulativeRewardFrom
          (Action := Action) (State := State) remaining) =
      source.stochasticValueRemaining policy remaining hremaining state := by
  induction remaining generalizing state with
  | zero =>
      rw [stochasticTrajectoryKernelRemaining,
        ProbabilityTheory.Kernel.deterministic_apply]
      rw [integral_dirac'
        (MDP.sampledCumulativeRewardFrom
          (Action := Action) (State := State) 0)
        (fun i => Fin.elim0 i)]
      · rfl
      · exact (MDP.measurable_sampledCumulativeRewardFrom
          (Action := Action) (State := State) 0).stronglyMeasurable
  | succ remaining ih =>
      let stage : Fin mdp.horizon :=
        ⟨mdp.horizon - (remaining + 1), by omega⟩
      let tailKernel : ProbabilityTheory.Kernel
          (Prod State (Prod Action (Prod Real State)))
          (RewardStepTrace Action State remaining) :=
        (source.stochasticTrajectoryKernelRemaining policy remaining (by omega)).comap
          (fun p : Prod State (Prod Action (Prod Real State)) => p.2.2.2)
          (show Measurable
              (fun p : Prod State (Prod Action (Prod Real State)) => p.2.2.2) from
            measurable_snd.snd.snd)
      let consStep :=
        fun p : Prod (Prod Action (Prod Real State))
            (RewardStepTrace Action State remaining) =>
          @Fin.cons remaining (fun _ => Prod Action (Prod Real State)) p.1 p.2
      have hcons : Measurable consStep := RewardStepTrace.measurable_cons remaining
      have hreturn : Measurable
          (MDP.sampledCumulativeRewardFrom
            (Action := Action) (State := State) (remaining + 1)) :=
        MDP.measurable_sampledCumulativeRewardFrom (remaining + 1)
      have hmapped :=
        source.integrable_sampledCumulativeRewardFrom_stochasticTrajectoryKernelRemaining
          policy (remaining + 1) (by omega) state
      rw [stochasticTrajectoryKernelRemaining,
        ProbabilityTheory.Kernel.map_apply _ hcons] at hmapped
      have hpre : Integrable
          (fun p =>
            MDP.sampledCumulativeRewardFrom
              (Action := Action) (State := State) (remaining + 1) (consStep p))
          (((source.actionRewardStateKernel policy stage).compProd tailKernel) state) :=
        (integrable_map_measure hreturn.aestronglyMeasurable
          hcons.aemeasurable).1 hmapped
      rw [stochasticTrajectoryKernelRemaining]
      rw [ProbabilityTheory.Kernel.map_apply _ hcons]
      rw [integral_map hcons.aemeasurable hreturn.aestronglyMeasurable]
      rw [ProbabilityTheory.integral_compProd hpre]
      have htailIntegral :
          (fun head : Prod Action (Prod Real State) =>
              integral (tailKernel (state, head))
                (fun tail =>
                  MDP.sampledCumulativeRewardFrom
                    (Action := Action) (State := State) (remaining + 1)
                      (consStep (head, tail)))) =
            (fun head => head.2.1 +
              source.stochasticValueRemaining policy remaining
                (by omega) head.2.2) := by
        funext head
        rw [ProbabilityTheory.Kernel.comap_apply]
        change integral
            (source.stochasticTrajectoryKernelRemaining policy remaining
              (by omega) head.2.2)
            (fun tail => head.2.1 +
              MDP.sampledCumulativeRewardFrom
                (Action := Action) (State := State) remaining tail) = _
        rw [integral_add (integrable_const _)
          (source.integrable_sampledCumulativeRewardFrom_stochasticTrajectoryKernelRemaining
            policy remaining (by omega) head.2.2)]
        rw [ih (by omega) head.2.2]
        simp
      have hhead := hpre.integral_compProd
      rw [htailIntegral] at hhead ⊢
      unfold actionRewardStateKernel at hhead ⊢
      rw [ProbabilityTheory.integral_compProd hhead]
      rw [stochasticValueRemaining]
      rfl

/-- Full reward-bearing trajectory law, including the initial state. -/
noncomputable def stochasticTrajectoryMeasure
    (source : MeanCompatibleRewardKernel mdp)
    (policy : MarkovPolicy mdp) (initialState : Measure State) :
    Measure (Prod State (RewardStepTrace Action State mdp.horizon)) :=
  initialState.compProd
    (source.stochasticTrajectoryKernelRemaining policy mdp.horizon le_rfl)

instance instStochasticTrajectoryMeasureIsProbabilityMeasure
    (source : MeanCompatibleRewardKernel mdp)
    (policy : MarkovPolicy mdp) (initialState : Measure State)
    [IsProbabilityMeasure initialState] :
    IsProbabilityMeasure (source.stochasticTrajectoryMeasure policy initialState) := by
  unfold stochasticTrajectoryMeasure
  infer_instance

/-- Sampled cumulative reward on the full stochastic trajectory. -/
def sampledCumulativeReward
    (trajectory : Prod State (RewardStepTrace Action State mdp.horizon)) : Real :=
  MDP.sampledCumulativeRewardFrom mdp.horizon trajectory.2

/-- The full sampled cumulative reward is measurable. -/
theorem measurable_sampledCumulativeReward :
    Measurable (sampledCumulativeReward (mdp := mdp)) :=
  (MDP.measurable_sampledCumulativeRewardFrom mdp.horizon).comp measurable_snd

/-- The full sampled cumulative reward is integrable under its generated law. -/
theorem integrable_sampledCumulativeReward_stochasticTrajectoryMeasure
    (source : MeanCompatibleRewardKernel mdp)
    (policy : MarkovPolicy mdp) (initialState : Measure State)
    [IsProbabilityMeasure initialState] :
    Integrable (sampledCumulativeReward (mdp := mdp))
      (source.stochasticTrajectoryMeasure policy initialState) := by
  unfold stochasticTrajectoryMeasure
  let trajectoryKernel :=
    source.stochasticTrajectoryKernelRemaining policy mdp.horizon le_rfl
  have hfullAE : AEStronglyMeasurable
      (sampledCumulativeReward (mdp := mdp))
      (initialState.compProd trajectoryKernel) :=
    measurable_sampledCumulativeReward.aestronglyMeasurable
  apply (Measure.integrable_compProd_iff hfullAE).2
  constructor
  · exact Filter.Eventually.of_forall fun state =>
      source.integrable_sampledCumulativeRewardFrom_stochasticTrajectoryKernelRemaining
        policy mdp.horizon le_rfl state
  · have hAE : AEStronglyMeasurable
        (fun state => integral (trajectoryKernel state)
          (fun trace => ‖sampledCumulativeReward (mdp := mdp) (state, trace)‖))
        initialState :=
      hfullAE.norm.integral_kernel_compProd
    exact integrable_of_fintype_aestronglyMeasurable initialState _ hAE

/--
Route endpoint: expected sampled cumulative reward equals the stochastic and
existing mean policy values at chronological stage zero.
-/
theorem integral_sampledCumulativeReward_stochasticTrajectoryMeasure_eq_integral_valueAt_zero
    (source : MeanCompatibleRewardKernel mdp)
    (policy : MarkovPolicy mdp) (initialState : Measure State)
    [IsProbabilityMeasure initialState] :
    integral (source.stochasticTrajectoryMeasure policy initialState)
        (sampledCumulativeReward (mdp := mdp)) =
      integral initialState
        (source.stochasticValueAt policy 0 (Nat.zero_le mdp.horizon)) ∧
    integral (source.stochasticTrajectoryMeasure policy initialState)
        (sampledCumulativeReward (mdp := mdp)) =
      integral initialState
        (policy.valueAt 0 (Nat.zero_le mdp.horizon)) := by
  have hintegrable :=
    source.integrable_sampledCumulativeReward_stochasticTrajectoryMeasure
      policy initialState
  have hstochastic :
      integral (source.stochasticTrajectoryMeasure policy initialState)
          (sampledCumulativeReward (mdp := mdp)) =
        integral initialState
          (source.stochasticValueAt policy 0 (Nat.zero_le mdp.horizon)) := by
    unfold stochasticTrajectoryMeasure
    rw [Measure.integral_compProd hintegrable]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun state => by
      change integral
          (source.stochasticTrajectoryKernelRemaining policy mdp.horizon
            le_rfl state)
          (MDP.sampledCumulativeRewardFrom
            (Action := Action) (State := State) mdp.horizon) =
        source.stochasticValueRemaining policy mdp.horizon le_rfl state
      exact
        source.integral_sampledCumulativeRewardFrom_stochasticTrajectoryKernelRemaining_eq_stochasticValueRemaining
          policy mdp.horizon le_rfl state
  refine ⟨hstochastic, ?_⟩
  calc
    integral (source.stochasticTrajectoryMeasure policy initialState)
        (sampledCumulativeReward (mdp := mdp)) =
        integral initialState
          (source.stochasticValueAt policy 0
            (Nat.zero_le mdp.horizon)) := hstochastic
    _ = integral initialState
          (policy.valueAt 0 (Nat.zero_le mdp.horizon)) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun state =>
        congrFun
          (source.stochasticValueAt_eq_valueAt policy 0
            (Nat.zero_le mdp.horizon)) state

end MDP.MeanCompatibleRewardKernel
end FiniteHorizonRL
end BanditRLProof
