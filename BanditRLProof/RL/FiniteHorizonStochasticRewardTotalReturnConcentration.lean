import BanditRLProof.RL.FiniteHorizonStochasticRewardBellmanInnovationConcentration

/-!
# Finite-horizon sampled-return concentration

This module combines selected-reward noise with policy-action and transition
noise. The target random variable is the actual sampled cumulative return minus
the recursive policy value. The additive proxy relies on the product structure
of reward and next-state sampling given the current state and action.
-/

open MeasureTheory
open scoped ProbabilityTheory BigOperators

universe u v

namespace ProbabilityTheory
namespace Kernel

variable {Alpha Beta Gamma : Type*}
    [MeasurableSpace Alpha] [MeasurableSpace Beta] [MeasurableSpace Gamma]

/--
Sampling from `kappa` and then from a kernel that ignores the sampled value is
the same as sampling from the product kernel at the original input.
-/
theorem compProd_prodMkRight_eq_prod
    (kappa : Kernel Alpha Beta) (eta : Kernel Alpha Gamma)
    [IsFiniteKernel kappa] [IsFiniteKernel eta] :
    kappa ⊗ₖ prodMkRight Beta eta = kappa ×ₖ eta := by
  apply Kernel.ext
  intro a
  apply Measure.ext_prod
  intro s t hs ht
  rw [compProd_apply_prod hs ht, prod_apply_prod]
  simp [mul_comm]

/-- Push a first-coordinate-dependent map through the second stage of `compProd`. -/
theorem map_compProd_prodMk
    {Delta : Type*} [MeasurableSpace Delta]
    (kappa : Kernel Alpha Beta)
    (eta : Kernel (Alpha × Beta) Gamma)
    (eta' : Kernel (Alpha × Beta) Delta)
    [IsSFiniteKernel kappa] [IsSFiniteKernel eta] [IsSFiniteKernel eta']
    (g : Beta -> Gamma -> Delta) (hg : Measurable g.uncurry)
    (hmap : forall a b, (eta (a, b)).map (g b) = eta' (a, b)) :
    (kappa ⊗ₖ eta).map (fun p => (p.1, g p.1 p.2)) = kappa ⊗ₖ eta' := by
  have hwhole : Measurable (fun p : Beta × Gamma => (p.1, g p.1 p.2)) :=
    measurable_fst.prodMk (hg.comp (measurable_fst.prodMk measurable_snd))
  apply Kernel.ext
  intro a
  ext s hs
  rw [Kernel.map_apply _ hwhole]
  rw [Measure.map_apply hwhole hs]
  rw [compProd_apply (hs.preimage hwhole), compProd_apply hs]
  congr with b
  have hgb : Measurable (g b) :=
    hg.comp (measurable_const.prodMk measurable_id)
  rw [← hmap a b, Measure.map_apply hgb (measurable_prodMk_left hs)]
  rfl

end Kernel
end ProbabilityTheory

namespace BanditRLProof
namespace FiniteHorizonRL

variable {State : Type u} {Action : Type v}
    [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action]

namespace MDP

end MDP

namespace MarkovPolicy

/-- Retain the current state together with one sampled action/next-state pair. -/
noncomputable def retainedActionStateKernel
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (stage : Fin mdp.horizon) :
    ProbabilityTheory.Kernel State (State × (Action × State)) :=
  ProbabilityTheory.Kernel.id ×ₖ policy.actionStateKernel stage

instance instRetainedActionStateKernelIsMarkovKernel
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (stage : Fin mdp.horizon) :
    ProbabilityTheory.IsMarkovKernel
      (policy.retainedActionStateKernel stage) := by
  unfold retainedActionStateKernel
  infer_instance

end MarkovPolicy

namespace MDP

/-- Actual sampled cumulative return centered at the recursive policy value. -/
noncomputable def sampledCumulativeReturnDeviationFrom
    (mdp : MDP State Action) (policy : MarkovPolicy mdp)
    (remaining : Nat) (hremaining : remaining <= mdp.horizon)
    (state : State) (trace : RewardStepTrace Action State remaining) : Real :=
  sampledCumulativeRewardFrom remaining trace -
    policy.valueRemaining remaining hremaining state

/-- The sampled-return deviation is jointly measurable in start state and trace. -/
theorem measurable_sampledCumulativeReturnDeviationFrom
    (mdp : MDP State Action) (policy : MarkovPolicy mdp)
    (remaining : Nat) (hremaining : remaining <= mdp.horizon) :
    Measurable (fun p : State × RewardStepTrace Action State remaining =>
      mdp.sampledCumulativeReturnDeviationFrom policy remaining
        hremaining p.1 p.2) := by
  exact
    ((measurable_sampledCumulativeRewardFrom remaining).comp measurable_snd).sub
      ((policy.measurable_valueRemaining remaining hremaining).comp measurable_fst)

/--
The centered sampled return splits pathwise into selected-reward noise and the
mean Bellman innovation. No probabilistic independence is used in this identity.
-/
theorem sampledCumulativeReturnDeviationFrom_eq_rewardDeviation_add_meanBellmanInnovation
    (mdp : MDP State Action) (policy : MarkovPolicy mdp)
    (remaining : Nat) (hremaining : remaining <= mdp.horizon)
    (state : State) (trace : RewardStepTrace Action State remaining) :
    mdp.sampledCumulativeReturnDeviationFrom policy remaining
        hremaining state trace =
      mdp.sampledCumulativeRewardDeviationFrom remaining state trace +
        mdp.sampledCumulativeMeanBellmanInnovationFrom policy remaining
          hremaining state trace := by
  induction remaining generalizing state with
  | zero =>
      simp [sampledCumulativeReturnDeviationFrom, sampledCumulativeRewardFrom,
        sampledCumulativeRewardDeviationFrom,
        sampledCumulativeMeanBellmanInnovationFrom, MarkovPolicy.valueRemaining]
  | succ remaining ih =>
      have htail := ih (by omega) (trace 0).2.2 (Fin.tail trace)
      simp only [sampledCumulativeReturnDeviationFrom] at htail
      simp only [sampledCumulativeReturnDeviationFrom,
        sampledCumulativeRewardFrom, sampledCumulativeRewardDeviationFrom,
        sampledCumulativeMeanBellmanInnovationFrom]
      linarith

namespace MeanCompatibleRewardKernel

variable {mdp : MDP State Action}

/-- Center a sampled reward using the retained state/action coordinates. -/
def rewardDeviationAfterActionState (mdp : MDP State Action) :
    ((State × (Action × State)) × Real) -> Real :=
  fun p => p.2 - mdp.reward p.1.1 p.1.2.1

theorem measurable_rewardDeviationAfterActionState (mdp : MDP State Action) :
    Measurable (rewardDeviationAfterActionState mdp) := by
  exact measurable_snd.sub
    (mdp.measurable_reward.comp
      (measurable_fst.fst.prodMk measurable_fst.snd.fst))

/-- Raw reward sampled from the retained current-state/action coordinates. -/
noncomputable def rawRewardKernelAfterActionState
    (source : MeanCompatibleRewardKernel mdp) :
    ProbabilityTheory.Kernel (State × (Action × State)) Real :=
  source.rewardKernel.kernel.comap
    (fun p => (p.1, p.2.1)) (by fun_prop)

instance instRawRewardKernelAfterActionStateIsMarkovKernel
    (source : MeanCompatibleRewardKernel mdp) :
    ProbabilityTheory.IsMarkovKernel
      source.rawRewardKernelAfterActionState := by
  unfold rawRewardKernelAfterActionState
  infer_instance

/--
Reward residual sampled after retaining the current state and an already sampled
action/next-state pair.
-/
noncomputable def rewardDeviationKernelAfterActionState
    (source : MeanCompatibleRewardKernel mdp) :
    ProbabilityTheory.Kernel (State × (Action × State)) Real :=
  (ProbabilityTheory.Kernel.id ×ₖ
      source.rawRewardKernelAfterActionState).map
    (rewardDeviationAfterActionState mdp)

instance instRewardDeviationKernelAfterActionStateIsMarkovKernel
    (source : MeanCompatibleRewardKernel mdp) :
    ProbabilityTheory.IsMarkovKernel
      source.rewardDeviationKernelAfterActionState := by
  unfold rewardDeviationKernelAfterActionState
  exact ProbabilityTheory.Kernel.IsMarkovKernel.map _
    (measurable_rewardDeviationAfterActionState mdp)

/-- Pointwise law of the retained-state centered reward kernel. -/
theorem rewardDeviationKernelAfterActionState_apply
    (source : MeanCompatibleRewardKernel mdp)
    (p : State × (Action × State)) :
    source.rewardDeviationKernelAfterActionState p =
      (source.rewardKernel.kernel (p.1, p.2.1)).map
        (fun reward => reward - mdp.reward p.1 p.2.1) := by
  unfold rewardDeviationKernelAfterActionState
  rw [ProbabilityTheory.Kernel.map_apply _
    (measurable_rewardDeviationAfterActionState mdp)]
  rw [ProbabilityTheory.Kernel.prod_apply]
  rw [ProbabilityTheory.Kernel.id_apply,
    rawRewardKernelAfterActionState,
    ProbabilityTheory.Kernel.comap_apply, Measure.dirac_prod]
  rw [Measure.map_map (measurable_rewardDeviationAfterActionState mdp)
    (by fun_prop)]
  rfl

/-- The retained-state reward residual kernel inherits the uniform reward MGF. -/
theorem rewardDeviationKernelAfterActionState_hasSubgaussianMGF
    [StandardBorelSpace State] [StandardBorelSpace Action]
    (source : MeanCompatibleRewardKernel mdp)
    (varianceProxy : NNReal)
    (law : source.UniformSubgaussianRewardLaw varianceProxy)
    (base : Measure (State × (Action × State)))
    [IsFiniteMeasure base] :
    ProbabilityTheory.Kernel.HasSubgaussianMGF id varianceProxy
      source.rewardDeviationKernelAfterActionState base := by
  have hpoint : forall p : State × (Action × State),
      ProbabilityTheory.HasSubgaussianMGF id varianceProxy
        (source.rewardDeviationKernelAfterActionState p) := by
    intro p
    rw [source.rewardDeviationKernelAfterActionState_apply p]
    exact (ProbabilityTheory.HasSubgaussianMGF.id_map_iff
      (measurable_id.sub measurable_const).aemeasurable).2
        (law.hasSubgaussianMGF p.1 p.2.1)
  constructor
  · intro t
    rw [Measure.integrable_comp_iff (by fun_prop)]
    constructor
    · exact Filter.Eventually.of_forall fun p =>
        (hpoint p).integrable_exp_mul t
    · exact integrable_of_fintype _ _ (measurable_of_finite _)
  · exact Filter.Eventually.of_forall fun p t => (hpoint p).mgf_le t

/-- Ignore the outer duplicated state and sample the raw retained-coordinate reward. -/
noncomputable def rawRewardKernelAfterRetainedActionState
    (source : MeanCompatibleRewardKernel mdp) :
    ProbabilityTheory.Kernel
      (State × (State × (Action × State))) Real :=
  source.rawRewardKernelAfterActionState.prodMkLeft State

/-- Ignore the outer duplicated state and sample the centered reward residual. -/
noncomputable def rewardDeviationKernelAfterRetainedActionState
    (source : MeanCompatibleRewardKernel mdp) :
    ProbabilityTheory.Kernel
      (State × (State × (Action × State))) Real :=
  source.rewardDeviationKernelAfterActionState.prodMkLeft State

instance instRawRewardKernelAfterRetainedActionStateIsMarkovKernel
    (source : MeanCompatibleRewardKernel mdp) :
    ProbabilityTheory.IsMarkovKernel
      source.rawRewardKernelAfterRetainedActionState := by
  unfold rawRewardKernelAfterRetainedActionState
  infer_instance

instance instRewardDeviationKernelAfterRetainedActionStateIsMarkovKernel
    (source : MeanCompatibleRewardKernel mdp) :
    ProbabilityTheory.IsMarkovKernel
      source.rewardDeviationKernelAfterRetainedActionState := by
  unfold rewardDeviationKernelAfterRetainedActionState
  infer_instance

/-- Add the retained MDP mean back to a centered reward residual. -/
def uncenterRewardAfterRetainedActionState (mdp : MDP State Action) :
    State × (Action × State) -> Real -> Real :=
  fun retained residual => residual + mdp.reward retained.1 retained.2.1

theorem measurable_uncenterRewardAfterRetainedActionState
    (mdp : MDP State Action) :
    Measurable (uncenterRewardAfterRetainedActionState mdp).uncurry := by
  exact measurable_snd.add
    (mdp.measurable_reward.comp
      (measurable_fst.fst.prodMk measurable_fst.snd.fst))

/-- Centering and then restoring the retained MDP mean recovers the raw reward law. -/
theorem rewardDeviationKernelAfterRetainedActionState_map_uncenter
    (source : MeanCompatibleRewardKernel mdp)
    (outer : State) (retained : State × (Action × State)) :
    (source.rewardDeviationKernelAfterRetainedActionState
        (outer, retained)).map
        (uncenterRewardAfterRetainedActionState mdp retained) =
      source.rawRewardKernelAfterRetainedActionState (outer, retained) := by
  change
    (source.rewardDeviationKernelAfterActionState retained).map
        (uncenterRewardAfterRetainedActionState mdp retained) =
      source.rawRewardKernelAfterActionState retained
  have huncenter : Measurable
      (uncenterRewardAfterRetainedActionState mdp retained) := by
    exact (measurable_uncenterRewardAfterRetainedActionState mdp).comp
      (measurable_const.prodMk measurable_id)
  have hcenter : Measurable (fun reward : Real =>
      reward - mdp.reward retained.1 retained.2.1) :=
    measurable_id.sub measurable_const
  rw [source.rewardDeviationKernelAfterActionState_apply retained]
  rw [Measure.map_map huncenter hcenter]
  simp [uncenterRewardAfterRetainedActionState, Function.comp_def,
    rawRewardKernelAfterActionState]

/-- Restore raw rewards throughout the retained action-state product kernel. -/
theorem retainedActionStateKernel_compProd_rewardDeviation_map_uncenter
    (source : MeanCompatibleRewardKernel mdp)
    (policy : MarkovPolicy mdp) (stage : Fin mdp.horizon) :
    ((policy.retainedActionStateKernel stage) ⊗ₖ
        source.rewardDeviationKernelAfterRetainedActionState).map
        (fun p =>
          (p.1, uncenterRewardAfterRetainedActionState mdp p.1 p.2)) =
      (policy.retainedActionStateKernel stage) ⊗ₖ
        source.rawRewardKernelAfterRetainedActionState := by
  exact ProbabilityTheory.Kernel.map_compProd_prodMk
    (policy.retainedActionStateKernel stage)
    source.rewardDeviationKernelAfterRetainedActionState
    source.rawRewardKernelAfterRetainedActionState
    (uncenterRewardAfterRetainedActionState mdp)
    (measurable_uncenterRewardAfterRetainedActionState mdp)
    (fun outer retained =>
      source.rewardDeviationKernelAfterRetainedActionState_map_uncenter
        outer retained)

/-- Arrange retained current/action/next-state coordinates with a raw reward. -/
def assembleRawRewardAfterRetainedActionState :
    ((State × (Action × State)) × Real) ->
      Action × (Real × State) :=
  fun p => (p.1.2.1, (p.2, p.1.2.2))

omit [Fintype State] [Fintype Action] in
theorem measurable_assembleRawRewardAfterRetainedActionState :
    Measurable
      (assembleRawRewardAfterRetainedActionState
        (State := State) (Action := Action)) := by
  exact measurable_fst.snd.fst.prodMk
    (measurable_snd.prodMk measurable_fst.snd.snd)

/-- The retained raw-reward construction is exactly the existing head kernel. -/
theorem retainedActionStateKernel_compProd_rawReward_map_assemble
    (source : MeanCompatibleRewardKernel mdp)
    (policy : MarkovPolicy mdp) (stage : Fin mdp.horizon) :
    ((policy.retainedActionStateKernel stage) ⊗ₖ
        source.rawRewardKernelAfterRetainedActionState).map
        (assembleRawRewardAfterRetainedActionState
          (State := State) (Action := Action)) =
      source.actionRewardStateKernel policy stage := by
  apply ProbabilityTheory.Kernel.ext
  intro state
  apply Measure.ext_prod₃
  intro actionSet rewardSet stateSet hactionSet hrewardSet hstateSet
  rw [ProbabilityTheory.Kernel.map_apply _
    measurable_assembleRawRewardAfterRetainedActionState]
  rw [Measure.map_apply
    measurable_assembleRawRewardAfterRetainedActionState
    (hactionSet.prod (hrewardSet.prod hstateSet))]
  have hpreimage :
      assembleRawRewardAfterRetainedActionState
          (State := State) (Action := Action) ⁻¹'
          (actionSet ×ˢ (rewardSet ×ˢ stateSet)) =
        ((Set.univ : Set State) ×ˢ (actionSet ×ˢ stateSet)) ×ˢ
          rewardSet := by
    ext p
    simp [assembleRawRewardAfterRetainedActionState]
    tauto
  rw [hpreimage]
  rw [ProbabilityTheory.Kernel.compProd_apply_prod
    (MeasurableSet.univ.prod (hactionSet.prod hstateSet)) hrewardSet]
  simp_rw [rawRewardKernelAfterRetainedActionState,
    ProbabilityTheory.Kernel.prodMkLeft_apply,
    rawRewardKernelAfterActionState,
    ProbabilityTheory.Kernel.comap_apply]
  rw [MarkovPolicy.retainedActionStateKernel,
    ProbabilityTheory.Kernel.prod_apply,
    ProbabilityTheory.Kernel.id_apply, Measure.dirac_prod]
  have hrewardValue : Measurable
      (fun retained : State × (Action × State) =>
        source.rewardKernel.kernel (retained.1, retained.2.1) rewardSet) :=
    (source.rewardKernel.kernel.measurable_coe hrewardSet).comp
      (measurable_fst.prodMk measurable_snd.fst)
  have hretain : Measurable
      (Prod.mk state : (Action × State) -> State × (Action × State)) :=
    measurable_const.prodMk measurable_id
  rw [MeasureTheory.setLIntegral_map
    (MeasurableSet.univ.prod (hactionSet.prod hstateSet))
    hrewardValue hretain]
  have hretainPreimage :
      (Prod.mk state) ⁻¹'
          ((Set.univ : Set State) ×ˢ (actionSet ×ˢ stateSet)) =
        actionSet ×ˢ stateSet := by
    ext p
    simp
  rw [hretainPreimage]
  rw [MarkovPolicy.actionStateKernel]
  let rewardValue : Action × State -> ENNReal := fun x =>
    source.rewardKernel.kernel (state, x.1) rewardSet
  have hrewardValue' : Measurable rewardValue :=
    (source.rewardKernel.kernel.measurable_coe hrewardSet).comp
      (measurable_const.prodMk measurable_fst)
  change
    (∫⁻ x in actionSet ×ˢ stateSet, rewardValue x
      ∂(policy.actionKernel stage ⊗ₖ mdp.transition) state) = _
  rw [ProbabilityTheory.Kernel.setLIntegral_compProd _ _ state
    hrewardValue'
    hactionSet hstateSet]
  simp_rw [rewardValue, MeasureTheory.setLIntegral_const]
  rw [MeanCompatibleRewardKernel.actionRewardStateKernel,
    ProbabilityTheory.Kernel.compProd_apply_prod hactionSet
      (hrewardSet.prod hstateSet)]
  simp_rw [MeanCompatibleRewardKernel.rewardNextStateKernel,
    ProbabilityTheory.Kernel.prod_apply_prod]

/-- Assemble a reward-bearing head directly from a centered residual. -/
def assembleRewardDeviationAfterRetainedActionState (mdp : MDP State Action) :
    ((State × (Action × State)) × Real) ->
      Action × (Real × State) :=
  fun p => assembleRawRewardAfterRetainedActionState
    (p.1, uncenterRewardAfterRetainedActionState mdp p.1 p.2)

theorem measurable_assembleRewardDeviationAfterRetainedActionState
    (mdp : MDP State Action) :
    Measurable (assembleRewardDeviationAfterRetainedActionState mdp) := by
  exact measurable_assembleRawRewardAfterRetainedActionState.comp
    (measurable_fst.prodMk
      ((measurable_uncenterRewardAfterRetainedActionState mdp).comp
        (measurable_fst.prodMk measurable_snd)))

/-- The centered residual construction maps exactly to the existing head kernel. -/
theorem retainedActionStateKernel_compProd_rewardDeviation_map_assemble
    (source : MeanCompatibleRewardKernel mdp)
    (policy : MarkovPolicy mdp) (stage : Fin mdp.horizon) :
    ((policy.retainedActionStateKernel stage) ⊗ₖ
        source.rewardDeviationKernelAfterRetainedActionState).map
        (assembleRewardDeviationAfterRetainedActionState mdp) =
      source.actionRewardStateKernel policy stage := by
  let restore :
      ((State × (Action × State)) × Real) ->
        (State × (Action × State)) × Real :=
    fun p =>
      (p.1, uncenterRewardAfterRetainedActionState mdp p.1 p.2)
  have hrestore : Measurable restore :=
    measurable_fst.prodMk
      ((measurable_uncenterRewardAfterRetainedActionState mdp).comp
        (measurable_fst.prodMk measurable_snd))
  have hcomposition :
      assembleRewardDeviationAfterRetainedActionState mdp =
        assembleRawRewardAfterRetainedActionState ∘ restore := rfl
  rw [hcomposition]
  rw [ProbabilityTheory.Kernel.map_comp_right _ hrestore
    measurable_assembleRawRewardAfterRetainedActionState]
  rw [source.retainedActionStateKernel_compProd_rewardDeviation_map_uncenter
    policy stage]
  exact source.retainedActionStateKernel_compProd_rawReward_map_assemble
    policy stage

/-- Retaining the current state preserves the one-step Bellman innovation MGF. -/
theorem retainedActionStateKernel_meanBellmanInnovation_hasSubgaussianMGF
    (policy : MarkovPolicy mdp)
    (rewardBound : NNReal)
    (hrewardBound : forall state action,
      |mdp.reward state action| <= (rewardBound : Real))
    (remaining : Nat) (hremaining : remaining + 1 <= mdp.horizon)
    (state : State) :
    ProbabilityTheory.HasSubgaussianMGF
      (fun retained : State × (Action × State) =>
        mdp.reward retained.1 retained.2.1 +
          policy.valueRemaining remaining (by omega) retained.2.2 -
            policy.valueRemaining (remaining + 1) hremaining state)
      (meanBellmanInnovationStepVarianceProxy rewardBound (remaining + 1))
      (policy.retainedActionStateKernel
        ⟨mdp.horizon - (remaining + 1), by omega⟩ state) := by
  let stage : Fin mdp.horizon :=
    ⟨mdp.horizon - (remaining + 1), by omega⟩
  let X : Action × State -> Real := fun head =>
    mdp.reward state head.1 +
      policy.valueRemaining remaining (by omega) head.2 -
        policy.valueRemaining (remaining + 1) hremaining state
  let retainedX : State × (Action × State) -> Real := fun retained =>
    mdp.reward retained.1 retained.2.1 +
      policy.valueRemaining remaining (by omega) retained.2.2 -
        policy.valueRemaining (remaining + 1) hremaining state
  have hX : Measurable X :=
    ((mdp.measurable_reward.comp
      (measurable_const.prodMk measurable_fst)).add
      ((policy.measurable_valueRemaining remaining (by omega)).comp
        measurable_snd)).sub measurable_const
  have hretainedX : Measurable retainedX :=
    ((mdp.measurable_reward.comp
      (measurable_fst.prodMk measurable_snd.fst)).add
      ((policy.measurable_valueRemaining remaining (by omega)).comp
        measurable_snd.snd)).sub measurable_const
  have hretainedLaw :
      policy.retainedActionStateKernel stage state =
        (policy.actionStateKernel stage state).map (Prod.mk state) := by
    rw [MarkovPolicy.retainedActionStateKernel,
      ProbabilityTheory.Kernel.prod_apply,
      ProbabilityTheory.Kernel.id_apply, Measure.dirac_prod]
  have hbase := actionStateKernel_meanBellmanInnovation_hasSubgaussianMGF
    policy rewardBound hrewardBound remaining hremaining state
  apply hbase.congr_identDistrib
  refine
    { aemeasurable_fst := hX.aemeasurable
      aemeasurable_snd := hretainedX.aemeasurable
      map_eq := ?_ }
  rw [hretainedLaw]
  change Measure.map X (policy.actionStateKernel stage state) =
    Measure.map retainedX
      (Measure.map (Prod.mk state) (policy.actionStateKernel stage state))
  have hembed : Measurable
      (Prod.mk state : Action × State -> State × (Action × State)) :=
    measurable_const.prodMk measurable_id
  rw [Measure.map_map hretainedX hembed]
  rfl

/--
One sampled reward plus the sampled next policy value is sub-Gaussian around
the current policy value with the sum of reward and Bellman innovation proxies.
-/
theorem actionRewardStateKernel_sampledReturnBellmanInnovation_hasSubgaussianMGF
    [StandardBorelSpace State] [StandardBorelSpace Action]
    [Nonempty Action]
    (source : MeanCompatibleRewardKernel mdp)
    (policy : MarkovPolicy mdp)
    (rewardBound rewardVarianceProxy : NNReal)
    (hrewardBound : forall state action,
      |mdp.reward state action| <= (rewardBound : Real))
    (law : source.UniformSubgaussianRewardLaw rewardVarianceProxy)
    (remaining : Nat) (hremaining : remaining + 1 <= mdp.horizon)
    (state : State) :
    ProbabilityTheory.HasSubgaussianMGF
      (fun head : Action × (Real × State) =>
        head.2.1 + policy.valueRemaining remaining (by omega) head.2.2 -
          policy.valueRemaining (remaining + 1) hremaining state)
      (meanBellmanInnovationStepVarianceProxy rewardBound (remaining + 1) +
        rewardVarianceProxy)
      (source.actionRewardStateKernel policy
        ⟨mdp.horizon - (remaining + 1), by omega⟩ state) := by
  let stage : Fin mdp.horizon :=
    ⟨mdp.horizon - (remaining + 1), by omega⟩
  let retainedKernel : ProbabilityTheory.Kernel State
      (State × (Action × State)) :=
    policy.retainedActionStateKernel stage
  let residualKernel : ProbabilityTheory.Kernel
      (State × (State × (Action × State))) Real :=
    source.rewardDeviationKernelAfterRetainedActionState
  let X : State × (Action × State) -> Real := fun retained =>
    mdp.reward retained.1 retained.2.1 +
      policy.valueRemaining remaining (by omega) retained.2.2 -
        policy.valueRemaining (remaining + 1) hremaining state
  let Z : (State × (Action × State)) × Real -> Real :=
    fun p => X p.1 + p.2
  let headZ : Action × (Real × State) -> Real := fun head =>
    head.2.1 + policy.valueRemaining remaining (by omega) head.2.2 -
      policy.valueRemaining (remaining + 1) hremaining state
  have hX : Measurable X :=
    ((mdp.measurable_reward.comp
      (measurable_fst.prodMk measurable_snd.fst)).add
      ((policy.measurable_valueRemaining remaining (by omega)).comp
        measurable_snd.snd)).sub measurable_const
  have hZ : Measurable Z := hX.comp measurable_fst |>.add measurable_snd
  have hheadZ : Measurable headZ :=
    (measurable_snd.fst.add
      ((policy.measurable_valueRemaining remaining (by omega)).comp
        measurable_snd.snd)).sub measurable_const
  have hXkernel : ProbabilityTheory.Kernel.HasSubgaussianMGF
      X (meanBellmanInnovationStepVarianceProxy rewardBound (remaining + 1))
      retainedKernel (Measure.dirac state) := by
    apply Concentration.kernel_hasSubgaussianMGF_of_ae
      (Measure.dirac state) retainedKernel X
      (meanBellmanInnovationStepVarianceProxy rewardBound (remaining + 1)) hX
    rw [ae_dirac_eq]
    simpa [X, retainedKernel, stage] using
      retainedActionStateKernel_meanBellmanInnovation_hasSubgaussianMGF
        policy rewardBound hrewardBound remaining hremaining state
  have hResidual : ProbabilityTheory.Kernel.HasSubgaussianMGF
      id rewardVarianceProxy source.rewardDeviationKernelAfterActionState
      (retainedKernel ∘ₘ Measure.dirac state) :=
    source.rewardDeviationKernelAfterActionState_hasSubgaussianMGF
      rewardVarianceProxy law (retainedKernel ∘ₘ Measure.dirac state)
  have hYkernel : ProbabilityTheory.Kernel.HasSubgaussianMGF
      id rewardVarianceProxy residualKernel
      (Measure.dirac state ⊗ₘ retainedKernel) := by
    simpa [residualKernel] using hResidual.prodMkLeft_compProd
  have hsumKernel := hXkernel.add_compProd hYkernel
  have hsum : ProbabilityTheory.HasSubgaussianMGF
      Z
      (meanBellmanInnovationStepVarianceProxy rewardBound (remaining + 1) +
        rewardVarianceProxy)
      ((retainedKernel ⊗ₖ residualKernel) state) := by
    simpa [Z] using
      (Concentration.hasSubgaussianMGF_apply_of_kernel_dirac
        (retainedKernel ⊗ₖ residualKernel) state
        (fun p => X p.1 + id p.2)
        (meanBellmanInnovationStepVarianceProxy rewardBound (remaining + 1) +
          rewardVarianceProxy) hsumKernel)
  apply hsum.congr_identDistrib
  refine
    { aemeasurable_fst := hZ.aemeasurable
      aemeasurable_snd := hheadZ.aemeasurable
      map_eq := ?_ }
  change Measure.map Z ((retainedKernel ⊗ₖ residualKernel) state) =
    Measure.map headZ (source.actionRewardStateKernel policy stage state)
  have hheadLaw := congrArg (fun kernel => kernel state)
    (source.retainedActionStateKernel_compProd_rewardDeviation_map_assemble
      policy stage)
  change
    ((retainedKernel ⊗ₖ residualKernel).map
      (assembleRewardDeviationAfterRetainedActionState mdp)) state =
      source.actionRewardStateKernel policy stage state at hheadLaw
  rw [ProbabilityTheory.Kernel.map_apply _
    (measurable_assembleRewardDeviationAfterRetainedActionState mdp)] at hheadLaw
  rw [← hheadLaw]
  rw [Measure.map_map hheadZ
    (measurable_assembleRewardDeviationAfterRetainedActionState mdp)]
  have hpoint : Z = headZ ∘
      assembleRewardDeviationAfterRetainedActionState mdp := by
    funext p
    simp [Z, X, headZ, assembleRewardDeviationAfterRetainedActionState,
      assembleRawRewardAfterRetainedActionState,
      uncenterRewardAfterRetainedActionState]
    ring
  rw [hpoint]

/--
The full sampled return is sub-Gaussian around the recursive policy value, with
the reward-noise proxy plus the mean Bellman innovation proxy.
-/
theorem stochasticTrajectoryKernelRemaining_sampledCumulativeReturnDeviationFrom_hasSubgaussianMGF
    [StandardBorelSpace State] [StandardBorelSpace Action]
    [Nonempty Action]
    (source : MeanCompatibleRewardKernel mdp)
    (policy : MarkovPolicy mdp)
    (rewardBound rewardVarianceProxy : NNReal)
    (hrewardBound : forall state action,
      |mdp.reward state action| <= (rewardBound : Real))
    (law : source.UniformSubgaussianRewardLaw rewardVarianceProxy)
    (remaining : Nat) (hremaining : remaining <= mdp.horizon)
    (state : State) :
    ProbabilityTheory.HasSubgaussianMGF
      (mdp.sampledCumulativeReturnDeviationFrom policy remaining
        hremaining state)
      ((remaining : NNReal) * rewardVarianceProxy +
        meanBellmanInnovationVarianceProxy rewardBound remaining)
      (source.stochasticTrajectoryKernelRemaining policy
        remaining hremaining state) := by
  induction remaining generalizing state with
  | zero =>
      have hfun :
          mdp.sampledCumulativeReturnDeviationFrom policy 0 hremaining state =
            (fun _ : RewardStepTrace Action State 0 => 0) := by
        funext trace
        simp [MDP.sampledCumulativeReturnDeviationFrom,
          MDP.sampledCumulativeRewardFrom, MarkovPolicy.valueRemaining]
      have hproxy :
          (((0 : Nat) : NNReal) * rewardVarianceProxy +
            meanBellmanInnovationVarianceProxy rewardBound 0) = 0 := by
        simp [meanBellmanInnovationVarianceProxy]
      rw [hfun, hproxy]
      exact ProbabilityTheory.HasSubgaussianMGF.fun_zero
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
            RewardStepTrace Action State remaining) ->
            State × RewardStepTrace Action State remaining :=
        fun p => (p.1.2.2.2, p.2)
      have hretainNext : Measurable retainNext :=
        measurable_fst.snd.snd.snd.prodMk measurable_snd
      let tailStateKernel : ProbabilityTheory.Kernel
          (State × (Action × (Real × State)))
          (State × RewardStepTrace Action State remaining) :=
        (ProbabilityTheory.Kernel.id ×ₖ tailKernel).map retainNext
      let X : Action × (Real × State) -> Real := fun head =>
        head.2.1 + policy.valueRemaining remaining (by omega) head.2.2 -
          policy.valueRemaining (remaining + 1) hremaining state
      have hX : Measurable X :=
        (measurable_snd.fst.add
          ((policy.measurable_valueRemaining remaining (by omega)).comp
            measurable_snd.snd)).sub measurable_const
      let Y : State × RewardStepTrace Action State remaining -> Real :=
        fun p => mdp.sampledCumulativeReturnDeviationFrom policy
          remaining (by omega) p.1 p.2
      have hY : Measurable Y :=
        mdp.measurable_sampledCumulativeReturnDeviationFrom
          policy remaining (by omega)
      have hXkernel : ProbabilityTheory.Kernel.HasSubgaussianMGF
          X
          (meanBellmanInnovationStepVarianceProxy rewardBound (remaining + 1) +
            rewardVarianceProxy)
          headKernel (Measure.dirac state) := by
        apply Concentration.kernel_hasSubgaussianMGF_of_ae
          (Measure.dirac state) headKernel X
          (meanBellmanInnovationStepVarianceProxy rewardBound (remaining + 1) +
            rewardVarianceProxy) hX
        rw [ae_dirac_eq]
        simpa [X, headKernel, stage] using
          source.actionRewardStateKernel_sampledReturnBellmanInnovation_hasSubgaussianMGF
            policy rewardBound rewardVarianceProxy hrewardBound law
            remaining hremaining state
      have hYkernel : ProbabilityTheory.Kernel.HasSubgaussianMGF
          Y
          ((remaining : NNReal) * rewardVarianceProxy +
            meanBellmanInnovationVarianceProxy rewardBound remaining)
          tailStateKernel (Measure.dirac state ⊗ₘ headKernel) := by
        apply Concentration.kernel_hasSubgaussianMGF_of_ae
          (Measure.dirac state ⊗ₘ headKernel) tailStateKernel Y
          ((remaining : NNReal) * rewardVarianceProxy +
            meanBellmanInnovationVarianceProxy rewardBound remaining) hY
        exact Filter.Eventually.of_forall fun input => by
          let nextState : State := input.2.2.2
          have htail := ih (by omega) nextState
          have htailMeas : Measurable
              (mdp.sampledCumulativeReturnDeviationFrom policy remaining
                (by omega) nextState) :=
            (mdp.measurable_sampledCumulativeReturnDeviationFrom
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
          let embed : RewardStepTrace Action State remaining ->
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
          ((meanBellmanInnovationStepVarianceProxy rewardBound (remaining + 1) +
              rewardVarianceProxy) +
            ((remaining : NNReal) * rewardVarianceProxy +
              meanBellmanInnovationVarianceProxy rewardBound remaining))
          ((headKernel ⊗ₖ tailStateKernel) state) :=
        Concentration.hasSubgaussianMGF_apply_of_kernel_dirac
          (headKernel ⊗ₖ tailStateKernel) state
          (fun p => X p.1 + Y p.2)
          ((meanBellmanInnovationStepVarianceProxy rewardBound (remaining + 1) +
              rewardVarianceProxy) +
            ((remaining : NNReal) * rewardVarianceProxy +
              meanBellmanInnovationVarianceProxy rewardBound remaining))
          hcombinedKernel
      let assemble :
          (Action × (Real × State)) ×
              (State × RewardStepTrace Action State remaining) ->
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
          ∀ᵐ p ∂((headKernel ⊗ₖ tailStateKernel) state),
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
        let embed : RewardStepTrace Action State remaining ->
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
          (mdp.sampledCumulativeReturnDeviationFrom policy
            (remaining + 1) hremaining state)
          ((headKernel ⊗ₖ tailStateKernel) state)
          (source.stochasticTrajectoryKernelRemaining policy
            (remaining + 1) hremaining state) := by
        refine
          { aemeasurable_fst := (hX.comp measurable_fst).add
              (hY.comp measurable_snd) |>.aemeasurable
            aemeasurable_snd :=
              (mdp.measurable_sampledCumulativeReturnDeviationFrom
                policy (remaining + 1) hremaining).comp
                (measurable_const.prodMk measurable_id) |>.aemeasurable
            map_eq := ?_ }
        have hfinal : Measurable
            (mdp.sampledCumulativeReturnDeviationFrom policy
              (remaining + 1) hremaining state) :=
          (mdp.measurable_sampledCumulativeReturnDeviationFrom
            policy (remaining + 1) hremaining).comp
            (measurable_const.prodMk measurable_id)
        have hfunction :
            (fun p => X p.1 + Y p.2) =ᵐ[
              (headKernel ⊗ₖ tailStateKernel) state]
              (mdp.sampledCumulativeReturnDeviationFrom policy
                (remaining + 1) hremaining state) ∘ assemble := by
          filter_upwards [hstateAgree] with p hp
          simp [X, Y, assemble,
            MDP.sampledCumulativeReturnDeviationFrom,
            MDP.sampledCumulativeRewardFrom, hp]
          ring
        rw [Measure.map_congr hfunction]
        calc
          _ = Measure.map
              (mdp.sampledCumulativeReturnDeviationFrom policy
                (remaining + 1) hremaining state)
              (((headKernel ⊗ₖ tailStateKernel) state).map assemble) := by
                rw [Measure.map_map hfinal hassemble]
          _ = _ := by rw [hgenerated]
      have htarget := hcombined.congr_identDistrib hident
      simpa [meanBellmanInnovationVarianceProxy_succ, Nat.cast_succ,
        add_mul, add_comm, add_left_comm, add_assoc] using htarget

/-- Fixed-horizon two-sided delta tail for sampled return around policy value. -/
theorem stochasticTrajectoryKernelRemaining_sampledCumulativeReturnDeviationFrom_abs_tail_le
    [StandardBorelSpace State] [StandardBorelSpace Action]
    [Nonempty Action]
    (source : MeanCompatibleRewardKernel mdp)
    (policy : MarkovPolicy mdp)
    (rewardBound rewardVarianceProxy : NNReal)
    (hrewardBound : forall state action,
      |mdp.reward state action| <= (rewardBound : Real))
    (law : source.UniformSubgaussianRewardLaw rewardVarianceProxy)
    (remaining : Nat) (hremaining : remaining <= mdp.horizon)
    (state : State)
    (htotal : 0 <
      ((((remaining : NNReal) * rewardVarianceProxy +
        meanBellmanInnovationVarianceProxy rewardBound remaining : NNReal) : Real)))
    (delta : Real) (hdelta : 0 < delta) (hdelta_le_one : delta <= 1) :
    (source.stochasticTrajectoryKernelRemaining policy remaining hremaining state)
      {trace |
        Concentration.subGaussianSumConfidenceRadius
            ((remaining : NNReal) * rewardVarianceProxy +
              meanBellmanInnovationVarianceProxy rewardBound remaining) delta <=
          |mdp.sampledCumulativeReturnDeviationFrom policy remaining
            hremaining state trace|} <=
      ENNReal.ofReal delta := by
  let mu := source.stochasticTrajectoryKernelRemaining policy
    remaining hremaining state
  let F : Filtration Nat
      (inferInstance : MeasurableSpace (RewardStepTrace Action State remaining)) :=
    Filtration.const Nat inferInstance le_rfl
  let Y : Nat -> RewardStepTrace Action State remaining -> Real :=
    fun _ => mdp.sampledCumulativeReturnDeviationFrom policy
      remaining hremaining state
  let cY : Nat -> NNReal := fun _ =>
    (remaining : NNReal) * rewardVarianceProxy +
      meanBellmanInnovationVarianceProxy rewardBound remaining
  have hstateMeas : Measurable
      (mdp.sampledCumulativeReturnDeviationFrom policy remaining
        hremaining state) :=
    (mdp.measurable_sampledCumulativeReturnDeviationFrom
      policy remaining hremaining).comp
      (measurable_const.prodMk measurable_id)
  have hadapted : StronglyAdapted F Y := by
    intro i
    simpa [F, Y] using hstateMeas.stronglyMeasurable
  have hzero : ProbabilityTheory.HasSubgaussianMGF (Y 0) (cY 0) mu := by
    simpa [Y, cY, mu] using
      source.stochasticTrajectoryKernelRemaining_sampledCumulativeReturnDeviationFrom_hasSubgaussianMGF
        policy rewardBound rewardVarianceProxy hrewardBound law
        remaining hremaining state
  have hsucc : forall i, i < 1 - 1 ->
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

end MeanCompatibleRewardKernel

end MDP
end FiniteHorizonRL
end BanditRLProof
