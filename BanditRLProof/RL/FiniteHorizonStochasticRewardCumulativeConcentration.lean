import BanditRLProof.RL.FiniteHorizonStochasticRewardConcentration
import Mathlib.Probability.Kernel.Composition.Prod

/-!
# Finite-horizon stochastic reward cumulative concentration

This module centers every sampled reward at the mean of its actual pre-step
state and sampled action.  A recursive kernel composition proof combines the
common one-step sub-Gaussian proxy additively, yielding a total proxy linear in
the remaining horizon and a fixed-horizon two-sided delta tail.
-/

open MeasureTheory
open scoped ProbabilityTheory

universe u v

namespace BanditRLProof
namespace Concentration

theorem kernel_hasSubgaussianMGF_of_ae
    {Alpha : Type u} {Omega : Type v}
    [MeasurableSpace Alpha] [MeasurableSpace Omega]
    (mu : Measure Alpha) [IsFiniteMeasure mu]
    (kernel : ProbabilityTheory.Kernel Alpha Omega)
    (X : Omega -> Real) (varianceProxy : NNReal)
    (hX : Measurable X)
    (hfiber : ∀ᵐ alpha ∂mu,
      ProbabilityTheory.HasSubgaussianMGF X varianceProxy (kernel alpha)) :
    ProbabilityTheory.Kernel.HasSubgaussianMGF X varianceProxy kernel mu := by
  have hintegrable : forall t : Real,
      Integrable (fun omega => Real.exp (t * X omega)) (kernel ∘ₘ mu) := by
    intro t
    let f : Omega -> Real := fun omega => Real.exp (t * X omega)
    have hf : Measurable f :=
      Real.measurable_exp.comp (measurable_const.mul hX)
    refine (Measure.integrable_comp_iff hf.aestronglyMeasurable).2 ⟨?_, ?_⟩
    · filter_upwards [hfiber] with alpha hsub
      simpa [f] using hsub.integrable_exp_mul t
    · have hinner : StronglyMeasurable
          (fun alpha => ∫ omega, ‖f omega‖ ∂kernel alpha) :=
        (hf.stronglyMeasurable.norm.integral_kernel)
      refine Integrable.of_bound hinner.aestronglyMeasurable
        (Real.exp (((varianceProxy : NNReal) : Real) * t ^ 2 / 2)) ?_
      filter_upwards [hfiber] with alpha hsub
      have heq :
          (∫ omega, ‖f omega‖ ∂kernel alpha) =
            ProbabilityTheory.mgf X (kernel alpha) t := by
        simp [f, ProbabilityTheory.mgf, Real.norm_eq_abs]
      rw [heq, Real.norm_of_nonneg ProbabilityTheory.mgf_nonneg]
      exact hsub.mgf_le t
  refine ProbabilityTheory.Kernel.HasSubgaussianMGF.of_rat hintegrable ?_
  intro q
  filter_upwards [hfiber] with alpha hsub
  simpa using hsub.mgf_le (q : Real)

theorem hasSubgaussianMGF_apply_of_kernel_dirac
    {Alpha : Type u} {Omega : Type v}
    [MeasurableSpace Alpha] [MeasurableSpace Omega]
    [MeasurableSingletonClass Alpha]
    (kernel : ProbabilityTheory.Kernel Alpha Omega)
    (alpha : Alpha) (X : Omega -> Real) (varianceProxy : NNReal)
    (hkernel : ProbabilityTheory.Kernel.HasSubgaussianMGF
      X varianceProxy kernel (Measure.dirac alpha)) :
    ProbabilityTheory.HasSubgaussianMGF X varianceProxy (kernel alpha) := by
  constructor
  · intro t
    have hfiber := Measure.ae_integrable_of_integrable_comp
      (hkernel.integrable_exp_mul t)
    simpa only [ae_dirac_eq, Filter.eventually_pure] using hfiber
  · intro t
    have hpointwise : forall s : Real,
        ProbabilityTheory.mgf X (kernel alpha) s <=
          Real.exp ((varianceProxy : Real) * s ^ 2 / 2) := by
      simpa only [ae_dirac_eq, Filter.eventually_pure] using hkernel.mgf_le
    exact hpointwise t

end Concentration

namespace FiniteHorizonRL

variable {State : Type u} {Action : Type v}
    [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action]

namespace MDP

def sampledCumulativeRewardDeviationFrom (mdp : MDP State Action) :
    (remaining : Nat) -> State -> RewardStepTrace Action State remaining -> Real
  | 0, _, _ => 0
  | remaining + 1, state, trace =>
      (trace 0).2.1 - mdp.reward state (trace 0).1 +
        sampledCumulativeRewardDeviationFrom mdp remaining
          (trace 0).2.2 (Fin.tail trace)

theorem measurable_sampledCumulativeRewardDeviationFrom (mdp : MDP State Action)
    (remaining : Nat) :
    Measurable (fun p : State × RewardStepTrace Action State remaining =>
      mdp.sampledCumulativeRewardDeviationFrom remaining p.1 p.2) := by
  induction remaining with
  | zero =>
      simp [sampledCumulativeRewardDeviationFrom]
  | succ remaining ih =>
      let head : State × RewardStepTrace Action State (remaining + 1) ->
          Action × (Real × State) := fun p => p.2 0
      have hhead : Measurable head := (measurable_pi_apply 0).comp measurable_snd
      have htail : Measurable
          (fun p : State × RewardStepTrace Action State (remaining + 1) =>
            ((head p).2.2, Fin.tail p.2)) :=
        hhead.snd.snd.prodMk
          ((RewardStepTrace.measurable_tail remaining).comp measurable_snd)
      simpa only [sampledCumulativeRewardDeviationFrom] using
        (hhead.snd.fst.sub
          (mdp.measurable_reward.comp (measurable_fst.prodMk hhead.fst))).add
            (ih.comp htail)

end MDP

namespace MDP.MeanCompatibleRewardKernel

variable {mdp : MDP State Action}

theorem actionRewardStateKernel_rewardDeviation_hasSubgaussianMGF
    [StandardBorelSpace State] [StandardBorelSpace Action]
    [Nonempty Action]
    (source : MeanCompatibleRewardKernel mdp)
    (policy : MarkovPolicy mdp)
    (remaining : Nat) (hremaining : remaining + 1 <= mdp.horizon)
    (state : State) (varianceProxy : NNReal)
    (law : source.UniformSubgaussianRewardLaw varianceProxy) :
    ProbabilityTheory.HasSubgaussianMGF
      (fun head : Action × (Real × State) =>
        head.2.1 - mdp.reward state head.1)
      varianceProxy
      (source.actionRewardStateKernel policy
        ⟨mdp.horizon - (remaining + 1), by omega⟩ state) := by
  let headDeviation : Action × (Real × State) -> Real :=
    fun head => head.2.1 - mdp.reward state head.1
  have hheadDeviation : Measurable headDeviation :=
    measurable_snd.fst.sub
      (mdp.measurable_reward.comp (measurable_const.prodMk measurable_fst))
  have hfull :=
    source.stochasticTrajectoryKernelRemaining_headRewardDeviation_hasSubgaussianMGF
      policy remaining hremaining state varianceProxy law
  apply hfull.congr_identDistrib
  refine
    { aemeasurable_fst :=
        (mdp.measurable_headRewardDeviation state remaining).aemeasurable
      aemeasurable_snd := hheadDeviation.aemeasurable
      map_eq := ?_ }
  change Measure.map
      (headDeviation ∘ RewardStepTrace.head
        (Action := Action) (State := State) remaining)
      (source.stochasticTrajectoryKernelRemaining policy
        (remaining + 1) hremaining state) = _
  rw [← Measure.map_map hheadDeviation
    (RewardStepTrace.measurable_head remaining)]
  rw [source.stochasticTrajectoryKernelRemaining_map_head
    policy remaining hremaining state]

theorem stochasticTrajectoryKernelRemaining_sampledCumulativeRewardDeviationFrom_hasSubgaussianMGF
    [StandardBorelSpace State] [StandardBorelSpace Action]
    [Nonempty Action]
    (source : MeanCompatibleRewardKernel mdp)
    (policy : MarkovPolicy mdp)
    (remaining : Nat) (hremaining : remaining <= mdp.horizon)
    (state : State) (varianceProxy : NNReal)
    (law : source.UniformSubgaussianRewardLaw varianceProxy) :
    ProbabilityTheory.HasSubgaussianMGF
      (mdp.sampledCumulativeRewardDeviationFrom remaining state)
      ((remaining : NNReal) * varianceProxy)
      (source.stochasticTrajectoryKernelRemaining policy
        remaining hremaining state) := by
  induction remaining generalizing state with
  | zero =>
      simpa [MDP.sampledCumulativeRewardDeviationFrom] using
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
            RewardStepTrace Action State remaining) ->
            State × RewardStepTrace Action State remaining :=
        fun p => (p.1.2.2.2, p.2)
      have hretainNext : Measurable retainNext :=
        measurable_fst.snd.snd.snd.prodMk measurable_snd
      let tailStateKernel : ProbabilityTheory.Kernel
          (State × (Action × (Real × State)))
          (State × RewardStepTrace Action State remaining) :=
        (ProbabilityTheory.Kernel.id ×ₖ tailKernel).map retainNext
      let X : Action × (Real × State) -> Real :=
        fun head => head.2.1 - mdp.reward state head.1
      have hX : Measurable X :=
        measurable_snd.fst.sub
          (mdp.measurable_reward.comp (measurable_const.prodMk measurable_fst))
      let Y : State × RewardStepTrace Action State remaining -> Real :=
        fun p => mdp.sampledCumulativeRewardDeviationFrom remaining p.1 p.2
      have hY : Measurable Y :=
        mdp.measurable_sampledCumulativeRewardDeviationFrom remaining
      have hXkernel : ProbabilityTheory.Kernel.HasSubgaussianMGF
          X varianceProxy headKernel (Measure.dirac state) := by
        apply Concentration.kernel_hasSubgaussianMGF_of_ae
          (Measure.dirac state) headKernel X varianceProxy hX
        rw [ae_dirac_eq]
        simpa [X, headKernel, stage] using
          source.actionRewardStateKernel_rewardDeviation_hasSubgaussianMGF
            policy remaining hremaining state varianceProxy law
      have hYkernel : ProbabilityTheory.Kernel.HasSubgaussianMGF
          Y ((remaining : NNReal) * varianceProxy) tailStateKernel
          (Measure.dirac state ⊗ₘ headKernel) := by
        apply Concentration.kernel_hasSubgaussianMGF_of_ae
          (Measure.dirac state ⊗ₘ headKernel) tailStateKernel Y
          ((remaining : NNReal) * varianceProxy) hY
        exact Filter.Eventually.of_forall fun input => by
          let nextState : State := input.2.2.2
          have htail := ih (by omega) nextState
          have htailMeas : Measurable
              (mdp.sampledCumulativeRewardDeviationFrom remaining nextState) :=
            (mdp.measurable_sampledCumulativeRewardDeviationFrom remaining).comp
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
          (varianceProxy + (remaining : NNReal) * varianceProxy)
          ((headKernel ⊗ₖ tailStateKernel) state) :=
        Concentration.hasSubgaussianMGF_apply_of_kernel_dirac
          (headKernel ⊗ₖ tailStateKernel) state
          (fun p => X p.1 + Y p.2)
          (varianceProxy + (remaining : NNReal) * varianceProxy)
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
      have hident : ProbabilityTheory.IdentDistrib
          (fun p => X p.1 + Y p.2)
          (mdp.sampledCumulativeRewardDeviationFrom (remaining + 1) state)
          ((headKernel ⊗ₖ tailStateKernel) state)
          (source.stochasticTrajectoryKernelRemaining policy
            (remaining + 1) hremaining state) := by
        refine
          { aemeasurable_fst := (hX.comp measurable_fst).add
              (hY.comp measurable_snd) |>.aemeasurable
            aemeasurable_snd :=
              (mdp.measurable_sampledCumulativeRewardDeviationFrom
                (remaining + 1)).comp
                (measurable_const.prodMk measurable_id) |>.aemeasurable
            map_eq := ?_ }
        have hfinal : Measurable
            (mdp.sampledCumulativeRewardDeviationFrom
              (remaining + 1) state) :=
          (mdp.measurable_sampledCumulativeRewardDeviationFrom
            (remaining + 1)).comp (measurable_const.prodMk measurable_id)
        change Measure.map
          ((mdp.sampledCumulativeRewardDeviationFrom
            (remaining + 1) state) ∘ assemble)
          ((headKernel ⊗ₖ tailStateKernel) state) = _
        calc
          _ = Measure.map
              (mdp.sampledCumulativeRewardDeviationFrom
                (remaining + 1) state)
              (((headKernel ⊗ₖ tailStateKernel) state).map assemble) := by
                rw [Measure.map_map hfinal hassemble]
          _ = _ := by rw [hgenerated]
      have htarget := hcombined.congr_identDistrib hident
      simpa [Nat.cast_succ, add_mul, add_comm, add_left_comm, add_assoc] using htarget

theorem stochasticTrajectoryKernelRemaining_sampledCumulativeRewardDeviationFrom_abs_tail_le
    [StandardBorelSpace State] [StandardBorelSpace Action]
    [Nonempty Action]
    (source : MeanCompatibleRewardKernel mdp)
    (policy : MarkovPolicy mdp)
    (remaining : Nat) (hremaining : remaining <= mdp.horizon)
    (state : State) (varianceProxy : NNReal)
    (law : source.UniformSubgaussianRewardLaw varianceProxy)
    (htotal : 0 < ((((remaining : NNReal) * varianceProxy : NNReal) : Real)))
    (delta : Real) (hdelta : 0 < delta) (hdelta_le_one : delta <= 1) :
    (source.stochasticTrajectoryKernelRemaining policy remaining hremaining state)
      {trace |
        Concentration.subGaussianSumConfidenceRadius
            ((remaining : NNReal) * varianceProxy) delta <=
          |mdp.sampledCumulativeRewardDeviationFrom remaining state trace|} <=
      ENNReal.ofReal delta := by
  let mu := source.stochasticTrajectoryKernelRemaining policy
    remaining hremaining state
  let F : Filtration Nat
      (inferInstance : MeasurableSpace (RewardStepTrace Action State remaining)) :=
    Filtration.const Nat inferInstance le_rfl
  let Y : Nat -> RewardStepTrace Action State remaining -> Real :=
    fun _ => mdp.sampledCumulativeRewardDeviationFrom remaining state
  let cY : Nat -> NNReal := fun _ => (remaining : NNReal) * varianceProxy
  have hstateMeas : Measurable
      (mdp.sampledCumulativeRewardDeviationFrom remaining state) :=
    (mdp.measurable_sampledCumulativeRewardDeviationFrom remaining).comp
      (measurable_const.prodMk measurable_id)
  have hadapted : StronglyAdapted F Y := by
    intro i
    simpa [F, Y] using hstateMeas.stronglyMeasurable
  have hzero : ProbabilityTheory.HasSubgaussianMGF (Y 0) (cY 0) mu := by
    simpa [Y, cY, mu] using
      source.stochasticTrajectoryKernelRemaining_sampledCumulativeRewardDeviationFrom_hasSubgaussianMGF
        policy remaining hremaining state varianceProxy law
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

end MDP.MeanCompatibleRewardKernel
end FiniteHorizonRL
end BanditRLProof
