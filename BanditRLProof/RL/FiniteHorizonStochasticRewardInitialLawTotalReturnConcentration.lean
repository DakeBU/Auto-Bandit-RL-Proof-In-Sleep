import BanditRLProof.RL.FiniteHorizonStochasticRewardTotalReturnConcentration

/-!
# Initial-law finite-horizon sampled-return concentration

This module lifts the statewise sampled-return concentration theorem to the
full stochastic trajectory measure generated from a finite initial-state law.
The random variable remains centered by the recursive value of its own initial
state; no concentration claim is made for mixing those state-dependent values.
-/

open MeasureTheory
open scoped ProbabilityTheory BigOperators

universe u v

namespace BanditRLProof

namespace Concentration

/--
A common sub-Gaussian proxy on every fiber of a Markov kernel is preserved by
mixing the fibers with a probability measure on a finite index type.
-/
theorem hasSubgaussianMGF_compProd_of_forall_fintype
    {Index Omega : Type*}
    [MeasurableSpace Index] [MeasurableSpace Omega] [Fintype Index]
    (mu : Measure Index) [IsProbabilityMeasure mu]
    (kappa : ProbabilityTheory.Kernel Index Omega)
    [ProbabilityTheory.IsMarkovKernel kappa]
    (X : Index × Omega -> Real) (hX : Measurable X) (c : NNReal)
    (hfiber : forall index,
      ProbabilityTheory.HasSubgaussianMGF
        (fun omega => X (index, omega)) c (kappa index)) :
    ProbabilityTheory.HasSubgaussianMGF X c (mu.compProd kappa) := by
  constructor
  · intro t
    have hfullMeas : Measurable (fun p => Real.exp (t * X p)) :=
      Real.measurable_exp.comp (measurable_const.mul hX)
    have hfullAE : AEStronglyMeasurable
        (fun p => Real.exp (t * X p)) (mu.compProd kappa) :=
      hfullMeas.aestronglyMeasurable
    apply (Measure.integrable_compProd_iff hfullAE).2
    constructor
    · exact Filter.Eventually.of_forall fun index =>
        (hfiber index).integrable_exp_mul t
    · exact FiniteHorizonRL.integrable_of_fintype_aestronglyMeasurable mu _
        hfullAE.norm.integral_kernel_compProd
  · intro t
    have hfullMeas : Measurable (fun p => Real.exp (t * X p)) :=
      Real.measurable_exp.comp (measurable_const.mul hX)
    have hfullAE : AEStronglyMeasurable
        (fun p => Real.exp (t * X p)) (mu.compProd kappa) :=
      hfullMeas.aestronglyMeasurable
    have hfullInt : Integrable (fun p => Real.exp (t * X p))
        (mu.compProd kappa) := by
      apply (Measure.integrable_compProd_iff hfullAE).2
      constructor
      · exact Filter.Eventually.of_forall fun index =>
          (hfiber index).integrable_exp_mul t
      · exact FiniteHorizonRL.integrable_of_fintype_aestronglyMeasurable mu _
          hfullAE.norm.integral_kernel_compProd
    have hinnerAE : AEStronglyMeasurable
        (fun index => integral (kappa index)
          (fun omega => Real.exp (t * X (index, omega)))) mu :=
      hfullAE.integral_kernel_compProd
    have hinnerInt : Integrable
        (fun index => integral (kappa index)
          (fun omega => Real.exp (t * X (index, omega)))) mu :=
      FiniteHorizonRL.integrable_of_fintype_aestronglyMeasurable mu _ hinnerAE
    rw [ProbabilityTheory.mgf, Measure.integral_compProd hfullInt]
    have hmono := integral_mono_ae hinnerInt (integrable_const _)
      (Filter.Eventually.of_forall fun index => by
        simpa [ProbabilityTheory.mgf] using (hfiber index).mgf_le t)
    simpa using hmono

end Concentration

namespace FiniteHorizonRL

variable {State : Type u} {Action : Type v}
    [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action]

namespace MDP

/--
Sampled cumulative return centered by the policy value at the trajectory's own
initial state.
-/
noncomputable def sampledCumulativeReturnDeviation
    (mdp : MDP State Action) (policy : MarkovPolicy mdp)
    (trajectory : State × RewardStepTrace Action State mdp.horizon) : Real :=
  mdp.sampledCumulativeReturnDeviationFrom policy mdp.horizon le_rfl
    trajectory.1 trajectory.2

/-- The full initial-state-dependent sampled-return deviation is measurable. -/
theorem measurable_sampledCumulativeReturnDeviation
    (mdp : MDP State Action) (policy : MarkovPolicy mdp) :
    Measurable (mdp.sampledCumulativeReturnDeviation policy) := by
  exact mdp.measurable_sampledCumulativeReturnDeviationFrom
    policy mdp.horizon le_rfl

namespace MeanCompatibleRewardKernel

variable {mdp : MDP State Action}

/--
Initial-law sampled-return MGF bound. The centering is state dependent, so the
common statewise proxy passes unchanged through the finite initial-state mix.
-/
theorem stochasticTrajectoryMeasure_sampledCumulativeReturnDeviation_hasSubgaussianMGF
    [StandardBorelSpace State] [StandardBorelSpace Action]
    [Nonempty Action]
    (source : MeanCompatibleRewardKernel mdp)
    (policy : MarkovPolicy mdp) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardBound rewardVarianceProxy : NNReal)
    (hrewardBound : forall state action,
      |mdp.reward state action| <= (rewardBound : Real))
    (law : source.UniformSubgaussianRewardLaw rewardVarianceProxy) :
    ProbabilityTheory.HasSubgaussianMGF
      (mdp.sampledCumulativeReturnDeviation policy)
      ((mdp.horizon : NNReal) * rewardVarianceProxy +
        meanBellmanInnovationVarianceProxy rewardBound mdp.horizon)
      (source.stochasticTrajectoryMeasure policy initialState) := by
  unfold stochasticTrajectoryMeasure
  apply Concentration.hasSubgaussianMGF_compProd_of_forall_fintype
    initialState
    (source.stochasticTrajectoryKernelRemaining policy mdp.horizon le_rfl)
    (mdp.sampledCumulativeReturnDeviation policy)
    (mdp.measurable_sampledCumulativeReturnDeviation policy)
  intro state
  simpa [MDP.sampledCumulativeReturnDeviation] using
    source.stochasticTrajectoryKernelRemaining_sampledCumulativeReturnDeviationFrom_hasSubgaussianMGF
      policy rewardBound rewardVarianceProxy hrewardBound law
      mdp.horizon le_rfl state

/--
Fixed-horizon two-sided delta tail under an arbitrary finite initial-state law.
-/
theorem stochasticTrajectoryMeasure_sampledCumulativeReturnDeviation_abs_tail_le
    [StandardBorelSpace State] [StandardBorelSpace Action]
    [Nonempty Action]
    (source : MeanCompatibleRewardKernel mdp)
    (policy : MarkovPolicy mdp) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardBound rewardVarianceProxy : NNReal)
    (hrewardBound : forall state action,
      |mdp.reward state action| <= (rewardBound : Real))
    (law : source.UniformSubgaussianRewardLaw rewardVarianceProxy)
    (htotal : 0 <
      ((((mdp.horizon : NNReal) * rewardVarianceProxy +
        meanBellmanInnovationVarianceProxy rewardBound mdp.horizon : NNReal) : Real)))
    (delta : Real) (hdelta : 0 < delta) (hdelta_le_one : delta <= 1) :
    (source.stochasticTrajectoryMeasure policy initialState)
      {trajectory |
        Concentration.subGaussianSumConfidenceRadius
            ((mdp.horizon : NNReal) * rewardVarianceProxy +
              meanBellmanInnovationVarianceProxy rewardBound mdp.horizon) delta <=
          |mdp.sampledCumulativeReturnDeviation policy trajectory|} <=
      ENNReal.ofReal delta := by
  let mu := source.stochasticTrajectoryMeasure policy initialState
  let F : Filtration Nat
      (inferInstance : MeasurableSpace
        (State × RewardStepTrace Action State mdp.horizon)) :=
    Filtration.const Nat inferInstance le_rfl
  let Y : Nat -> State × RewardStepTrace Action State mdp.horizon -> Real :=
    fun _ => mdp.sampledCumulativeReturnDeviation policy
  let cY : Nat -> NNReal := fun _ =>
    (mdp.horizon : NNReal) * rewardVarianceProxy +
      meanBellmanInnovationVarianceProxy rewardBound mdp.horizon
  have hadapted : StronglyAdapted F Y := by
    intro i
    simpa [F, Y] using
      (mdp.measurable_sampledCumulativeReturnDeviation policy).stronglyMeasurable
  have hzero : ProbabilityTheory.HasSubgaussianMGF (Y 0) (cY 0) mu := by
    simpa [Y, cY, mu] using
      source.stochasticTrajectoryMeasure_sampledCumulativeReturnDeviation_hasSubgaussianMGF
        policy initialState rewardBound rewardVarianceProxy hrewardBound law
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
