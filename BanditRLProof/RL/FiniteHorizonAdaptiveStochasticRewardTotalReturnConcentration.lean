import BanditRLProof.RL.FiniteHorizonStochasticRewardIIDTotalReturnConcentration
import BanditRLProof.RL.FiniteHorizonAdaptiveEpisodeBatchLaw
import BanditRLProof.ConditionalExpectationReward

/-!
# Adaptive stochastic-reward episode-batch concentration

This module generates complete reward-bearing episode batches with a policy
selected from the preceding batch history.  It retains that history while
mapping the next-batch kernel, identifies the resulting dynamic sampled-return
law through `condDistrib` and `condExpKernel`, and applies the conditional
sub-Gaussian sum theorem across a fixed finite number of adaptive rounds.

No independence is assumed across rounds.  Independence is used only inside
each conditionally iid episode batch.  The result is a sampled-return
deviation bound, not a regret, optimism, or anytime theorem.
-/

open MeasureTheory
open scoped ENNReal ProbabilityTheory BigOperators

universe u v w

namespace ProbabilityTheory
namespace Kernel

variable {Input : Type u} {Output : Type v}
    [MeasurableSpace Input] [MeasurableSpace Output]

/-- Pair a kernel output with the input at which the kernel is evaluated. -/
noncomputable def retainedInputKernel
    (kernel : ProbabilityTheory.Kernel Input Output) :
    ProbabilityTheory.Kernel Input (Input × Output) :=
  ProbabilityTheory.Kernel.id.prod kernel

instance instRetainedInputKernelIsMarkov
    (kernel : ProbabilityTheory.Kernel Input Output)
    [ProbabilityTheory.IsMarkovKernel kernel] :
    ProbabilityTheory.IsMarkovKernel (retainedInputKernel kernel) := by
  unfold retainedInputKernel
  infer_instance

theorem retainedInputKernel_apply
    (kernel : ProbabilityTheory.Kernel Input Output)
    [ProbabilityTheory.IsMarkovKernel kernel]
    (input : Input) :
    retainedInputKernel kernel input =
      (kernel input).map (Prod.mk input) := by
  rw [retainedInputKernel, ProbabilityTheory.Kernel.prod_apply,
    ProbabilityTheory.Kernel.id_apply, Measure.dirac_prod]

/-- Recover the conditional law of the retained input/output pair. -/
theorem condDistrib_pair_ae_eq_retainedInputKernel_of_pair_map_eq_compProd
    {Sample : Type w} [MeasurableSpace Sample]
    [StandardBorelSpace (Input × Output)] [Nonempty (Input × Output)]
    (mu : Measure Sample) [IsFiniteMeasure mu]
    (condition : Sample → Input) (next : Sample → Output)
    (kernel : ProbabilityTheory.Kernel Input Output)
    [ProbabilityTheory.IsMarkovKernel kernel]
    (hcondition : Measurable condition) (hnext : Measurable next)
    (hpair :
      mu.map (fun sample => (condition sample, next sample)) =
        (mu.map condition).compProd kernel) :
    ProbabilityTheory.condDistrib
        (fun sample => (condition sample, next sample)) condition mu =ᵐ[
          mu.map condition]
      retainedInputKernel kernel := by
  apply ProbabilityTheory.condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
    hcondition (hcondition.prodMk hnext)
  calc
    mu.map
          (fun sample =>
            (condition sample, (condition sample, next sample))) =
        (mu.map (fun sample => (condition sample, next sample))).map
          (fun pair => (pair.1, pair)) := by
            symm
            simpa [Function.comp_def] using
              (Measure.map_map
                (μ := mu)
                (g := fun pair : Input × Output => (pair.1, pair))
                (f := fun sample => (condition sample, next sample))
                (measurable_fst.prodMk measurable_id)
                (hcondition.prodMk hnext))
    _ = ((mu.map condition).compProd kernel).map
          (fun pair => (pair.1, pair)) := by rw [hpair]
    _ = (mu.map condition).compProd (retainedInputKernel kernel) := by
      ext event hevent
      rw [Measure.map_apply
        (f := fun pair : Input × Output => (pair.1, pair))
        (measurable_fst.prodMk measurable_id) hevent]
      rw [Measure.compProd_apply
        (s := (fun pair : Input × Output => (pair.1, pair)) ⁻¹' event)
        (hevent.preimage (measurable_fst.prodMk measurable_id)),
        Measure.compProd_apply (s := event) hevent]
      congr with input
      rw [retainedInputKernel_apply]
      calc
        kernel input
              (Prod.mk input ⁻¹'
                ((fun pair : Input × Output => (input, pair)) ⁻¹' event)) =
            kernel input
              ((Prod.mk input : Output → Input × Output) ⁻¹'
                ((Prod.mk input : Input × Output → Input × (Input × Output)) ⁻¹' event)) := by
                  rfl
        _ = (Measure.map (Prod.mk input) (kernel input))
              ((Prod.mk input : Input × Output → Input × (Input × Output)) ⁻¹' event) := by
                symm
                exact Measure.map_apply
                  (μ := kernel input)
                  (f := Prod.mk input)
                  (measurable_const.prodMk measurable_id)
                  (hevent.preimage (measurable_const.prodMk measurable_id))

/-- Map a statistic which depends jointly on the retained input and output. -/
theorem condDistrib_dynamic_map_ae_eq_of_pair_map_eq_compProd
    {Sample : Type w} [MeasurableSpace Sample]
    [StandardBorelSpace (Input × Output)] [Nonempty (Input × Output)]
    {Result : Type*} [MeasurableSpace Result]
    [StandardBorelSpace Result] [Nonempty Result]
    (mu : Measure Sample) [IsFiniteMeasure mu]
    (condition : Sample → Input) (next : Sample → Output)
    (kernel : ProbabilityTheory.Kernel Input Output)
    [ProbabilityTheory.IsMarkovKernel kernel]
    (g : Input × Output → Result)
    (hcondition : Measurable condition) (hnext : Measurable next)
    (hg : Measurable g)
    (hpair :
      mu.map (fun sample => (condition sample, next sample)) =
        (mu.map condition).compProd kernel) :
    ProbabilityTheory.condDistrib
        (fun sample => g (condition sample, next sample)) condition mu =ᵐ[
          mu.map condition]
      (retainedInputKernel kernel).map g := by
  have hpairCond :=
    condDistrib_pair_ae_eq_retainedInputKernel_of_pair_map_eq_compProd
      mu condition next kernel hcondition hnext hpair
  have hcomp :
      ProbabilityTheory.condDistrib
          (g ∘ fun sample => (condition sample, next sample)) condition mu =ᵐ[
            mu.map condition]
        (ProbabilityTheory.condDistrib
          (fun sample => (condition sample, next sample)) condition mu).map g :=
    ProbabilityTheory.condDistrib_comp
      (mβ := inferInstance) (μ := mu) condition
      (hcondition.prodMk hnext).aemeasurable hg
  filter_upwards [hcomp, hpairCond] with input hcompInput hpairInput
  calc
    ProbabilityTheory.condDistrib
          (fun sample => g (condition sample, next sample)) condition mu input =
        ((ProbabilityTheory.condDistrib
          (fun sample => (condition sample, next sample)) condition mu).map g) input := by
            simpa [Function.comp_def] using hcompInput
    _ = ((retainedInputKernel kernel).map g) input := by
      rw [ProbabilityTheory.Kernel.map_apply _ hg,
        ProbabilityTheory.Kernel.map_apply _ hg, hpairInput]

end Kernel
end ProbabilityTheory

namespace BanditRLProof
namespace FiniteHorizonRL

variable {State : Type u} {Action : Type v}
    [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action]

/-- A complete stochastic-reward episode batch. -/
abbrev StochasticEpisodeBatch
    (mdp : MDP State Action) (episodes : Nat) :=
  Fin episodes → State × RewardStepTrace Action State mdp.horizon

/-- Finite history through stochastic batch coordinate `n`. -/
abbrev StochasticEpisodeBatchPrefix
    (mdp : MDP State Action) (episodes n : Nat) :=
  (i : Finset.Iic n) → StochasticEpisodeBatch mdp episodes

/-- Infinite stochastic episode-batch trajectory. -/
abbrev StochasticEpisodeBatchTrajectory
    (mdp : MDP State Action) (episodes : Nat) :=
  Nat → StochasticEpisodeBatch mdp episodes

/--
An adaptive source of complete stochastic-reward episode batches.

The dynamic measurability field is the only additional policy-selection
regularity needed by this route.  The exact batch-kernel equality supplies the
pointwise conditionally iid law selected by each observed prefix.
-/
structure AdaptiveStochasticEpisodeBatchSource
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState] (episodes : Nat) where
  rewardSource : mdp.MeanCompatibleRewardKernel
  initialPolicy : MarkovPolicy mdp
  successorPolicy : (n : Nat) →
    StochasticEpisodeBatchPrefix mdp episodes n → MarkovPolicy mdp
  batchKernel : (n : Nat) →
    ProbabilityTheory.Kernel
      (StochasticEpisodeBatchPrefix mdp episodes n)
      (StochasticEpisodeBatch mdp episodes)
  batchKernel_isMarkov : ∀ n,
    ProbabilityTheory.IsMarkovKernel (batchKernel n)
  batchKernel_eq_iidStochasticTrajectoryFamilyMeasure : ∀ n history,
    batchKernel n history =
      rewardSource.iidStochasticTrajectoryFamilyMeasure
        (successorPolicy n history) initialState episodes
  measurable_successorSampledReturnDeviation : ∀ n,
    Measurable fun pair :
        StochasticEpisodeBatchPrefix mdp episodes n ×
          StochasticEpisodeBatch mdp episodes =>
      mdp.sampledCumulativeReturnDeviationSum
        (successorPolicy n pair.1) episodes pair.2

namespace AdaptiveStochasticEpisodeBatchSource

instance instBatchKernelIsMarkov
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveStochasticEpisodeBatchSource mdp initialState episodes)
    (n : Nat) :
    ProbabilityTheory.IsMarkovKernel (source.batchKernel n) :=
  source.batchKernel_isMarkov n

/-- The adaptive infinite stochastic batch-trajectory law. -/
noncomputable def trajectoryMeasure
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveStochasticEpisodeBatchSource mdp initialState episodes) :
    Measure (StochasticEpisodeBatchTrajectory mdp episodes) :=
  ProbabilityTheory.Kernel.trajMeasure
    (X := fun _ : Nat => StochasticEpisodeBatch mdp episodes)
    (source.rewardSource.iidStochasticTrajectoryFamilyMeasure
      source.initialPolicy initialState episodes)
    source.batchKernel

instance instTrajectoryMeasureIsProbabilityMeasure
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveStochasticEpisodeBatchSource mdp initialState episodes) :
    IsProbabilityMeasure source.trajectoryMeasure := by
  unfold trajectoryMeasure
  infer_instance

/-- Coordinate zero has the configured initial stochastic batch law. -/
theorem trajectoryMeasure_map_eval_zero
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveStochasticEpisodeBatchSource mdp initialState episodes) :
    source.trajectoryMeasure.map (Function.eval 0) =
      source.rewardSource.iidStochasticTrajectoryFamilyMeasure
        source.initialPolicy initialState episodes := by
  unfold trajectoryMeasure
  exact RewardKernel.trajMeasure_map_eval_zero
    (X := fun _ : Nat => StochasticEpisodeBatch mdp episodes)
    (source.rewardSource.iidStochasticTrajectoryFamilyMeasure
      source.initialPolicy initialState episodes)
    source.batchKernel

/-- The prefix/next-batch marginal has the configured compProd law. -/
theorem trajectoryMeasure_prefix_compProd
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveStochasticEpisodeBatchSource mdp initialState episodes)
    (n : Nat) :
    source.trajectoryMeasure.map (Preorder.frestrictLe n) ⊗ₘ
        source.batchKernel n =
      source.trajectoryMeasure.map
        (fun trajectory =>
          (Preorder.frestrictLe n trajectory, trajectory (n + 1))) := by
  unfold trajectoryMeasure
  exact
    ProbabilityTheory.Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
      (X := fun _ : Nat => StochasticEpisodeBatch mdp episodes)
      (μ₀ := source.rewardSource.iidStochasticTrajectoryFamilyMeasure
        source.initialPolicy initialState episodes)
      (κ := source.batchKernel) (a := n)

/-- The dynamic next-round sampled-return statistic on prefix/batch pairs. -/
noncomputable def successorSampledReturnDeviation
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveStochasticEpisodeBatchSource mdp initialState episodes)
    (n : Nat)
    (pair : StochasticEpisodeBatchPrefix mdp episodes n ×
      StochasticEpisodeBatch mdp episodes) : Real :=
  mdp.sampledCumulativeReturnDeviationSum
    (source.successorPolicy n pair.1) episodes pair.2

/-- Conditional kernel of the dynamic next-round deviation. -/
noncomputable def successorDeviationKernel
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveStochasticEpisodeBatchSource mdp initialState episodes)
    (n : Nat) :
    ProbabilityTheory.Kernel
      (StochasticEpisodeBatchPrefix mdp episodes n) Real :=
  (ProbabilityTheory.Kernel.retainedInputKernel (source.batchKernel n)).map
    (source.successorSampledReturnDeviation n)

instance instSuccessorDeviationKernelIsMarkov
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveStochasticEpisodeBatchSource mdp initialState episodes)
    (n : Nat) :
    ProbabilityTheory.IsMarkovKernel (source.successorDeviationKernel n) := by
  unfold successorDeviationKernel
  exact ProbabilityTheory.Kernel.IsMarkovKernel.map _
    (source.measurable_successorSampledReturnDeviation n)

/-- Each deviation-kernel fiber is the selected policy's iid statistic law. -/
theorem successorDeviationKernel_apply
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveStochasticEpisodeBatchSource mdp initialState episodes)
    (n : Nat) (history : StochasticEpisodeBatchPrefix mdp episodes n) :
    source.successorDeviationKernel n history =
      (source.rewardSource.iidStochasticTrajectoryFamilyMeasure
        (source.successorPolicy n history) initialState episodes).map
          (mdp.sampledCumulativeReturnDeviationSum
            (source.successorPolicy n history) episodes) := by
  unfold successorDeviationKernel
  rw [ProbabilityTheory.Kernel.map_apply
      (f := source.successorSampledReturnDeviation n)
      (ProbabilityTheory.Kernel.retainedInputKernel (source.batchKernel n))
      (source.measurable_successorSampledReturnDeviation n) history,
    ProbabilityTheory.Kernel.retainedInputKernel_apply]
  calc
    Measure.map (source.successorSampledReturnDeviation n)
          (Measure.map (Prod.mk history) (source.batchKernel n history)) =
        Measure.map
          ((source.successorSampledReturnDeviation n) ∘ Prod.mk history)
          (source.batchKernel n history) :=
      Measure.map_map
        (source.measurable_successorSampledReturnDeviation n)
        (measurable_const.prodMk measurable_id)
    _ = (source.rewardSource.iidStochasticTrajectoryFamilyMeasure
          (source.successorPolicy n history) initialState episodes).map
            (mdp.sampledCumulativeReturnDeviationSum
              (source.successorPolicy n history) episodes) := by
      rw [source.batchKernel_eq_iidStochasticTrajectoryFamilyMeasure]
      rfl

/-- The trajectory-level dynamic deviation at successor coordinate `n + 1`. -/
noncomputable def successorSampledReturnDeviationAt
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveStochasticEpisodeBatchSource mdp initialState episodes)
    (n : Nat) (trajectory : StochasticEpisodeBatchTrajectory mdp episodes) : Real :=
  source.successorSampledReturnDeviation n
    (Preorder.frestrictLe n trajectory, trajectory (n + 1))

theorem measurable_successorSampledReturnDeviationAt
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveStochasticEpisodeBatchSource mdp initialState episodes)
    (n : Nat) :
    Measurable (source.successorSampledReturnDeviationAt n) := by
  exact (source.measurable_successorSampledReturnDeviation n).comp
    ((Preorder.measurable_frestrictLe n).prodMk (measurable_pi_apply (n + 1)))

/-- The conditional law of the dynamic successor deviation. -/
theorem trajectoryMeasure_condDistrib_successorSampledReturnDeviationAt
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    [StandardBorelSpace (StochasticEpisodeBatch mdp episodes)]
    [Nonempty (StochasticEpisodeBatch mdp episodes)]
    (source : AdaptiveStochasticEpisodeBatchSource mdp initialState episodes)
    (n : Nat) :
    ProbabilityTheory.condDistrib
        (source.successorSampledReturnDeviationAt n)
        (Preorder.frestrictLe n) source.trajectoryMeasure =ᵐ[
          source.trajectoryMeasure.map (Preorder.frestrictLe n)]
      source.successorDeviationKernel n := by
  exact
    ProbabilityTheory.Kernel.condDistrib_dynamic_map_ae_eq_of_pair_map_eq_compProd
      source.trajectoryMeasure
      (Preorder.frestrictLe n)
      (fun trajectory : StochasticEpisodeBatchTrajectory mdp episodes =>
        trajectory (n + 1))
      (source.batchKernel n)
      (source.successorSampledReturnDeviation n)
      (Preorder.measurable_frestrictLe n)
      (measurable_pi_apply (n + 1))
      (source.measurable_successorSampledReturnDeviation n)
      (source.trajectoryMeasure_prefix_compProd n).symm

/-- The trimmed conditional-expectation kernel has the same dynamic law. -/
theorem condExpKernel_map_successorSampledReturnDeviationAt_eq
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    [StandardBorelSpace (StochasticEpisodeBatch mdp episodes)]
    [Nonempty (StochasticEpisodeBatch mdp episodes)]
    [StandardBorelSpace (StochasticEpisodeBatchTrajectory mdp episodes)]
    (source : AdaptiveStochasticEpisodeBatchSource mdp initialState episodes)
    (n : Nat) :
    Filter.Eventually
      (fun trajectory : StochasticEpisodeBatchTrajectory mdp episodes =>
        Measure.map (source.successorSampledReturnDeviationAt n)
            (ProbabilityTheory.condExpKernel source.trajectoryMeasure
              ((inferInstance : MeasurableSpace
                (StochasticEpisodeBatchPrefix mdp episodes n)).comap
                  (Preorder.frestrictLe n)) trajectory) =
          source.successorDeviationKernel n
            (Preorder.frestrictLe n trajectory))
      (ae (source.trajectoryMeasure.trim
        (Preorder.measurable_frestrictLe n).comap_le)) := by
  exact
    ConditionalExpectationReward.condExpKernel_map_eq_of_condDistrib_ae_eq_real_trim
      source.trajectoryMeasure
      (source.successorSampledReturnDeviationAt n)
      (Preorder.frestrictLe n)
      (source.measurable_successorSampledReturnDeviationAt n)
      (Preorder.measurable_frestrictLe n)
      (source.successorDeviationKernel n)
      (source.trajectoryMeasure_condDistrib_successorSampledReturnDeviationAt n)

/-- Prefix-level increment, including the genuine initial stochastic batch. -/
noncomputable def sampledReturnDeviationPrefixIncrement
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveStochasticEpisodeBatchSource mdp initialState episodes) :
    (round : Nat) → StochasticEpisodeBatchPrefix mdp episodes round → Real
  | 0, history =>
      mdp.sampledCumulativeReturnDeviationSum source.initialPolicy episodes
        (history ⟨0, Finset.mem_Iic.mpr le_rfl⟩)
  | n + 1, history =>
      source.successorSampledReturnDeviation n
        (Preorder.frestrictLe₂
          (π := fun _ : Nat => StochasticEpisodeBatch mdp episodes)
          (Nat.le_succ n) history,
        history ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩)

theorem measurable_sampledReturnDeviationPrefixIncrement
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveStochasticEpisodeBatchSource mdp initialState episodes)
    (round : Nat) :
    Measurable (source.sampledReturnDeviationPrefixIncrement round) := by
  cases round with
  | zero =>
      simpa [sampledReturnDeviationPrefixIncrement] using
        (mdp.measurable_sampledCumulativeReturnDeviationSum
          source.initialPolicy episodes).comp
            (measurable_pi_apply
              (⟨0, Finset.mem_Iic.mpr le_rfl⟩ : Finset.Iic 0))
  | succ n =>
      simpa [sampledReturnDeviationPrefixIncrement] using
        (source.measurable_successorSampledReturnDeviation n).comp
          ((Preorder.measurable_frestrictLe₂
            (X := fun _ : Nat => StochasticEpisodeBatch mdp episodes)
            (Nat.le_succ n)).prodMk
              (measurable_pi_apply
                (⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩ : Finset.Iic (n + 1))))

/-- Adapted sampled-return deviation increment on the full trajectory. -/
noncomputable def sampledReturnDeviationIncrement
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveStochasticEpisodeBatchSource mdp initialState episodes)
    (round : Nat)
    (trajectory : StochasticEpisodeBatchTrajectory mdp episodes) : Real :=
  source.sampledReturnDeviationPrefixIncrement round
    (Preorder.frestrictLe round trajectory)

theorem measurable_sampledReturnDeviationIncrement
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveStochasticEpisodeBatchSource mdp initialState episodes)
    (round : Nat) :
    Measurable (source.sampledReturnDeviationIncrement round) := by
  exact (source.measurable_sampledReturnDeviationPrefixIncrement round).comp
    (Preorder.measurable_frestrictLe round)

theorem sampledReturnDeviationIncrement_stronglyAdapted_piLE
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveStochasticEpisodeBatchSource mdp initialState episodes) :
    StronglyAdapted
      (Filtration.piLE
        (X := fun _ : Nat => StochasticEpisodeBatch mdp episodes))
      source.sampledReturnDeviationIncrement := by
  intro round
  rw [Filtration.piLE_eq_comap_frestrictLe]
  exact ((source.measurable_sampledReturnDeviationPrefixIncrement round).comp
    (Measurable.of_comap_le le_rfl)).stronglyMeasurable

/-- The initial adaptive coordinate inherits the iid batch MGF. -/
theorem sampledReturnDeviationIncrement_zero_hasSubgaussianMGF
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    [StandardBorelSpace State] [StandardBorelSpace Action]
    [Nonempty Action]
    [StandardBorelSpace (StochasticEpisodeBatch mdp episodes)]
    (source : AdaptiveStochasticEpisodeBatchSource mdp initialState episodes)
    (rewardBound rewardVarianceProxy : NNReal)
    (hrewardBound : ∀ state action,
      |mdp.reward state action| ≤ (rewardBound : Real))
    (law : source.rewardSource.UniformSubgaussianRewardLaw
      rewardVarianceProxy) :
    ProbabilityTheory.HasSubgaussianMGF
      (source.sampledReturnDeviationIncrement 0)
      (mdp.iidSampledCumulativeReturnDeviationVarianceProxy
        episodes rewardBound rewardVarianceProxy)
      source.trajectoryMeasure := by
  have hbase :=
    source.rewardSource.iidStochasticTrajectoryFamilyMeasure_sampledCumulativeReturnDeviationSum_hasSubgaussianMGF
      source.initialPolicy initialState episodes rewardBound rewardVarianceProxy
      hrewardBound law
  rw [← source.trajectoryMeasure_map_eval_zero] at hbase
  have hlift := ProbabilityTheory.HasSubgaussianMGF.of_map
    (μ := source.trajectoryMeasure)
    (Y := Function.eval 0)
    (X := mdp.sampledCumulativeReturnDeviationSum
      source.initialPolicy episodes)
    (measurable_pi_apply 0).aemeasurable hbase
  simpa [sampledReturnDeviationIncrement,
    sampledReturnDeviationPrefixIncrement, Preorder.frestrictLe_apply,
    Function.comp_def] using hlift

/-- Every successor adaptive coordinate is conditionally sub-Gaussian. -/
theorem sampledReturnDeviationIncrement_succ_hasCondSubgaussianMGF
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    [StandardBorelSpace State] [StandardBorelSpace Action]
    [Nonempty Action]
    [StandardBorelSpace (StochasticEpisodeBatch mdp episodes)]
    [Nonempty (StochasticEpisodeBatch mdp episodes)]
    [StandardBorelSpace (StochasticEpisodeBatchTrajectory mdp episodes)]
    (source : AdaptiveStochasticEpisodeBatchSource mdp initialState episodes)
    (n : Nat) (rewardBound rewardVarianceProxy : NNReal)
    (hrewardBound : ∀ state action,
      |mdp.reward state action| ≤ (rewardBound : Real))
    (law : source.rewardSource.UniformSubgaussianRewardLaw
      rewardVarianceProxy) :
    ProbabilityTheory.HasCondSubgaussianMGF
      (Filtration.piLE
        (X := fun _ : Nat => StochasticEpisodeBatch mdp episodes) n)
      ((Filtration.piLE
        (X := fun _ : Nat => StochasticEpisodeBatch mdp episodes)).le n)
      (source.sampledReturnDeviationIncrement (n + 1))
      (mdp.iidSampledCumulativeReturnDeviationVarianceProxy
        episodes rewardBound rewardVarianceProxy)
      source.trajectoryMeasure := by
  let prefixMap : StochasticEpisodeBatchTrajectory mdp episodes →
      StochasticEpisodeBatchPrefix mdp episodes n := Preorder.frestrictLe n
  let X := source.successorSampledReturnDeviationAt n
  let target : StochasticEpisodeBatchTrajectory mdp episodes → Measure Real :=
    fun trajectory => source.successorDeviationKernel n (prefixMap trajectory)
  let mcond : MeasurableSpace
      (StochasticEpisodeBatchTrajectory mdp episodes) :=
    (inferInstance : MeasurableSpace
      (StochasticEpisodeBatchPrefix mdp episodes n)).comap prefixMap
  have hmcond : mcond ≤ MeasurableSpace.pi := by
    simpa [mcond, prefixMap] using
      (Preorder.measurable_frestrictLe
        (X := fun _ : Nat => StochasticEpisodeBatch mdp episodes) n).comap_le
  have hspace :
      Filtration.piLE
          (X := fun _ : Nat => StochasticEpisodeBatch mdp episodes) n =
        mcond := by
    simpa [mcond, prefixMap] using
      (Filtration.piLE_eq_comap_frestrictLe
        (X := fun _ : Nat => StochasticEpisodeBatch mdp episodes) n)
  have hkernel : Filter.Eventually
      (fun trajectory : StochasticEpisodeBatchTrajectory mdp episodes =>
        @Measure.map (StochasticEpisodeBatchTrajectory mdp episodes) Real
            MeasurableSpace.pi inferInstance X
            ((@ProbabilityTheory.condExpKernel
              (StochasticEpisodeBatchTrajectory mdp episodes)
              MeasurableSpace.pi _ source.trajectoryMeasure _ mcond)
                trajectory) =
          target trajectory)
      (ae (source.trajectoryMeasure.trim hmcond)) := by
    simpa [X, target, prefixMap, mcond] using
      source.condExpKernel_map_successorSampledReturnDeviationAt_eq n
  have htarget : Filter.Eventually
      (fun trajectory : StochasticEpisodeBatchTrajectory mdp episodes =>
        ProbabilityTheory.HasSubgaussianMGF id
          (mdp.iidSampledCumulativeReturnDeviationVarianceProxy
            episodes rewardBound rewardVarianceProxy)
          (target trajectory))
      (ae (source.trajectoryMeasure.trim hmcond)) := by
    exact Filter.Eventually.of_forall fun trajectory => by
      let history := prefixMap trajectory
      let policy := source.successorPolicy n history
      have hbase :=
        source.rewardSource.iidStochasticTrajectoryFamilyMeasure_sampledCumulativeReturnDeviationSum_hasSubgaussianMGF
          policy initialState episodes rewardBound rewardVarianceProxy
          hrewardBound law
      have hid :=
        (ProbabilityTheory.HasSubgaussianMGF.id_map_iff
          (mdp.measurable_sampledCumulativeReturnDeviationSum
            policy episodes).aemeasurable).2 hbase
      change ProbabilityTheory.HasSubgaussianMGF id
        (mdp.iidSampledCumulativeReturnDeviationVarianceProxy
          episodes rewardBound rewardVarianceProxy)
        (source.successorDeviationKernel n history)
      rw [source.successorDeviationKernel_apply n history]
      exact hid
  have hcondComap :=
    ConditionalExpectationReward.hasCondSubgaussianMGF_of_condExpKernel_map_eq
      (mOmega := MeasurableSpace.pi)
      source.trajectoryMeasure mcond hmcond X
      (mdp.iidSampledCumulativeReturnDeviationVarianceProxy
        episodes rewardBound rewardVarianceProxy)
      (source.measurable_successorSampledReturnDeviationAt n)
      target hkernel htarget
  have hcond :=
    ConditionalExpectationReward.hasCondSubgaussianMGF_congr_measurableSpace
      (mOmega := MeasurableSpace.pi)
      source.trajectoryMeasure mcond
      (Filtration.piLE
        (X := fun _ : Nat => StochasticEpisodeBatch mdp episodes) n)
      hmcond
      ((Filtration.piLE
        (X := fun _ : Nat => StochasticEpisodeBatch mdp episodes)).le n)
      hspace.symm X
      (mdp.iidSampledCumulativeReturnDeviationVarianceProxy
        episodes rewardBound rewardVarianceProxy)
      hcondComap
  simpa [sampledReturnDeviationIncrement,
    sampledReturnDeviationPrefixIncrement,
    successorSampledReturnDeviationAt, X, prefixMap,
    Preorder.frestrictLe_apply, Preorder.frestrictLe₂_apply] using hcond

/-- Sum of per-round proxies over `rounds` adaptive stochastic batches. -/
noncomputable def cumulativeSampledReturnDeviationVarianceProxy
    (mdp : MDP State Action) (rounds episodes : Nat)
    (rewardBound rewardVarianceProxy : NNReal) : NNReal :=
  ∑ _round ∈ Finset.range rounds,
    mdp.iidSampledCumulativeReturnDeviationVarianceProxy
      episodes rewardBound rewardVarianceProxy

theorem cumulativeSampledReturnDeviationVarianceProxy_eq
    (mdp : MDP State Action) (rounds episodes : Nat)
    (rewardBound rewardVarianceProxy : NNReal) :
    cumulativeSampledReturnDeviationVarianceProxy mdp rounds episodes
        rewardBound rewardVarianceProxy =
      (rounds : NNReal) *
        mdp.iidSampledCumulativeReturnDeviationVarianceProxy
          episodes rewardBound rewardVarianceProxy := by
  simp [cumulativeSampledReturnDeviationVarianceProxy]

/-- Cumulative sampled-return deviation over `rounds` adaptive batches. -/
noncomputable def cumulativeSampledReturnDeviation
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveStochasticEpisodeBatchSource mdp initialState episodes)
    (rounds : Nat)
    (trajectory : StochasticEpisodeBatchTrajectory mdp episodes) : Real :=
  ∑ round ∈ Finset.range rounds,
    source.sampledReturnDeviationIncrement round trajectory

/-- Fixed-round two-sided tail for adaptive stochastic sampled returns. -/
theorem trajectoryMeasure_cumulativeSampledReturnDeviation_abs_tail_le
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    [StandardBorelSpace State] [StandardBorelSpace Action]
    [Nonempty Action]
    [StandardBorelSpace (StochasticEpisodeBatch mdp episodes)]
    [Nonempty (StochasticEpisodeBatch mdp episodes)]
    [StandardBorelSpace (StochasticEpisodeBatchTrajectory mdp episodes)]
    (source : AdaptiveStochasticEpisodeBatchSource mdp initialState episodes)
    (rounds : Nat) (rewardBound rewardVarianceProxy : NNReal)
    (hrewardBound : ∀ state action,
      |mdp.reward state action| ≤ (rewardBound : Real))
    (law : source.rewardSource.UniformSubgaussianRewardLaw
      rewardVarianceProxy)
    (htotal : 0 <
      ((cumulativeSampledReturnDeviationVarianceProxy mdp rounds episodes
        rewardBound rewardVarianceProxy : NNReal) : Real))
    (delta : Real) (hdelta : 0 < delta) (hdelta_le_one : delta ≤ 1) :
    source.trajectoryMeasure
        {trajectory |
          Concentration.subGaussianSumConfidenceRadius
              (cumulativeSampledReturnDeviationVarianceProxy mdp rounds episodes
                rewardBound rewardVarianceProxy) delta ≤
            |source.cumulativeSampledReturnDeviation rounds trajectory|} ≤
      ENNReal.ofReal delta := by
  let F := Filtration.piLE
    (X := fun _ : Nat => StochasticEpisodeBatch mdp episodes)
  let cY : Nat → NNReal := fun _ =>
    mdp.iidSampledCumulativeReturnDeviationVarianceProxy
      episodes rewardBound rewardVarianceProxy
  have hadapted : StronglyAdapted F source.sampledReturnDeviationIncrement := by
    simpa [F] using source.sampledReturnDeviationIncrement_stronglyAdapted_piLE
  have hzero : ProbabilityTheory.HasSubgaussianMGF
      (source.sampledReturnDeviationIncrement 0) (cY 0)
      source.trajectoryMeasure := by
    simpa [cY] using
      source.sampledReturnDeviationIncrement_zero_hasSubgaussianMGF
        rewardBound rewardVarianceProxy hrewardBound law
  have hsucc : ∀ i, i < rounds - 1 →
      ProbabilityTheory.HasCondSubgaussianMGF
        (F i) (F.le i) (source.sampledReturnDeviationIncrement (i + 1))
        (cY (i + 1)) source.trajectoryMeasure := by
    intro i _hi
    simpa [F, cY] using
      source.sampledReturnDeviationIncrement_succ_hasCondSubgaussianMGF
        i rewardBound rewardVarianceProxy hrewardBound law
  have hvariance :
      0 < ((((Finset.range rounds).sum cY : NNReal) : Real)) := by
    simpa [cY, cumulativeSampledReturnDeviationVarianceProxy] using htotal
  simpa [cumulativeSampledReturnDeviationVarianceProxy,
    cumulativeSampledReturnDeviation, cY] using
    (Concentration.condSubGaussian_sum_abs_tail_ennreal_delta_of_stronglyAdapted
      hadapted hzero rounds hsucc hvariance delta hdelta hdelta_le_one)

end AdaptiveStochasticEpisodeBatchSource
end FiniteHorizonRL
end BanditRLProof
