import BanditRLProof.RL.FiniteHorizonAdaptiveStochasticRewardSampledEmpiricalOptimisticSelfConsistentCausalSource
import BanditRLProof.RL.FiniteHorizonAdaptiveStochasticRewardTotalReturnConcentration

/-!
# Sampled-return concentration on the heterogeneous causal source

This module transports two adaptive sampled-return concentration processes to
the dependent source whose coordinate `n` contains `episodes n` complete
stochastic episodes.  The supporting process uses the initial policy and
`episodes 0` at coordinate zero, then the prefix-selected policy and
`episodes (n + 1)` at coordinate `n + 1`; each batch is centered at its own
sampled initial-state value.  The regret-facing global process is zero at
coordinate zero and globally centers successor coordinates `1..rounds` by the
initial-law expected value of the selected policy.  Its measurable-selector
boundary is packaged by `GlobalReturnMeasurability`.

The proof route maps each exact selected iid batch fiber to its sampled-return
deviation, identifies the dynamic conditional law through the prefix/next
`compProd` theorem, obtains the corresponding conditional sub-Gaussian MGF,
and applies the existing strongly-adapted finite-sum tail theorem.  Each total
variance proxy is the genuine heterogeneous sum of its coordinate proxies;
the global proxy also retains sampled-initial-state value fluctuation.

Regularity is finite measurable nonempty State/Action with measurable
singletons, a probability initial law, Standard Borel State/Action for regular
conditional laws, a uniform selected-reward sub-Gaussian law, and a deterministic
bound on stored mean rewards.  The generic tail keeps strict positivity of the
summed proxy explicit.

Failure policy: this proves sampled-return concentration for the new
round-varying latest-batch causal algorithm.  It does not transport empirical
model confidence, optimism, regret, or any rate from the old constant-parameter
window laws.  It is fixed-`rounds`, not uniform-in-time, pathwise,
almost-sure, anytime, minimax, or complete UCB-VI control.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

universe u v

namespace BanditRLProof.FiniteHorizonRL

variable {State : Type u} {Action : Type v}
    [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action]
    [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action]

namespace HeterogeneousAdaptiveStochasticEpisodeBatchSource

/-- Dynamic next-coordinate sampled-return deviation on a prefix/batch pair. -/
noncomputable def successorSampledReturnDeviation
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat -> Nat}
    (source : HeterogeneousAdaptiveStochasticEpisodeBatchSource
      mdp initialState episodes) (n : Nat)
    (pair : HeterogeneousStochasticEpisodeBatchPrefix mdp episodes n ×
      StochasticEpisodeBatch mdp (episodes (n + 1))) : Real :=
  mdp.sampledCumulativeReturnDeviationSum
    (source.successorPolicy n pair.1) (episodes (n + 1)) pair.2

/-- Conditional kernel of the dynamic heterogeneous successor deviation. -/
noncomputable def successorDeviationKernel
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat -> Nat}
    (source : HeterogeneousAdaptiveStochasticEpisodeBatchSource
      mdp initialState episodes) (n : Nat) :
    Kernel (HeterogeneousStochasticEpisodeBatchPrefix mdp episodes n) Real :=
  (Kernel.retainedInputKernel (source.batchKernel n)).map
    (source.successorSampledReturnDeviation n)

instance instSuccessorDeviationKernelIsMarkov
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat -> Nat}
    (source : HeterogeneousAdaptiveStochasticEpisodeBatchSource
      mdp initialState episodes) (n : Nat) :
    IsMarkovKernel (source.successorDeviationKernel n) := by
  unfold successorDeviationKernel
  exact Kernel.IsMarkovKernel.map _
    (source.measurable_successorSampledReturnDeviation n)

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- Every dynamic deviation fiber is the selected policy's iid statistic law. -/
theorem successorDeviationKernel_apply
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat -> Nat}
    (source : HeterogeneousAdaptiveStochasticEpisodeBatchSource
      mdp initialState episodes) (n : Nat)
    (history : HeterogeneousStochasticEpisodeBatchPrefix mdp episodes n) :
    source.successorDeviationKernel n history =
      (source.rewardSource.iidStochasticTrajectoryFamilyMeasure
        (source.successorPolicy n history) initialState
        (episodes (n + 1))).map
          (mdp.sampledCumulativeReturnDeviationSum
            (source.successorPolicy n history) (episodes (n + 1))) := by
  unfold successorDeviationKernel
  rw [Kernel.map_apply
      (f := source.successorSampledReturnDeviation n)
      (Kernel.retainedInputKernel (source.batchKernel n))
      (source.measurable_successorSampledReturnDeviation n) history,
    Kernel.retainedInputKernel_apply]
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
          (source.successorPolicy n history) initialState
          (episodes (n + 1))).map
            (mdp.sampledCumulativeReturnDeviationSum
              (source.successorPolicy n history) (episodes (n + 1))) := by
      rw [source.batchKernel_eq_iidStochasticTrajectoryFamilyMeasure]
      rfl

/-- Dynamic deviation evaluated at successor trajectory coordinate `n + 1`. -/
noncomputable def successorSampledReturnDeviationAt
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat -> Nat}
    (source : HeterogeneousAdaptiveStochasticEpisodeBatchSource
      mdp initialState episodes) (n : Nat)
    (trajectory : HeterogeneousStochasticEpisodeBatchTrajectory mdp episodes) :
    Real :=
  source.successorSampledReturnDeviation n
    (Preorder.frestrictLe n trajectory, trajectory (n + 1))

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
theorem measurable_successorSampledReturnDeviationAt
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat -> Nat}
    (source : HeterogeneousAdaptiveStochasticEpisodeBatchSource
      mdp initialState episodes) (n : Nat) :
    Measurable (source.successorSampledReturnDeviationAt n) := by
  exact (source.measurable_successorSampledReturnDeviation n).comp
    ((Preorder.measurable_frestrictLe n).prodMk
      (measurable_pi_apply (n + 1)))

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- Conditional law of the heterogeneous dynamic successor deviation. -/
theorem trajectoryMeasure_condDistrib_successorSampledReturnDeviationAt
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat -> Nat}
    (source : HeterogeneousAdaptiveStochasticEpisodeBatchSource
      mdp initialState episodes) (n : Nat)
    [StandardBorelSpace
      (HeterogeneousStochasticEpisodeBatchPrefix mdp episodes n)]
    [Nonempty (HeterogeneousStochasticEpisodeBatchPrefix mdp episodes n)]
    [StandardBorelSpace
      (StochasticEpisodeBatch mdp (episodes (n + 1)))]
    [Nonempty (StochasticEpisodeBatch mdp (episodes (n + 1)))]
    :
    condDistrib (source.successorSampledReturnDeviationAt n)
        (Preorder.frestrictLe n) source.trajectoryMeasure =ᵐ[
          source.trajectoryMeasure.map (Preorder.frestrictLe n)]
      source.successorDeviationKernel n := by
  exact Kernel.condDistrib_dynamic_map_ae_eq_of_pair_map_eq_compProd
    source.trajectoryMeasure
    (Preorder.frestrictLe n)
    (fun trajectory :
      HeterogeneousStochasticEpisodeBatchTrajectory mdp episodes =>
        trajectory (n + 1))
    (source.batchKernel n)
    (source.successorSampledReturnDeviation n)
    (Preorder.measurable_frestrictLe n)
    (measurable_pi_apply (n + 1))
    (source.measurable_successorSampledReturnDeviation n)
    (source.trajectoryMeasure_prefix_compProd n).symm

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action] in
/-- Trimmed conditional-expectation kernel form of the same dynamic law. -/
theorem condExpKernel_map_successorSampledReturnDeviationAt_eq
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat -> Nat}
    (source : HeterogeneousAdaptiveStochasticEpisodeBatchSource
      mdp initialState episodes) (n : Nat)
    [StandardBorelSpace
      (HeterogeneousStochasticEpisodeBatchPrefix mdp episodes n)]
    [Nonempty (HeterogeneousStochasticEpisodeBatchPrefix mdp episodes n)]
    [StandardBorelSpace
      (StochasticEpisodeBatch mdp (episodes (n + 1)))]
    [Nonempty (StochasticEpisodeBatch mdp (episodes (n + 1)))]
    [StandardBorelSpace
      (HeterogeneousStochasticEpisodeBatchTrajectory mdp episodes)]
    :
    Filter.Eventually
      (fun trajectory :
          HeterogeneousStochasticEpisodeBatchTrajectory mdp episodes =>
        Measure.map (source.successorSampledReturnDeviationAt n)
            (condExpKernel source.trajectoryMeasure
              ((inferInstance : MeasurableSpace
                (HeterogeneousStochasticEpisodeBatchPrefix mdp episodes n)).comap
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

/-- Prefix-level heterogeneous increment, including coordinate zero. -/
noncomputable def sampledReturnDeviationPrefixIncrement
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat -> Nat}
    (source : HeterogeneousAdaptiveStochasticEpisodeBatchSource
      mdp initialState episodes) :
    (round : Nat) ->
      HeterogeneousStochasticEpisodeBatchPrefix mdp episodes round -> Real
  | 0, history =>
      mdp.sampledCumulativeReturnDeviationSum source.initialPolicy (episodes 0)
        (history ⟨0, Finset.mem_Iic.mpr le_rfl⟩)
  | n + 1, history =>
      source.successorSampledReturnDeviation n
        (Preorder.frestrictLe₂
          (π := fun k : Nat => StochasticEpisodeBatch mdp (episodes k))
          (Nat.le_succ n) history,
        history ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩)

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
theorem measurable_sampledReturnDeviationPrefixIncrement
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat -> Nat}
    (source : HeterogeneousAdaptiveStochasticEpisodeBatchSource
      mdp initialState episodes) (round : Nat) :
    Measurable (source.sampledReturnDeviationPrefixIncrement round) := by
  cases round with
  | zero =>
      simpa [sampledReturnDeviationPrefixIncrement] using
        (mdp.measurable_sampledCumulativeReturnDeviationSum
          source.initialPolicy (episodes 0)).comp
            (measurable_pi_apply
              (⟨0, Finset.mem_Iic.mpr le_rfl⟩ : Finset.Iic 0))
  | succ n =>
      simpa [sampledReturnDeviationPrefixIncrement] using
        (source.measurable_successorSampledReturnDeviation n).comp
          ((Preorder.measurable_frestrictLe₂
            (X := fun k : Nat => StochasticEpisodeBatch mdp (episodes k))
            (Nat.le_succ n)).prodMk
              (measurable_pi_apply
                (⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩ : Finset.Iic (n + 1))))

/-- Adapted heterogeneous sampled-return increment on the full trajectory. -/
noncomputable def sampledReturnDeviationIncrement
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat -> Nat}
    (source : HeterogeneousAdaptiveStochasticEpisodeBatchSource
      mdp initialState episodes) (round : Nat)
    (trajectory : HeterogeneousStochasticEpisodeBatchTrajectory mdp episodes) :
    Real :=
  source.sampledReturnDeviationPrefixIncrement round
    (Preorder.frestrictLe round trajectory)

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
theorem measurable_sampledReturnDeviationIncrement
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat -> Nat}
    (source : HeterogeneousAdaptiveStochasticEpisodeBatchSource
      mdp initialState episodes) (round : Nat) :
    Measurable (source.sampledReturnDeviationIncrement round) := by
  exact (source.measurable_sampledReturnDeviationPrefixIncrement round).comp
    (Preorder.measurable_frestrictLe round)

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
theorem sampledReturnDeviationIncrement_stronglyAdapted_piLE
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat -> Nat}
    (source : HeterogeneousAdaptiveStochasticEpisodeBatchSource
      mdp initialState episodes) :
    StronglyAdapted
      (Filtration.piLE
        (X := fun n : Nat => StochasticEpisodeBatch mdp (episodes n)))
      source.sampledReturnDeviationIncrement := by
  intro round
  rw [Filtration.piLE_eq_comap_frestrictLe]
  exact ((source.measurable_sampledReturnDeviationPrefixIncrement round).comp
    (Measurable.of_comap_le le_rfl)).stronglyMeasurable

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] in
/-- Coordinate zero inherits the iid batch MGF at `episodes 0`. -/
theorem sampledReturnDeviationIncrement_zero_hasSubgaussianMGF
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat -> Nat}
    [StandardBorelSpace State] [StandardBorelSpace Action]
    [StandardBorelSpace (StochasticEpisodeBatch mdp (episodes 0))]
    (source : HeterogeneousAdaptiveStochasticEpisodeBatchSource
      mdp initialState episodes) (rewardBound rewardVarianceProxy : NNReal)
    (hrewardBound : forall state action,
      |mdp.reward state action| <= (rewardBound : Real))
    (law : source.rewardSource.UniformSubgaussianRewardLaw
      rewardVarianceProxy) :
    HasSubgaussianMGF (source.sampledReturnDeviationIncrement 0)
      (mdp.iidSampledCumulativeReturnDeviationVarianceProxy
        (episodes 0) rewardBound rewardVarianceProxy)
      source.trajectoryMeasure := by
  have hbase :=
    source.rewardSource.iidStochasticTrajectoryFamilyMeasure_sampledCumulativeReturnDeviationSum_hasSubgaussianMGF
      source.initialPolicy initialState (episodes 0) rewardBound
      rewardVarianceProxy hrewardBound law
  rw [← source.trajectoryMeasure_map_eval_zero] at hbase
  have hlift := HasSubgaussianMGF.of_map
    (μ := source.trajectoryMeasure)
    (Y := Function.eval 0)
    (X := mdp.sampledCumulativeReturnDeviationSum
      source.initialPolicy (episodes 0))
    (measurable_pi_apply 0).aemeasurable hbase
  simpa [sampledReturnDeviationIncrement,
    sampledReturnDeviationPrefixIncrement, Preorder.frestrictLe_apply,
    Function.comp_def] using hlift

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action] in
/-- Coordinate `n + 1` is conditionally sub-Gaussian at its own batch size. -/
theorem sampledReturnDeviationIncrement_succ_hasCondSubgaussianMGF
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat -> Nat}
    [StandardBorelSpace State] [StandardBorelSpace Action]
    (source : HeterogeneousAdaptiveStochasticEpisodeBatchSource
      mdp initialState episodes) (n : Nat)
    [StandardBorelSpace
      (HeterogeneousStochasticEpisodeBatchPrefix mdp episodes n)]
    [Nonempty (HeterogeneousStochasticEpisodeBatchPrefix mdp episodes n)]
    [StandardBorelSpace
      (StochasticEpisodeBatch mdp (episodes (n + 1)))]
    [Nonempty (StochasticEpisodeBatch mdp (episodes (n + 1)))]
    [StandardBorelSpace
      (HeterogeneousStochasticEpisodeBatchTrajectory mdp episodes)]
    (rewardBound rewardVarianceProxy : NNReal)
    (hrewardBound : forall state action,
      |mdp.reward state action| <= (rewardBound : Real))
    (law : source.rewardSource.UniformSubgaussianRewardLaw
      rewardVarianceProxy) :
    HasCondSubgaussianMGF
      (Filtration.piLE
        (X := fun k : Nat => StochasticEpisodeBatch mdp (episodes k)) n)
      ((Filtration.piLE
        (X := fun k : Nat => StochasticEpisodeBatch mdp (episodes k))).le n)
      (source.sampledReturnDeviationIncrement (n + 1))
      (mdp.iidSampledCumulativeReturnDeviationVarianceProxy
        (episodes (n + 1)) rewardBound rewardVarianceProxy)
      source.trajectoryMeasure := by
  let prefixMap :
      HeterogeneousStochasticEpisodeBatchTrajectory mdp episodes ->
        HeterogeneousStochasticEpisodeBatchPrefix mdp episodes n :=
    Preorder.frestrictLe n
  let X := source.successorSampledReturnDeviationAt n
  let target : HeterogeneousStochasticEpisodeBatchTrajectory mdp episodes ->
      Measure Real :=
    fun trajectory => source.successorDeviationKernel n (prefixMap trajectory)
  let mcond : MeasurableSpace
      (HeterogeneousStochasticEpisodeBatchTrajectory mdp episodes) :=
    (inferInstance : MeasurableSpace
      (HeterogeneousStochasticEpisodeBatchPrefix mdp episodes n)).comap
        prefixMap
  have hmcond : mcond <= MeasurableSpace.pi := by
    simpa [mcond, prefixMap] using
      (Preorder.measurable_frestrictLe
        (X := fun k : Nat => StochasticEpisodeBatch mdp (episodes k)) n).comap_le
  have hspace :
      Filtration.piLE
          (X := fun k : Nat => StochasticEpisodeBatch mdp (episodes k)) n =
        mcond := by
    simpa [mcond, prefixMap] using
      (Filtration.piLE_eq_comap_frestrictLe
        (X := fun k : Nat => StochasticEpisodeBatch mdp (episodes k)) n)
  have hkernel : Filter.Eventually
      (fun trajectory :
          HeterogeneousStochasticEpisodeBatchTrajectory mdp episodes =>
        @Measure.map
            (HeterogeneousStochasticEpisodeBatchTrajectory mdp episodes) Real
            MeasurableSpace.pi inferInstance X
            ((@condExpKernel
              (HeterogeneousStochasticEpisodeBatchTrajectory mdp episodes)
              MeasurableSpace.pi _ source.trajectoryMeasure _ mcond)
                trajectory) =
          target trajectory)
      (ae (source.trajectoryMeasure.trim hmcond)) := by
    simpa [X, target, prefixMap, mcond] using
      source.condExpKernel_map_successorSampledReturnDeviationAt_eq n
  have htarget : Filter.Eventually
      (fun trajectory :
          HeterogeneousStochasticEpisodeBatchTrajectory mdp episodes =>
        HasSubgaussianMGF id
          (mdp.iidSampledCumulativeReturnDeviationVarianceProxy
            (episodes (n + 1)) rewardBound rewardVarianceProxy)
          (target trajectory))
      (ae (source.trajectoryMeasure.trim hmcond)) := by
    exact Filter.Eventually.of_forall fun trajectory => by
      let history := prefixMap trajectory
      let policy := source.successorPolicy n history
      have hbase :=
        source.rewardSource.iidStochasticTrajectoryFamilyMeasure_sampledCumulativeReturnDeviationSum_hasSubgaussianMGF
          policy initialState (episodes (n + 1)) rewardBound
          rewardVarianceProxy hrewardBound law
      have hid :=
        (HasSubgaussianMGF.id_map_iff
          (mdp.measurable_sampledCumulativeReturnDeviationSum
            policy (episodes (n + 1))).aemeasurable).2 hbase
      change HasSubgaussianMGF id
        (mdp.iidSampledCumulativeReturnDeviationVarianceProxy
          (episodes (n + 1)) rewardBound rewardVarianceProxy)
        (source.successorDeviationKernel n history)
      rw [source.successorDeviationKernel_apply n history]
      exact hid
  have hcondComap :=
    ConditionalExpectationReward.hasCondSubgaussianMGF_of_condExpKernel_map_eq
      (mOmega := MeasurableSpace.pi)
      source.trajectoryMeasure mcond hmcond X
      (mdp.iidSampledCumulativeReturnDeviationVarianceProxy
        (episodes (n + 1)) rewardBound rewardVarianceProxy)
      (source.measurable_successorSampledReturnDeviationAt n)
      target hkernel htarget
  have hcond :=
    ConditionalExpectationReward.hasCondSubgaussianMGF_congr_measurableSpace
      (mOmega := MeasurableSpace.pi)
      source.trajectoryMeasure mcond
      (Filtration.piLE
        (X := fun k : Nat => StochasticEpisodeBatch mdp (episodes k)) n)
      hmcond
      ((Filtration.piLE
        (X := fun k : Nat => StochasticEpisodeBatch mdp (episodes k))).le n)
      hspace.symm X
      (mdp.iidSampledCumulativeReturnDeviationVarianceProxy
        (episodes (n + 1)) rewardBound rewardVarianceProxy)
      hcondComap
  simpa [sampledReturnDeviationIncrement,
    sampledReturnDeviationPrefixIncrement,
    successorSampledReturnDeviationAt, X, prefixMap,
    Preorder.frestrictLe_apply, Preorder.frestrictLe₂_apply] using hcond

/-- Sum of coordinate-specific sampled-return variance proxies. -/
noncomputable def cumulativeSampledReturnDeviationVarianceProxy
    (mdp : MDP State Action) (episodes : Nat -> Nat) (rounds : Nat)
    (rewardBound rewardVarianceProxy : NNReal) : NNReal :=
  ∑ round ∈ Finset.range rounds,
    mdp.iidSampledCumulativeReturnDeviationVarianceProxy
      (episodes round) rewardBound rewardVarianceProxy

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The heterogeneous total proxy is positive under a positive batch schedule. -/
theorem cumulativeSampledReturnDeviationVarianceProxy_pos
    (mdp : MDP State Action) (episodes : Nat -> Nat) (rounds : Nat)
    (rewardBound rewardVarianceProxy : NNReal)
    (hrounds : 0 < rounds) (hepisodes : forall n, 0 < episodes n)
    (hhorizon : 0 < mdp.horizon)
    (hrewardVarianceProxy : 0 < rewardVarianceProxy) :
    0 < ((cumulativeSampledReturnDeviationVarianceProxy mdp episodes rounds
      rewardBound rewardVarianceProxy : NNReal) : Real) := by
  let cY : Nat -> NNReal := fun round =>
    mdp.iidSampledCumulativeReturnDeviationVarianceProxy
      (episodes round) rewardBound rewardVarianceProxy
  have hcoordinate : 0 <
      mdp.iidSampledCumulativeReturnDeviationVarianceProxy
        (episodes 0) rewardBound rewardVarianceProxy := by
    unfold MDP.iidSampledCumulativeReturnDeviationVarianceProxy
    have hepisodes0 : 0 < (episodes 0 : NNReal) := by
      exact_mod_cast hepisodes 0
    have hhorizonNN : 0 < (mdp.horizon : NNReal) := by
      exact_mod_cast hhorizon
    exact mul_pos hepisodes0
      (lt_of_lt_of_le (mul_pos hhorizonNN hrewardVarianceProxy)
        (le_add_of_nonneg_right (zero_le _)))
  have hcoordinate_le :
      mdp.iidSampledCumulativeReturnDeviationVarianceProxy
          (episodes 0) rewardBound rewardVarianceProxy <=
        cumulativeSampledReturnDeviationVarianceProxy mdp episodes rounds
          rewardBound rewardVarianceProxy := by
    have hsingle : cY 0 <= ∑ round ∈ Finset.range rounds, cY round :=
      Finset.single_le_sum (fun round _ => zero_le (cY round))
        (Finset.mem_range.mpr hrounds)
    simpa [cY, cumulativeSampledReturnDeviationVarianceProxy] using hsingle
  exact_mod_cast hcoordinate.trans_le hcoordinate_le

/-- Cumulative heterogeneous sampled-return deviation through `rounds`. -/
noncomputable def cumulativeSampledReturnDeviation
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat -> Nat}
    (source : HeterogeneousAdaptiveStochasticEpisodeBatchSource
      mdp initialState episodes) (rounds : Nat)
    (trajectory : HeterogeneousStochasticEpisodeBatchTrajectory mdp episodes) :
    Real :=
  ∑ round ∈ Finset.range rounds,
    source.sampledReturnDeviationIncrement round trajectory

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action] in
/-- Fixed-round two-sided tail on the heterogeneous causal law. -/
theorem trajectoryMeasure_cumulativeSampledReturnDeviation_abs_tail_le
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat -> Nat}
    [StandardBorelSpace State] [StandardBorelSpace Action]
    [forall n, StandardBorelSpace
      (HeterogeneousStochasticEpisodeBatchPrefix mdp episodes n)]
    [forall n, Nonempty
      (HeterogeneousStochasticEpisodeBatchPrefix mdp episodes n)]
    [forall n, StandardBorelSpace
      (StochasticEpisodeBatch mdp (episodes n))]
    [forall n, Nonempty (StochasticEpisodeBatch mdp (episodes n))]
    [StandardBorelSpace
      (HeterogeneousStochasticEpisodeBatchTrajectory mdp episodes)]
    (source : HeterogeneousAdaptiveStochasticEpisodeBatchSource
      mdp initialState episodes) (rounds : Nat)
    (rewardBound rewardVarianceProxy : NNReal)
    (hrewardBound : forall state action,
      |mdp.reward state action| <= (rewardBound : Real))
    (law : source.rewardSource.UniformSubgaussianRewardLaw
      rewardVarianceProxy)
    (htotal : 0 <
      ((cumulativeSampledReturnDeviationVarianceProxy mdp episodes rounds
        rewardBound rewardVarianceProxy : NNReal) : Real))
    (delta : Real) (hdelta : 0 < delta) (hdelta_le_one : delta <= 1) :
    source.trajectoryMeasure
        {trajectory |
          Concentration.subGaussianSumConfidenceRadius
              (cumulativeSampledReturnDeviationVarianceProxy mdp episodes rounds
                rewardBound rewardVarianceProxy) delta <=
            |source.cumulativeSampledReturnDeviation rounds trajectory|} <=
      ENNReal.ofReal delta := by
  let F := Filtration.piLE
    (X := fun n : Nat => StochasticEpisodeBatch mdp (episodes n))
  let cY : Nat -> NNReal := fun round =>
    mdp.iidSampledCumulativeReturnDeviationVarianceProxy
      (episodes round) rewardBound rewardVarianceProxy
  have hadapted : StronglyAdapted F
      source.sampledReturnDeviationIncrement := by
    simpa [F] using source.sampledReturnDeviationIncrement_stronglyAdapted_piLE
  have hzero : HasSubgaussianMGF
      (source.sampledReturnDeviationIncrement 0) (cY 0)
      source.trajectoryMeasure := by
    simpa [cY] using
      source.sampledReturnDeviationIncrement_zero_hasSubgaussianMGF
        rewardBound rewardVarianceProxy hrewardBound law
  have hsucc : forall i, i < rounds - 1 ->
      HasCondSubgaussianMGF
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

/-- Measurability contract for history-selected globally centered returns. -/
class GlobalReturnMeasurability
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat -> Nat}
    (source : HeterogeneousAdaptiveStochasticEpisodeBatchSource
      mdp initialState episodes) : Prop where
  measurable_successorGlobalReturnDeviation : forall n,
    Measurable fun pair :
        HeterogeneousStochasticEpisodeBatchPrefix mdp episodes n ×
          StochasticEpisodeBatch mdp (episodes (n + 1)) =>
      mdp.globalSampledCumulativeReturnDeviationSum
        (source.successorPolicy n pair.1) initialState
        (episodes (n + 1)) pair.2

/-- Dynamic globally centered return on a heterogeneous prefix/batch pair. -/
noncomputable def successorGlobalReturnDeviation
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat -> Nat}
    (source : HeterogeneousAdaptiveStochasticEpisodeBatchSource
      mdp initialState episodes) (n : Nat)
    (pair : HeterogeneousStochasticEpisodeBatchPrefix mdp episodes n ×
      StochasticEpisodeBatch mdp (episodes (n + 1))) : Real :=
  mdp.globalSampledCumulativeReturnDeviationSum
    (source.successorPolicy n pair.1) initialState (episodes (n + 1)) pair.2

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
theorem measurable_successorGlobalReturnDeviation
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat -> Nat}
    (source : HeterogeneousAdaptiveStochasticEpisodeBatchSource
      mdp initialState episodes) [source.GlobalReturnMeasurability] (n : Nat) :
    Measurable (source.successorGlobalReturnDeviation n) := by
  exact GlobalReturnMeasurability.measurable_successorGlobalReturnDeviation n

/-- Selected conditional kernel of the globally centered successor return. -/
noncomputable def successorGlobalReturnDeviationKernel
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat -> Nat}
    (source : HeterogeneousAdaptiveStochasticEpisodeBatchSource
      mdp initialState episodes) (n : Nat) :
    Kernel (HeterogeneousStochasticEpisodeBatchPrefix mdp episodes n) Real :=
  (Kernel.retainedInputKernel (source.batchKernel n)).map
    (source.successorGlobalReturnDeviation n)

instance instSuccessorGlobalReturnDeviationKernelIsMarkov
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat -> Nat}
    (source : HeterogeneousAdaptiveStochasticEpisodeBatchSource
      mdp initialState episodes) [source.GlobalReturnMeasurability] (n : Nat) :
    IsMarkovKernel (source.successorGlobalReturnDeviationKernel n) := by
  unfold successorGlobalReturnDeviationKernel
  exact Kernel.IsMarkovKernel.map _
    (source.measurable_successorGlobalReturnDeviation n)

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- Every global-return kernel fiber is the exact selected iid statistic law. -/
theorem successorGlobalReturnDeviationKernel_apply
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat -> Nat}
    (source : HeterogeneousAdaptiveStochasticEpisodeBatchSource
      mdp initialState episodes) [source.GlobalReturnMeasurability]
    (n : Nat)
    (history : HeterogeneousStochasticEpisodeBatchPrefix mdp episodes n) :
    source.successorGlobalReturnDeviationKernel n history =
      (source.rewardSource.iidStochasticTrajectoryFamilyMeasure
        (source.successorPolicy n history) initialState
        (episodes (n + 1))).map
          (mdp.globalSampledCumulativeReturnDeviationSum
            (source.successorPolicy n history) initialState
            (episodes (n + 1))) := by
  unfold successorGlobalReturnDeviationKernel
  rw [Kernel.map_apply
      (f := source.successorGlobalReturnDeviation n)
      (Kernel.retainedInputKernel (source.batchKernel n))
      (source.measurable_successorGlobalReturnDeviation n) history,
    Kernel.retainedInputKernel_apply]
  calc
    Measure.map (source.successorGlobalReturnDeviation n)
          (Measure.map (Prod.mk history) (source.batchKernel n history)) =
        Measure.map
          ((source.successorGlobalReturnDeviation n) ∘ Prod.mk history)
          (source.batchKernel n history) :=
      Measure.map_map
        (source.measurable_successorGlobalReturnDeviation n)
        (measurable_const.prodMk measurable_id)
    _ = (source.rewardSource.iidStochasticTrajectoryFamilyMeasure
          (source.successorPolicy n history) initialState
          (episodes (n + 1))).map
            (mdp.globalSampledCumulativeReturnDeviationSum
              (source.successorPolicy n history) initialState
              (episodes (n + 1))) := by
      rw [source.batchKernel_eq_iidStochasticTrajectoryFamilyMeasure]
      rfl

/-- Globally centered return evaluated at successor coordinate `n + 1`. -/
noncomputable def successorGlobalReturnDeviationAt
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat -> Nat}
    (source : HeterogeneousAdaptiveStochasticEpisodeBatchSource
      mdp initialState episodes) (n : Nat)
    (trajectory : HeterogeneousStochasticEpisodeBatchTrajectory mdp episodes) :
    Real :=
  source.successorGlobalReturnDeviation n
    (Preorder.frestrictLe n trajectory, trajectory (n + 1))

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
theorem measurable_successorGlobalReturnDeviationAt
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat -> Nat}
    (source : HeterogeneousAdaptiveStochasticEpisodeBatchSource
      mdp initialState episodes) [source.GlobalReturnMeasurability] (n : Nat) :
    Measurable (source.successorGlobalReturnDeviationAt n) := by
  exact (source.measurable_successorGlobalReturnDeviation n).comp
    ((Preorder.measurable_frestrictLe n).prodMk
      (measurable_pi_apply (n + 1)))

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- Dynamic conditional law of the globally centered successor return. -/
theorem trajectoryMeasure_condDistrib_successorGlobalReturnDeviationAt
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat -> Nat}
    (source : HeterogeneousAdaptiveStochasticEpisodeBatchSource
      mdp initialState episodes) [source.GlobalReturnMeasurability] (n : Nat)
    [StandardBorelSpace
      (HeterogeneousStochasticEpisodeBatchPrefix mdp episodes n)]
    [Nonempty (HeterogeneousStochasticEpisodeBatchPrefix mdp episodes n)]
    [StandardBorelSpace
      (StochasticEpisodeBatch mdp (episodes (n + 1)))]
    [Nonempty (StochasticEpisodeBatch mdp (episodes (n + 1)))] :
    condDistrib (source.successorGlobalReturnDeviationAt n)
        (Preorder.frestrictLe n) source.trajectoryMeasure =ᵐ[
          source.trajectoryMeasure.map (Preorder.frestrictLe n)]
      source.successorGlobalReturnDeviationKernel n := by
  exact Kernel.condDistrib_dynamic_map_ae_eq_of_pair_map_eq_compProd
    source.trajectoryMeasure
    (Preorder.frestrictLe n)
    (fun trajectory :
      HeterogeneousStochasticEpisodeBatchTrajectory mdp episodes =>
        trajectory (n + 1))
    (source.batchKernel n)
    (source.successorGlobalReturnDeviation n)
    (Preorder.measurable_frestrictLe n)
    (measurable_pi_apply (n + 1))
    (source.measurable_successorGlobalReturnDeviation n)
    (source.trajectoryMeasure_prefix_compProd n).symm

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action] in
/-- Trimmed conditional-expectation kernel form of the global-return law. -/
theorem condExpKernel_map_successorGlobalReturnDeviationAt_eq
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat -> Nat}
    (source : HeterogeneousAdaptiveStochasticEpisodeBatchSource
      mdp initialState episodes) [source.GlobalReturnMeasurability] (n : Nat)
    [StandardBorelSpace
      (HeterogeneousStochasticEpisodeBatchPrefix mdp episodes n)]
    [Nonempty (HeterogeneousStochasticEpisodeBatchPrefix mdp episodes n)]
    [StandardBorelSpace
      (StochasticEpisodeBatch mdp (episodes (n + 1)))]
    [Nonempty (StochasticEpisodeBatch mdp (episodes (n + 1)))]
    [StandardBorelSpace
      (HeterogeneousStochasticEpisodeBatchTrajectory mdp episodes)] :
    Filter.Eventually
      (fun trajectory :
          HeterogeneousStochasticEpisodeBatchTrajectory mdp episodes =>
        Measure.map (source.successorGlobalReturnDeviationAt n)
            (condExpKernel source.trajectoryMeasure
              ((inferInstance : MeasurableSpace
                (HeterogeneousStochasticEpisodeBatchPrefix mdp episodes n)).comap
                  (Preorder.frestrictLe n)) trajectory) =
          source.successorGlobalReturnDeviationKernel n
            (Preorder.frestrictLe n trajectory))
      (ae (source.trajectoryMeasure.trim
        (Preorder.measurable_frestrictLe n).comap_le)) := by
  exact
    ConditionalExpectationReward.condExpKernel_map_eq_of_condDistrib_ae_eq_real_trim
      source.trajectoryMeasure
      (source.successorGlobalReturnDeviationAt n)
      (Preorder.frestrictLe n)
      (source.measurable_successorGlobalReturnDeviationAt n)
      (Preorder.measurable_frestrictLe n)
      (source.successorGlobalReturnDeviationKernel n)
      (source.trajectoryMeasure_condDistrib_successorGlobalReturnDeviationAt n)

/-- Prefix process with coordinate zero uncharged and successors globally centered. -/
noncomputable def successorGlobalReturnPrefixIncrement
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat -> Nat}
    (source : HeterogeneousAdaptiveStochasticEpisodeBatchSource
      mdp initialState episodes) :
    (round : Nat) ->
      HeterogeneousStochasticEpisodeBatchPrefix mdp episodes round -> Real
  | 0, _history => 0
  | n + 1, history =>
      source.successorGlobalReturnDeviation n
        (Preorder.frestrictLe₂
          (π := fun k : Nat => StochasticEpisodeBatch mdp (episodes k))
          (Nat.le_succ n) history,
        history ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩)

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
theorem measurable_successorGlobalReturnPrefixIncrement
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat -> Nat}
    (source : HeterogeneousAdaptiveStochasticEpisodeBatchSource
      mdp initialState episodes) [source.GlobalReturnMeasurability]
    (round : Nat) :
    Measurable (source.successorGlobalReturnPrefixIncrement round) := by
  cases round with
  | zero =>
      simpa only [successorGlobalReturnPrefixIncrement] using
        (measurable_const : Measurable
          (fun _ : HeterogeneousStochasticEpisodeBatchPrefix mdp episodes 0 =>
            (0 : Real)))
  | succ n =>
      exact (source.measurable_successorGlobalReturnDeviation n).comp
        ((Preorder.measurable_frestrictLe₂
          (X := fun k : Nat => StochasticEpisodeBatch mdp (episodes k))
          (Nat.le_succ n)).prodMk
            (measurable_pi_apply
              (⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩ : Finset.Iic (n + 1))))

noncomputable def successorGlobalReturnIncrement
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat -> Nat}
    (source : HeterogeneousAdaptiveStochasticEpisodeBatchSource
      mdp initialState episodes) (round : Nat)
    (trajectory : HeterogeneousStochasticEpisodeBatchTrajectory mdp episodes) :
    Real :=
  source.successorGlobalReturnPrefixIncrement round
    (Preorder.frestrictLe round trajectory)

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
theorem successorGlobalReturnIncrement_stronglyAdapted_piLE
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat -> Nat}
    (source : HeterogeneousAdaptiveStochasticEpisodeBatchSource
      mdp initialState episodes) [source.GlobalReturnMeasurability] :
    StronglyAdapted
      (Filtration.piLE
        (X := fun n : Nat => StochasticEpisodeBatch mdp (episodes n)))
      source.successorGlobalReturnIncrement := by
  intro round
  rw [Filtration.piLE_eq_comap_frestrictLe]
  exact ((source.measurable_successorGlobalReturnPrefixIncrement round).comp
    (Measurable.of_comap_le le_rfl)).stronglyMeasurable

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action] in
/-- Every successor global-return coordinate has its selected conditional MGF. -/
theorem successorGlobalReturnIncrement_succ_hasCondSubgaussianMGF
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat -> Nat}
    [StandardBorelSpace State] [StandardBorelSpace Action]
    (source : HeterogeneousAdaptiveStochasticEpisodeBatchSource
      mdp initialState episodes) [source.GlobalReturnMeasurability] (n : Nat)
    [StandardBorelSpace
      (HeterogeneousStochasticEpisodeBatchPrefix mdp episodes n)]
    [Nonempty (HeterogeneousStochasticEpisodeBatchPrefix mdp episodes n)]
    [StandardBorelSpace
      (StochasticEpisodeBatch mdp (episodes (n + 1)))]
    [Nonempty (StochasticEpisodeBatch mdp (episodes (n + 1)))]
    [StandardBorelSpace
      (HeterogeneousStochasticEpisodeBatchTrajectory mdp episodes)]
    (rewardBound rewardVarianceProxy : NNReal)
    (hrewardBound : forall state action,
      |mdp.reward state action| <= (rewardBound : Real))
    (law : source.rewardSource.UniformSubgaussianRewardLaw
      rewardVarianceProxy) :
    HasCondSubgaussianMGF
      (Filtration.piLE
        (X := fun k : Nat => StochasticEpisodeBatch mdp (episodes k)) n)
      ((Filtration.piLE
        (X := fun k : Nat => StochasticEpisodeBatch mdp (episodes k))).le n)
      (source.successorGlobalReturnIncrement (n + 1))
      (mdp.iidGlobalSampledCumulativeReturnDeviationVarianceProxy
        (episodes (n + 1)) rewardBound rewardVarianceProxy)
      source.trajectoryMeasure := by
  let prefixMap :
      HeterogeneousStochasticEpisodeBatchTrajectory mdp episodes ->
        HeterogeneousStochasticEpisodeBatchPrefix mdp episodes n :=
    Preorder.frestrictLe n
  let X := source.successorGlobalReturnDeviationAt n
  let target : HeterogeneousStochasticEpisodeBatchTrajectory mdp episodes ->
      Measure Real :=
    fun trajectory =>
      source.successorGlobalReturnDeviationKernel n (prefixMap trajectory)
  let mcond : MeasurableSpace
      (HeterogeneousStochasticEpisodeBatchTrajectory mdp episodes) :=
    (inferInstance : MeasurableSpace
      (HeterogeneousStochasticEpisodeBatchPrefix mdp episodes n)).comap
        prefixMap
  have hmcond : mcond <= MeasurableSpace.pi := by
    simpa [mcond, prefixMap] using
      (Preorder.measurable_frestrictLe
        (X := fun k : Nat => StochasticEpisodeBatch mdp (episodes k)) n).comap_le
  have hspace :
      Filtration.piLE
          (X := fun k : Nat => StochasticEpisodeBatch mdp (episodes k)) n =
        mcond := by
    simpa [mcond, prefixMap] using
      (Filtration.piLE_eq_comap_frestrictLe
        (X := fun k : Nat => StochasticEpisodeBatch mdp (episodes k)) n)
  have hkernel : Filter.Eventually
      (fun trajectory :
          HeterogeneousStochasticEpisodeBatchTrajectory mdp episodes =>
        @Measure.map
            (HeterogeneousStochasticEpisodeBatchTrajectory mdp episodes) Real
            MeasurableSpace.pi inferInstance X
            ((@condExpKernel
              (HeterogeneousStochasticEpisodeBatchTrajectory mdp episodes)
              MeasurableSpace.pi _ source.trajectoryMeasure _ mcond)
                trajectory) =
          target trajectory)
      (ae (source.trajectoryMeasure.trim hmcond)) := by
    simpa [X, target, prefixMap, mcond] using
      source.condExpKernel_map_successorGlobalReturnDeviationAt_eq n
  have htarget : Filter.Eventually
      (fun trajectory :
          HeterogeneousStochasticEpisodeBatchTrajectory mdp episodes =>
        HasSubgaussianMGF id
          (mdp.iidGlobalSampledCumulativeReturnDeviationVarianceProxy
            (episodes (n + 1)) rewardBound rewardVarianceProxy)
          (target trajectory))
      (ae (source.trajectoryMeasure.trim hmcond)) := by
    exact Filter.Eventually.of_forall fun trajectory => by
      let history := prefixMap trajectory
      let policy := source.successorPolicy n history
      have hbase :=
        source.rewardSource.iidStochasticTrajectoryFamilyMeasure_globalSampledCumulativeReturnDeviationSum_hasSubgaussianMGF
          policy initialState (episodes (n + 1)) rewardBound
          rewardVarianceProxy hrewardBound law
      have hid :=
        (HasSubgaussianMGF.id_map_iff
          (mdp.measurable_globalSampledCumulativeReturnDeviationSum
            policy initialState (episodes (n + 1))).aemeasurable).2 hbase
      change HasSubgaussianMGF id
        (mdp.iidGlobalSampledCumulativeReturnDeviationVarianceProxy
          (episodes (n + 1)) rewardBound rewardVarianceProxy)
        (source.successorGlobalReturnDeviationKernel n history)
      rw [source.successorGlobalReturnDeviationKernel_apply n history]
      exact hid
  have hcondComap :=
    ConditionalExpectationReward.hasCondSubgaussianMGF_of_condExpKernel_map_eq
      (mOmega := MeasurableSpace.pi)
      source.trajectoryMeasure mcond hmcond X
      (mdp.iidGlobalSampledCumulativeReturnDeviationVarianceProxy
        (episodes (n + 1)) rewardBound rewardVarianceProxy)
      (source.measurable_successorGlobalReturnDeviationAt n)
      target hkernel htarget
  have hcond :=
    ConditionalExpectationReward.hasCondSubgaussianMGF_congr_measurableSpace
      (mOmega := MeasurableSpace.pi)
      source.trajectoryMeasure mcond
      (Filtration.piLE
        (X := fun k : Nat => StochasticEpisodeBatch mdp (episodes k)) n)
      hmcond
      ((Filtration.piLE
        (X := fun k : Nat => StochasticEpisodeBatch mdp (episodes k))).le n)
      hspace.symm X
      (mdp.iidGlobalSampledCumulativeReturnDeviationVarianceProxy
        (episodes (n + 1)) rewardBound rewardVarianceProxy)
      hcondComap
  simpa [successorGlobalReturnIncrement,
    successorGlobalReturnPrefixIncrement,
    successorGlobalReturnDeviationAt, X, prefixMap,
    Preorder.frestrictLe_apply, Preorder.frestrictLe₂_apply] using hcond

/-- Zero at coordinate zero plus heterogeneous global proxies at successors. -/
noncomputable def cumulativeSuccessorGlobalReturnVarianceProxy
    (mdp : MDP State Action) (episodes : Nat -> Nat) (rounds : Nat)
    (rewardBound rewardVarianceProxy : NNReal) : NNReal :=
  ∑ t ∈ Finset.range (rounds + 1),
    match t with
    | 0 => 0
    | _ + 1 =>
        mdp.iidGlobalSampledCumulativeReturnDeviationVarianceProxy
          (episodes t) rewardBound rewardVarianceProxy

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- Positive successor count and coordinate proxy imply a positive total proxy. -/
theorem cumulativeSuccessorGlobalReturnVarianceProxy_pos
    (mdp : MDP State Action) (episodes : Nat -> Nat) (rounds : Nat)
    (rewardBound rewardVarianceProxy : NNReal)
    (hrounds : 0 < rounds) (hepisodes : forall n, 0 < episodes n)
    (hhorizon : 0 < mdp.horizon)
    (hrewardVarianceProxy : 0 < rewardVarianceProxy) :
    0 < ((cumulativeSuccessorGlobalReturnVarianceProxy mdp episodes rounds
      rewardBound rewardVarianceProxy : NNReal) : Real) := by
  let cY : Nat -> NNReal := fun t =>
    match t with
    | 0 => 0
    | _ + 1 =>
        mdp.iidGlobalSampledCumulativeReturnDeviationVarianceProxy
          (episodes t) rewardBound rewardVarianceProxy
  have hsample : 0 <
      mdp.iidSampledCumulativeReturnDeviationVarianceProxy
        (episodes 1) rewardBound rewardVarianceProxy := by
    unfold MDP.iidSampledCumulativeReturnDeviationVarianceProxy
    have hepisodes1 : 0 < (episodes 1 : NNReal) := by
      exact_mod_cast hepisodes 1
    have hhorizonNN : 0 < (mdp.horizon : NNReal) := by
      exact_mod_cast hhorizon
    exact mul_pos hepisodes1
      (lt_of_lt_of_le (mul_pos hhorizonNN hrewardVarianceProxy)
        (le_add_of_nonneg_right (zero_le _)))
  have hcoordinate : 0 <
      mdp.iidGlobalSampledCumulativeReturnDeviationVarianceProxy
        (episodes 1) rewardBound rewardVarianceProxy := by
    unfold MDP.iidGlobalSampledCumulativeReturnDeviationVarianceProxy
    exact pow_pos
      (lt_of_lt_of_le (NNReal.sqrt_pos.2 hsample)
        (le_add_of_nonneg_right (zero_le _))) 2
  have hcoordinate_le : cY 1 <=
      ∑ t ∈ Finset.range (rounds + 1), cY t :=
    Finset.single_le_sum (fun t _ => zero_le (cY t))
      (Finset.mem_range.mpr (Nat.succ_lt_succ hrounds))
  have hpositive : 0 < ∑ t ∈ Finset.range (rounds + 1), cY t := by
    exact (show 0 < cY 1 by simpa [cY] using hcoordinate).trans_le
      hcoordinate_le
  exact_mod_cast (show 0 <
    cumulativeSuccessorGlobalReturnVarianceProxy mdp episodes rounds
      rewardBound rewardVarianceProxy by
        simpa [cY, cumulativeSuccessorGlobalReturnVarianceProxy] using hpositive)

/-- Cumulative globally centered deviation over successor coordinates only. -/
noncomputable def cumulativeSuccessorGlobalReturnDeviation
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat -> Nat}
    (source : HeterogeneousAdaptiveStochasticEpisodeBatchSource
      mdp initialState episodes) (rounds : Nat)
    (trajectory : HeterogeneousStochasticEpisodeBatchTrajectory mdp episodes) :
    Real :=
  ∑ t ∈ Finset.range (rounds + 1),
    source.successorGlobalReturnIncrement t trajectory

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action] in
/-- Fixed-round successor-only globally centered two-sided tail. -/
theorem trajectoryMeasure_cumulativeSuccessorGlobalReturnDeviation_abs_tail_le
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat -> Nat}
    [StandardBorelSpace State] [StandardBorelSpace Action]
    [forall n, StandardBorelSpace
      (HeterogeneousStochasticEpisodeBatchPrefix mdp episodes n)]
    [forall n, Nonempty
      (HeterogeneousStochasticEpisodeBatchPrefix mdp episodes n)]
    [forall n, StandardBorelSpace
      (StochasticEpisodeBatch mdp (episodes n))]
    [forall n, Nonempty (StochasticEpisodeBatch mdp (episodes n))]
    [StandardBorelSpace
      (HeterogeneousStochasticEpisodeBatchTrajectory mdp episodes)]
    (source : HeterogeneousAdaptiveStochasticEpisodeBatchSource
      mdp initialState episodes) [source.GlobalReturnMeasurability]
    (rounds : Nat) (rewardBound rewardVarianceProxy : NNReal)
    (hrewardBound : forall state action,
      |mdp.reward state action| <= (rewardBound : Real))
    (law : source.rewardSource.UniformSubgaussianRewardLaw
      rewardVarianceProxy)
    (htotal : 0 <
      ((cumulativeSuccessorGlobalReturnVarianceProxy mdp episodes rounds
        rewardBound rewardVarianceProxy : NNReal) : Real))
    (delta : Real) (hdelta : 0 < delta) (hdelta_le_one : delta <= 1) :
    source.trajectoryMeasure
        {trajectory |
          Concentration.subGaussianSumConfidenceRadius
              (cumulativeSuccessorGlobalReturnVarianceProxy mdp episodes rounds
                rewardBound rewardVarianceProxy) delta <=
            |source.cumulativeSuccessorGlobalReturnDeviation
              rounds trajectory|} <=
      ENNReal.ofReal delta := by
  let F := Filtration.piLE
    (X := fun n : Nat => StochasticEpisodeBatch mdp (episodes n))
  let cY : Nat -> NNReal := fun t =>
    match t with
    | 0 => 0
    | _ + 1 =>
        mdp.iidGlobalSampledCumulativeReturnDeviationVarianceProxy
          (episodes t) rewardBound rewardVarianceProxy
  have hadapted : StronglyAdapted F
      source.successorGlobalReturnIncrement := by
    simpa [F] using source.successorGlobalReturnIncrement_stronglyAdapted_piLE
  have hzero : HasSubgaussianMGF
      (source.successorGlobalReturnIncrement 0) (cY 0)
      source.trajectoryMeasure := by
    change HasSubgaussianMGF (fun _ => 0) 0 source.trajectoryMeasure
    exact HasSubgaussianMGF.fun_zero
  have hsucc : forall i, i < (rounds + 1) - 1 ->
      HasCondSubgaussianMGF
        (F i) (F.le i) (source.successorGlobalReturnIncrement (i + 1))
        (cY (i + 1)) source.trajectoryMeasure := by
    intro i _hi
    simpa [F, cY] using
      source.successorGlobalReturnIncrement_succ_hasCondSubgaussianMGF
        i rewardBound rewardVarianceProxy hrewardBound law
  have hvariance :
      0 < ((((Finset.range (rounds + 1)).sum cY : NNReal) : Real)) := by
    simpa [cY, cumulativeSuccessorGlobalReturnVarianceProxy] using htotal
  simpa [cumulativeSuccessorGlobalReturnVarianceProxy,
    cumulativeSuccessorGlobalReturnDeviation, cY] using
    (Concentration.condSubGaussian_sum_abs_tail_ennreal_delta_of_stronglyAdapted
      hadapted hzero (rounds + 1) hsucc hvariance
      delta hdelta hdelta_le_one)

end HeterogeneousAdaptiveStochasticEpisodeBatchSource

namespace AdaptiveStochasticSampledEmpiricalOptimisticSource

/-- The measurable latest-batch selector closes global-return measurability. -/
noncomputable instance instHeterogeneousExploratorySourceGlobalReturnMeasurability
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState] (episodes : Nat -> Nat)
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (rewardBudget transitionBudget : Nat -> Real)
    (explorationRate : Nat -> NNReal)
    (hexplorationRate : forall n, explorationRate n <= 1) :
    (heterogeneousExploratorySource mdp initialState episodes rewardSource
      initialTable defaultState rewardBudget transitionBudget explorationRate
        hexplorationRate).GlobalReturnMeasurability where
  measurable_successorGlobalReturnDeviation n := by
    exact
      AdaptiveStochasticEmpiricalOptimisticSource.measurable_selectedExploratoryGlobalReturnDeviation
        (heterogeneousSuccessorTable defaultState rewardBudget transitionBudget n)
        (measurable_heterogeneousSuccessorTable
          defaultState rewardBudget transitionBudget n)
        (explorationRate (n + 1)) (hexplorationRate (n + 1))

/-- Concrete self-consistent schedule wrapper for the heterogeneous tail. -/
theorem selfConsistentScheduledCausalSource_trajectoryMeasure_cumulativeSampledReturnDeviation_abs_tail_le
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace State] [StandardBorelSpace Action]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (rounds : Nat)
    (rewardBound rewardVarianceProxy : NNReal)
    (hrewardBound : forall state action,
      |mdp.reward state action| <= (rewardBound : Real))
    (law : rewardSource.UniformSubgaussianRewardLaw rewardVarianceProxy)
    (hrounds : 0 < rounds) (hhorizon : 0 < mdp.horizon)
    (hrewardVarianceProxy : 0 < rewardVarianceProxy)
    (delta : Real) (hdelta : 0 < delta) (hdelta_le_one : delta <= 1) :
    let source := selfConsistentScheduledCausalSource mdp initialState
      rewardSource initialTable defaultState varianceProxy baseVisitFloor
    source.trajectoryMeasure
        {trajectory |
          Concentration.subGaussianSumConfidenceRadius
              (HeterogeneousAdaptiveStochasticEpisodeBatchSource.cumulativeSampledReturnDeviationVarianceProxy
                mdp
                (fun n =>
                  AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
                    mdp varianceProxy baseVisitFloor n)
                rounds rewardBound rewardVarianceProxy) delta <=
            |source.cumulativeSampledReturnDeviation rounds trajectory|} <=
      ENNReal.ofReal delta := by
  dsimp only
  have htotal :=
    HeterogeneousAdaptiveStochasticEpisodeBatchSource.cumulativeSampledReturnDeviationVarianceProxy_pos
      mdp
      (fun n =>
        AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
          mdp varianceProxy baseVisitFloor n)
      rounds rewardBound rewardVarianceProxy hrounds
      (fun n =>
        AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes_pos
          mdp varianceProxy baseVisitFloor n)
      hhorizon hrewardVarianceProxy
  exact
    (selfConsistentScheduledCausalSource mdp initialState rewardSource
      initialTable defaultState varianceProxy baseVisitFloor).trajectoryMeasure_cumulativeSampledReturnDeviation_abs_tail_le
        rounds rewardBound rewardVarianceProxy hrewardBound law htotal delta
          hdelta hdelta_le_one

/-- Self-consistent successor-only globally centered heterogeneous tail. -/
theorem selfConsistentScheduledCausalSource_trajectoryMeasure_cumulativeSuccessorGlobalReturnDeviation_abs_tail_le
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace State] [StandardBorelSpace Action]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (rounds : Nat)
    (rewardBound rewardVarianceProxy : NNReal)
    (hrewardBound : forall state action,
      |mdp.reward state action| <= (rewardBound : Real))
    (law : rewardSource.UniformSubgaussianRewardLaw rewardVarianceProxy)
    (hrounds : 0 < rounds) (hhorizon : 0 < mdp.horizon)
    (hrewardVarianceProxy : 0 < rewardVarianceProxy)
    (delta : Real) (hdelta : 0 < delta) (hdelta_le_one : delta <= 1) :
    let source := selfConsistentScheduledCausalSource mdp initialState
      rewardSource initialTable defaultState varianceProxy baseVisitFloor
    source.trajectoryMeasure
        {trajectory |
          Concentration.subGaussianSumConfidenceRadius
              (HeterogeneousAdaptiveStochasticEpisodeBatchSource.cumulativeSuccessorGlobalReturnVarianceProxy
                mdp
                (fun n =>
                  AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
                    mdp varianceProxy baseVisitFloor n)
                rounds rewardBound rewardVarianceProxy) delta <=
            |source.cumulativeSuccessorGlobalReturnDeviation
              rounds trajectory|} <=
      ENNReal.ofReal delta := by
  dsimp only
  let source := selfConsistentScheduledCausalSource mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor
  letI : source.GlobalReturnMeasurability := by
    dsimp [source, selfConsistentScheduledCausalSource]
    infer_instance
  have htotal :=
    HeterogeneousAdaptiveStochasticEpisodeBatchSource.cumulativeSuccessorGlobalReturnVarianceProxy_pos
      mdp
      (fun n =>
        AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
          mdp varianceProxy baseVisitFloor n)
      rounds rewardBound rewardVarianceProxy hrounds
      (fun n =>
        AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes_pos
          mdp varianceProxy baseVisitFloor n)
      hhorizon hrewardVarianceProxy
  exact
    source.trajectoryMeasure_cumulativeSuccessorGlobalReturnDeviation_abs_tail_le
        rounds rewardBound rewardVarianceProxy hrewardBound law htotal delta
          hdelta hdelta_le_one

end AdaptiveStochasticSampledEmpiricalOptimisticSource

end BanditRLProof.FiniteHorizonRL
