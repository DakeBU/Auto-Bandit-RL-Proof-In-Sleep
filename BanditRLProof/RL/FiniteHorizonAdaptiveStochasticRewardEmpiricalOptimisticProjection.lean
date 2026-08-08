import BanditRLProof.RL.FiniteHorizonAdaptiveEmpiricalOptimisticConfidence
import BanditRLProof.RL.FiniteHorizonAdaptiveStochasticRewardTotalReturnConcentration
import BanditRLProof.RL.FiniteHorizonStochasticRewardErasureLaw
import BanditRLProof.RewardTraceLaw

/-!
# Adaptive stochastic-reward empirical-optimistic projection

This module lifts the existing known-reward exploratory empirical-transition
source to stochastic rewards.  Its policy selector reads only the complete
known-reward projection of the observed stochastic prefix.  The resulting
adaptive stochastic trajectory therefore maps exactly to the deterministic
source trajectory, so the compiled count-confidence, optimism, and recommended
expected-regret terminal can be pulled back without estimating sampled rewards.

The projection preserves every action and next-state coordinate and reinstates
only the deterministic mean reward `mdp.reward`.  No realized behavior-regret
or stochastic reward-confidence claim is made here.
-/

open MeasureTheory
open scoped ENNReal ProbabilityTheory

universe u v

namespace BanditRLProof
namespace FiniteHorizonRL

namespace ProbabilityTheory

/--
Map both coordinates of a measure composition product when the base measure
and every kernel fiber have the prescribed mapped laws.
-/
theorem measure_compProd_map_prodMap_of_map_eq
    {Alpha Alpha' Beta Beta' : Type*}
    [MeasurableSpace Alpha] [MeasurableSpace Alpha']
    [MeasurableSpace Beta] [MeasurableSpace Beta']
    (mu : Measure Alpha) [IsProbabilityMeasure mu]
    (kappa : ProbabilityTheory.Kernel Alpha Beta)
      [ProbabilityTheory.IsMarkovKernel kappa]
    (mu' : Measure Alpha') [IsProbabilityMeasure mu']
    (kappa' : ProbabilityTheory.Kernel Alpha' Beta')
      [ProbabilityTheory.IsMarkovKernel kappa']
    (f : Alpha -> Alpha') (hf : Measurable f)
    (g : Beta -> Beta') (hg : Measurable g)
    (hmu : mu.map f = mu')
    (hkappa : forall alpha, (kappa alpha).map g = kappa' (f alpha)) :
    (mu ⊗ₘ kappa).map (Prod.map f g) = mu' ⊗ₘ kappa' := by
  apply Measure.ext_prod
  intro alphaSet betaSet halphaSet hbetaSet
  have hprodMap : Measurable (Prod.map f g) := hf.prodMap hg
  rw [Measure.map_apply hprodMap (halphaSet.prod hbetaSet)]
  have hpreimage :
      Prod.map f g ⁻¹' (alphaSet ×ˢ betaSet) =
        (f ⁻¹' alphaSet) ×ˢ (g ⁻¹' betaSet) := by
    ext pair
    simp
  rw [hpreimage, Measure.compProd_apply_prod (halphaSet.preimage hf)
    (hbetaSet.preimage hg)]
  rw [Measure.compProd_apply_prod halphaSet hbetaSet]
  have hfiber (alpha : Alpha) :
      kappa alpha (g ⁻¹' betaSet) = kappa' (f alpha) betaSet := by
    have h := congrArg (fun nu : Measure Beta' => nu betaSet) (hkappa alpha)
    simpa [Measure.map_apply hg hbetaSet] using h
  simp_rw [hfiber]
  let q : Alpha' -> ENNReal := fun alpha => kappa' alpha betaSet
  have hq : Measurable q := kappa'.measurable_coe hbetaSet
  change
    (∫⁻ alpha in f ⁻¹' alphaSet, q (f alpha) ∂mu) =
      ∫⁻ alpha in alphaSet, q alpha ∂mu'
  rw [← MeasureTheory.setLIntegral_map halphaSet hq hf]
  rw [hmu]

end ProbabilityTheory

variable {State : Type u} {Action : Type v}
    [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action]
    [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action]

namespace MDP.MeanCompatibleRewardKernel

variable {mdp : MDP State Action}

/-- Project one stochastic batch to the existing known-mean empirical batch. -/
def knownRewardEpisodeBatch
    (episodes : Nat) (batch : StochasticEpisodeBatch mdp episodes) :
    EpisodeBatch mdp episodes :=
  knownRewardEpisodeBatchOfStochasticTrajectories
    (mdp := mdp) episodes batch

omit [DecidableEq State] [DecidableEq Action]
    [Nonempty State] [Nonempty Action] in
/-- The stochastic-batch known-reward projection is measurable. -/
theorem measurable_knownRewardEpisodeBatch (episodes : Nat) :
    Measurable (knownRewardEpisodeBatch (mdp := mdp) episodes) :=
  measurable_knownRewardEpisodeBatchOfStochasticTrajectories episodes

/-- Project every coordinate of a finite stochastic batch prefix. -/
def knownRewardEpisodeBatchPrefix
    (episodes n : Nat) (history : StochasticEpisodeBatchPrefix mdp episodes n) :
    EpisodeBatchPrefix mdp episodes n :=
  fun coordinate => knownRewardEpisodeBatch episodes (history coordinate)

omit [DecidableEq State] [DecidableEq Action]
    [Nonempty State] [Nonempty Action] in
/-- The coordinatewise known-reward prefix projection is measurable. -/
theorem measurable_knownRewardEpisodeBatchPrefix (episodes n : Nat) :
    Measurable (knownRewardEpisodeBatchPrefix (mdp := mdp) episodes n) := by
  apply measurable_pi_lambda
  intro coordinate
  exact (measurable_knownRewardEpisodeBatch episodes).comp
    (measurable_pi_apply coordinate)

/-- Project every coordinate of an infinite stochastic batch trajectory. -/
def knownRewardEpisodeBatchTrajectory
    (episodes : Nat) (trajectory : StochasticEpisodeBatchTrajectory mdp episodes) :
    EpisodeBatchTrajectory mdp episodes :=
  fun round => knownRewardEpisodeBatch episodes (trajectory round)

omit [DecidableEq State] [DecidableEq Action]
    [Nonempty State] [Nonempty Action] in
/-- The coordinatewise complete known-reward trajectory projection is measurable. -/
theorem measurable_knownRewardEpisodeBatchTrajectory (episodes : Nat) :
    Measurable (knownRewardEpisodeBatchTrajectory (mdp := mdp) episodes) := by
  apply measurable_pi_lambda
  intro round
  exact (measurable_knownRewardEpisodeBatch episodes).comp
    (measurable_pi_apply round)

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- Projection commutes with restricting a complete trajectory to a prefix. -/
@[simp]
theorem knownRewardEpisodeBatchPrefix_frestrictLe
    (episodes n : Nat) (trajectory : StochasticEpisodeBatchTrajectory mdp episodes) :
    knownRewardEpisodeBatchPrefix episodes n (Preorder.frestrictLe n trajectory) =
      Preorder.frestrictLe n (knownRewardEpisodeBatchTrajectory episodes trajectory) := by
  rfl

end MDP.MeanCompatibleRewardKernel

namespace DeterministicMarkovPolicyTable

/-- Stochastic iid episode-batch law indexed by an exploratory policy table. -/
noncomputable def exploratoryIIDStochasticEpisodeBatchKernel
    {mdp : MDP State Action}
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (episodes : Nat) (explorationRate : NNReal)
    (hexplorationRate : explorationRate <= 1) :
    ProbabilityTheory.Kernel (DeterministicMarkovPolicyTable mdp)
      (StochasticEpisodeBatch mdp episodes) :=
  ProbabilityTheory.Kernel.ofFunOfCountable fun table =>
    rewardSource.iidStochasticTrajectoryFamilyMeasure
      (table.exploratoryPolicy explorationRate hexplorationRate)
      initialState episodes

omit [DecidableEq State] [DecidableEq Action] [Nonempty State] in
@[simp]
theorem exploratoryIIDStochasticEpisodeBatchKernel_apply
    {mdp : MDP State Action}
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (episodes : Nat) (explorationRate : NNReal)
    (hexplorationRate : explorationRate <= 1)
    (table : DeterministicMarkovPolicyTable mdp) :
    exploratoryIIDStochasticEpisodeBatchKernel rewardSource initialState episodes
        explorationRate hexplorationRate table =
      rewardSource.iidStochasticTrajectoryFamilyMeasure
        (table.exploratoryPolicy explorationRate hexplorationRate)
        initialState episodes :=
  rfl

instance instExploratoryIIDStochasticEpisodeBatchKernelIsMarkov
    {mdp : MDP State Action}
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (episodes : Nat) (explorationRate : NNReal)
    (hexplorationRate : explorationRate <= 1) :
    ProbabilityTheory.IsMarkovKernel
      (exploratoryIIDStochasticEpisodeBatchKernel rewardSource initialState episodes
        explorationRate hexplorationRate) where
  isProbabilityMeasure table := by
    rw [exploratoryIIDStochasticEpisodeBatchKernel_apply]
    infer_instance

end DeterministicMarkovPolicyTable

namespace AdaptiveStochasticEmpiricalOptimisticSource

omit [Nonempty State] in
/--
A finite table selector and its batch statistic form a measurable dynamic
sampled-return deviation.  This discharges the regularity field required by
`AdaptiveStochasticEpisodeBatchSource` without constraining sampled rewards.
-/
theorem measurable_selectedExploratorySampledReturnDeviation
    {mdp : MDP State Action} {episodes : Nat}
    {History : Type*} [MeasurableSpace History]
    (selector : History -> DeterministicMarkovPolicyTable mdp)
    (hselector : Measurable selector)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1) :
    Measurable fun pair : History × StochasticEpisodeBatch mdp episodes =>
      mdp.sampledCumulativeReturnDeviationSum
        ((selector pair.1).exploratoryPolicy explorationRate hexplorationRate)
        episodes pair.2 := by
  classical
  let statistic := fun table : DeterministicMarkovPolicyTable mdp =>
    mdp.sampledCumulativeReturnDeviationSum
      (table.exploratoryPolicy explorationRate hexplorationRate) episodes
  have hrepresentation :
      (fun pair : History × StochasticEpisodeBatch mdp episodes =>
        mdp.sampledCumulativeReturnDeviationSum
          ((selector pair.1).exploratoryPolicy explorationRate hexplorationRate)
          episodes pair.2) =
        fun pair => ∑ table : DeterministicMarkovPolicyTable mdp,
          if selector pair.1 = table then statistic table pair.2 else 0 := by
    funext pair
    simp [statistic]
  rw [hrepresentation]
  exact Finset.measurable_sum Finset.univ fun table _ =>
    Measurable.ite
      ((hselector.comp measurable_fst) (measurableSet_singleton table))
      ((mdp.measurable_sampledCumulativeReturnDeviationSum
        (table.exploratoryPolicy explorationRate hexplorationRate) episodes).comp
          measurable_snd)
      measurable_const

/--
Concrete stochastic-reward lift of the deterministic exploratory empirical
optimistic source.  Every policy update factors through known-reward history.
-/
noncomputable def exploratorySource
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState] (episodes : Nat)
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (transitionBonus : Real)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1) :
    AdaptiveStochasticEpisodeBatchSource mdp initialState episodes where
  rewardSource := rewardSource
  initialPolicy :=
    initialTable.exploratoryPolicy explorationRate hexplorationRate
  successorPolicy n history :=
    (AdaptiveEmpiricalOptimisticSource.successorTable defaultState
      transitionBonus n
      (MDP.MeanCompatibleRewardKernel.knownRewardEpisodeBatchPrefix
        (mdp := mdp) episodes n history)).exploratoryPolicy
        explorationRate hexplorationRate
  batchKernel n :=
    (DeterministicMarkovPolicyTable.exploratoryIIDStochasticEpisodeBatchKernel
      rewardSource initialState episodes explorationRate hexplorationRate).comap
        (fun history =>
          AdaptiveEmpiricalOptimisticSource.successorTable defaultState
            transitionBonus n
            (MDP.MeanCompatibleRewardKernel.knownRewardEpisodeBatchPrefix
              (mdp := mdp) episodes n history))
        ((AdaptiveEmpiricalOptimisticSource.measurable_successorTable
          defaultState transitionBonus n).comp
            (MDP.MeanCompatibleRewardKernel.measurable_knownRewardEpisodeBatchPrefix
              (mdp := mdp) episodes n))
  batchKernel_isMarkov n := by
    exact ProbabilityTheory.Kernel.IsMarkovKernel.comap _
      ((AdaptiveEmpiricalOptimisticSource.measurable_successorTable
        defaultState transitionBonus n).comp
          (MDP.MeanCompatibleRewardKernel.measurable_knownRewardEpisodeBatchPrefix
            (mdp := mdp) episodes n))
  batchKernel_eq_iidStochasticTrajectoryFamilyMeasure n history := by
    rw [ProbabilityTheory.Kernel.comap_apply]
    rfl
  measurable_successorSampledReturnDeviation n := by
    exact measurable_selectedExploratorySampledReturnDeviation
      (fun history =>
        AdaptiveEmpiricalOptimisticSource.successorTable defaultState
          transitionBonus n
          (MDP.MeanCompatibleRewardKernel.knownRewardEpisodeBatchPrefix
            (mdp := mdp) episodes n history))
      ((AdaptiveEmpiricalOptimisticSource.measurable_successorTable
        defaultState transitionBonus n).comp
          (MDP.MeanCompatibleRewardKernel.measurable_knownRewardEpisodeBatchPrefix
            (mdp := mdp) episodes n))
      explorationRate hexplorationRate

omit [Nonempty State] in
/-- The stochastic and deterministic initial policies agree definitionally. -/
theorem exploratorySource_initialPolicy
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (transitionBonus : Real)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1) :
    (exploratorySource mdp initialState episodes rewardSource initialTable
      defaultState transitionBonus explorationRate hexplorationRate).initialPolicy =
      (AdaptiveEmpiricalOptimisticSource.exploratorySource mdp initialState episodes
        initialTable defaultState transitionBonus explorationRate
          hexplorationRate).initialPolicy := by
  simp only [exploratorySource,
    AdaptiveEmpiricalOptimisticSource.exploratorySource]

omit [Nonempty State] in
/-- The stochastic successor policy is selected from the projected prefix. -/
theorem exploratorySource_successorPolicy
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (transitionBonus : Real)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1)
    (n : Nat) (history : StochasticEpisodeBatchPrefix mdp episodes n) :
    (exploratorySource mdp initialState episodes rewardSource initialTable
      defaultState transitionBonus explorationRate hexplorationRate).successorPolicy
        n history =
      (AdaptiveEmpiricalOptimisticSource.exploratorySource mdp initialState episodes
        initialTable defaultState transitionBonus explorationRate
          hexplorationRate).successorPolicy n
            (MDP.MeanCompatibleRewardKernel.knownRewardEpisodeBatchPrefix
              (mdp := mdp) episodes n history) := by
  simp only [exploratorySource,
    AdaptiveEmpiricalOptimisticSource.exploratorySource]

omit [Nonempty State] in
/-- The initial stochastic batch maps to the deterministic exploratory batch. -/
theorem exploratorySource_initialBatch_map_knownRewardEpisodeBatch
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (transitionBonus : Real)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1) :
    (rewardSource.iidStochasticTrajectoryFamilyMeasure
      (exploratorySource mdp initialState episodes rewardSource initialTable
        defaultState transitionBonus explorationRate
          hexplorationRate).initialPolicy initialState episodes).map
        (MDP.MeanCompatibleRewardKernel.knownRewardEpisodeBatch
          (mdp := mdp) episodes) =
      (AdaptiveEmpiricalOptimisticSource.exploratorySource mdp initialState episodes
        initialTable defaultState transitionBonus explorationRate
          hexplorationRate).initialPolicy.iidEpisodeBatchMeasure
            initialState episodes := by
  rw [exploratorySource_initialPolicy rewardSource initialTable defaultState
    transitionBonus explorationRate hexplorationRate]
  exact
    rewardSource.iidStochasticTrajectoryFamilyMeasure_map_knownRewardEpisodeBatch_eq_iidEpisodeBatchMeasure
      _ initialState episodes

omit [Nonempty State] in
/-- Every selected stochastic successor batch maps to its deterministic fiber. -/
theorem exploratorySource_batchKernel_map_knownRewardEpisodeBatch
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (transitionBonus : Real)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1)
    (n : Nat) (history : StochasticEpisodeBatchPrefix mdp episodes n) :
    ((exploratorySource mdp initialState episodes rewardSource initialTable
      defaultState transitionBonus explorationRate hexplorationRate).batchKernel
        n history).map
          (MDP.MeanCompatibleRewardKernel.knownRewardEpisodeBatch
            (mdp := mdp) episodes) =
      (AdaptiveEmpiricalOptimisticSource.exploratorySource mdp initialState episodes
        initialTable defaultState transitionBonus explorationRate
          hexplorationRate).batchKernel n
            (MDP.MeanCompatibleRewardKernel.knownRewardEpisodeBatchPrefix
              (mdp := mdp) episodes n history) := by
  let stochasticSource := exploratorySource mdp initialState episodes rewardSource
    initialTable defaultState transitionBonus explorationRate hexplorationRate
  let deterministicSource :=
    AdaptiveEmpiricalOptimisticSource.exploratorySource mdp initialState episodes
      initialTable defaultState transitionBonus explorationRate hexplorationRate
  rw [stochasticSource.batchKernel_eq_iidStochasticTrajectoryFamilyMeasure]
  rw [deterministicSource.batchKernel_eq_iidEpisodeBatchMeasure]
  have hpolicy :
      stochasticSource.successorPolicy n history =
        deterministicSource.successorPolicy n
          (MDP.MeanCompatibleRewardKernel.knownRewardEpisodeBatchPrefix
            (mdp := mdp) episodes n history) :=
    exploratorySource_successorPolicy rewardSource initialTable defaultState
      transitionBonus explorationRate hexplorationRate n history
  rw [hpolicy]
  exact
    rewardSource.iidStochasticTrajectoryFamilyMeasure_map_knownRewardEpisodeBatch_eq_iidEpisodeBatchMeasure
      _ initialState episodes

omit [Nonempty State] in
/--
After projecting both coordinates, every stochastic prefix/next-batch joint law
is the projected-prefix measure composed with the deterministic source kernel.
-/
theorem exploratorySource_trajectoryMeasure_map_projectedPrefix_next_eq_compProd
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (transitionBonus : Real)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1)
    (n : Nat) :
    let stochasticSource := exploratorySource mdp initialState episodes rewardSource
      initialTable defaultState transitionBonus explorationRate hexplorationRate
    let deterministicSource :=
      AdaptiveEmpiricalOptimisticSource.exploratorySource mdp initialState episodes
        initialTable defaultState transitionBonus explorationRate hexplorationRate
    stochasticSource.trajectoryMeasure.map
        (fun trajectory =>
          (MDP.MeanCompatibleRewardKernel.knownRewardEpisodeBatchPrefix
              (mdp := mdp) episodes n (Preorder.frestrictLe n trajectory),
            MDP.MeanCompatibleRewardKernel.knownRewardEpisodeBatch
              (mdp := mdp) episodes (trajectory (n + 1)))) =
      stochasticSource.trajectoryMeasure.map
          (fun trajectory =>
            MDP.MeanCompatibleRewardKernel.knownRewardEpisodeBatchPrefix
              (mdp := mdp) episodes n (Preorder.frestrictLe n trajectory)) ⊗ₘ
        deterministicSource.batchKernel n := by
  dsimp only
  let stochasticSource := exploratorySource mdp initialState episodes rewardSource
    initialTable defaultState transitionBonus explorationRate hexplorationRate
  let deterministicSource :=
    AdaptiveEmpiricalOptimisticSource.exploratorySource mdp initialState episodes
      initialTable defaultState transitionBonus explorationRate hexplorationRate
  let prefixProjection :=
    MDP.MeanCompatibleRewardKernel.knownRewardEpisodeBatchPrefix
      (mdp := mdp) episodes n
  let batchProjection :=
    MDP.MeanCompatibleRewardKernel.knownRewardEpisodeBatch
      (mdp := mdp) episodes
  let projectedPrefix := fun trajectory : StochasticEpisodeBatchTrajectory mdp episodes =>
    prefixProjection (Preorder.frestrictLe n trajectory)
  let projectedPair := fun trajectory : StochasticEpisodeBatchTrajectory mdp episodes =>
    (projectedPrefix trajectory, batchProjection (trajectory (n + 1)))
  let originalPair := fun trajectory : StochasticEpisodeBatchTrajectory mdp episodes =>
    (Preorder.frestrictLe n trajectory, trajectory (n + 1))
  have hprefixProjection : Measurable prefixProjection :=
    MDP.MeanCompatibleRewardKernel.measurable_knownRewardEpisodeBatchPrefix
      (mdp := mdp) episodes n
  have hbatchProjection : Measurable batchProjection :=
    MDP.MeanCompatibleRewardKernel.measurable_knownRewardEpisodeBatch
      (mdp := mdp) episodes
  have hrestrict : Measurable
      (Preorder.frestrictLe n : StochasticEpisodeBatchTrajectory mdp episodes ->
        StochasticEpisodeBatchPrefix mdp episodes n) :=
    Preorder.measurable_frestrictLe n
  have hprojectedPrefix : Measurable projectedPrefix :=
    hprefixProjection.comp hrestrict
  have horiginalPair : Measurable originalPair :=
    hrestrict.prodMk (measurable_pi_apply (n + 1))
  have hprodMap : Measurable (Prod.map prefixProjection batchProjection) :=
    hprefixProjection.prodMap hbatchProjection
  have hbaseMap :
      (stochasticSource.trajectoryMeasure.map (Preorder.frestrictLe n)).map
          prefixProjection =
        stochasticSource.trajectoryMeasure.map projectedPrefix := by
    rw [Measure.map_map hprefixProjection hrestrict]
    rfl
  letI : IsProbabilityMeasure
      (stochasticSource.trajectoryMeasure.map (Preorder.frestrictLe n)) :=
    Measure.isProbabilityMeasure_map hrestrict.aemeasurable
  letI : IsProbabilityMeasure
      (stochasticSource.trajectoryMeasure.map projectedPrefix) :=
    Measure.isProbabilityMeasure_map hprojectedPrefix.aemeasurable
  have hcompProdMap :
      ((stochasticSource.trajectoryMeasure.map (Preorder.frestrictLe n)) ⊗ₘ
          stochasticSource.batchKernel n).map
            (Prod.map prefixProjection batchProjection) =
        stochasticSource.trajectoryMeasure.map projectedPrefix ⊗ₘ
          deterministicSource.batchKernel n := by
    exact ProbabilityTheory.measure_compProd_map_prodMap_of_map_eq
      (stochasticSource.trajectoryMeasure.map (Preorder.frestrictLe n))
      (stochasticSource.batchKernel n)
      (stochasticSource.trajectoryMeasure.map projectedPrefix)
      (deterministicSource.batchKernel n)
      prefixProjection hprefixProjection batchProjection hbatchProjection
      hbaseMap
      (fun history =>
        exploratorySource_batchKernel_map_knownRewardEpisodeBatch rewardSource
          initialTable defaultState transitionBonus explorationRate
            hexplorationRate n history)
  change stochasticSource.trajectoryMeasure.map projectedPair =
    stochasticSource.trajectoryMeasure.map projectedPrefix ⊗ₘ
      deterministicSource.batchKernel n
  calc
    stochasticSource.trajectoryMeasure.map projectedPair =
        (stochasticSource.trajectoryMeasure.map originalPair).map
          (Prod.map prefixProjection batchProjection) := by
      rw [Measure.map_map hprodMap horiginalPair]
      rfl
    _ = ((stochasticSource.trajectoryMeasure.map (Preorder.frestrictLe n)) ⊗ₘ
          stochasticSource.batchKernel n).map
            (Prod.map prefixProjection batchProjection) := by
      rw [stochasticSource.trajectoryMeasure_prefix_compProd n]
    _ = stochasticSource.trajectoryMeasure.map projectedPrefix ⊗ₘ
          deterministicSource.batchKernel n := hcompProdMap

omit [Nonempty State] in
/--
Conditioned on the projected stochastic prefix, the projected next batch has
the deterministic exploratory empirical-optimistic source kernel.
-/
theorem exploratorySource_trajectoryMeasure_condDistrib_projectedNext
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    [StandardBorelSpace (EpisodeBatch mdp episodes)]
    [Nonempty (EpisodeBatch mdp episodes)]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (transitionBonus : Real)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1)
    (n : Nat) :
    let stochasticSource := exploratorySource mdp initialState episodes rewardSource
      initialTable defaultState transitionBonus explorationRate hexplorationRate
    let deterministicSource :=
      AdaptiveEmpiricalOptimisticSource.exploratorySource mdp initialState episodes
        initialTable defaultState transitionBonus explorationRate hexplorationRate
    ProbabilityTheory.condDistrib
        (fun trajectory : StochasticEpisodeBatchTrajectory mdp episodes =>
          MDP.MeanCompatibleRewardKernel.knownRewardEpisodeBatch
            (mdp := mdp) episodes (trajectory (n + 1)))
        (fun trajectory : StochasticEpisodeBatchTrajectory mdp episodes =>
          MDP.MeanCompatibleRewardKernel.knownRewardEpisodeBatchPrefix
            (mdp := mdp) episodes n (Preorder.frestrictLe n trajectory))
        stochasticSource.trajectoryMeasure =ᵐ[
          stochasticSource.trajectoryMeasure.map
            (fun trajectory =>
              MDP.MeanCompatibleRewardKernel.knownRewardEpisodeBatchPrefix
                (mdp := mdp) episodes n (Preorder.frestrictLe n trajectory))]
      deterministicSource.batchKernel n := by
  dsimp only
  apply ProbabilityTheory.condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
  · exact
      (MDP.MeanCompatibleRewardKernel.measurable_knownRewardEpisodeBatchPrefix
        (mdp := mdp) episodes n).comp (Preorder.measurable_frestrictLe n)
  · exact
      (MDP.MeanCompatibleRewardKernel.measurable_knownRewardEpisodeBatch
        (mdp := mdp) episodes).comp (measurable_pi_apply (n + 1))
  · exact
      exploratorySource_trajectoryMeasure_map_projectedPrefix_next_eq_compProd
        rewardSource initialTable defaultState transitionBonus explorationRate
          hexplorationRate n

omit [Nonempty State] in
/--
The complete known-reward projection of the concrete stochastic adaptive source
is exactly the existing deterministic exploratory source trajectory law.
-/
theorem exploratorySource_trajectoryMeasure_map_knownRewardEpisodeBatchTrajectory
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    [StandardBorelSpace (EpisodeBatch mdp episodes)]
    [Nonempty (EpisodeBatch mdp episodes)]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (transitionBonus : Real)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1) :
    let stochasticSource := exploratorySource mdp initialState episodes rewardSource
      initialTable defaultState transitionBonus explorationRate hexplorationRate
    let deterministicSource :=
      AdaptiveEmpiricalOptimisticSource.exploratorySource mdp initialState episodes
        initialTable defaultState transitionBonus explorationRate hexplorationRate
    stochasticSource.trajectoryMeasure.map
        (MDP.MeanCompatibleRewardKernel.knownRewardEpisodeBatchTrajectory
          (mdp := mdp) episodes) =
      deterministicSource.trajectoryMeasure := by
  dsimp only
  let stochasticSource := exploratorySource mdp initialState episodes rewardSource
    initialTable defaultState transitionBonus explorationRate hexplorationRate
  let deterministicSource :=
    AdaptiveEmpiricalOptimisticSource.exploratorySource mdp initialState episodes
      initialTable defaultState transitionBonus explorationRate hexplorationRate
  let projection :=
    MDP.MeanCompatibleRewardKernel.knownRewardEpisodeBatchTrajectory
      (mdp := mdp) episodes
  have hzero :
      stochasticSource.trajectoryMeasure.map
          (fun trajectory => projection trajectory 0) =
        deterministicSource.initialPolicy.iidEpisodeBatchMeasure
          initialState episodes := by
    let batchProjection :=
      MDP.MeanCompatibleRewardKernel.knownRewardEpisodeBatch
        (mdp := mdp) episodes
    have hbatchProjection : Measurable batchProjection :=
      MDP.MeanCompatibleRewardKernel.measurable_knownRewardEpisodeBatch
        (mdp := mdp) episodes
    calc
      stochasticSource.trajectoryMeasure.map
          (fun trajectory => projection trajectory 0) =
        (stochasticSource.trajectoryMeasure.map (Function.eval 0)).map
          batchProjection := by
          rw [Measure.map_map hbatchProjection (measurable_pi_apply 0)]
          rfl
      _ = (stochasticSource.rewardSource.iidStochasticTrajectoryFamilyMeasure
          stochasticSource.initialPolicy initialState episodes).map
            batchProjection := by
          rw [stochasticSource.trajectoryMeasure_map_eval_zero]
      _ = deterministicSource.initialPolicy.iidEpisodeBatchMeasure
          initialState episodes := by
        have hrewards : stochasticSource.rewardSource = rewardSource := by
          simp only [stochasticSource, exploratorySource]
        rw [hrewards]
        exact exploratorySource_initialBatch_map_knownRewardEpisodeBatch rewardSource
          initialTable defaultState transitionBonus explorationRate
          hexplorationRate
  have hcond : forall n,
      ProbabilityTheory.condDistrib
          (fun trajectory : StochasticEpisodeBatchTrajectory mdp episodes =>
            projection trajectory (n + 1))
          (fun trajectory : StochasticEpisodeBatchTrajectory mdp episodes =>
            History.finiteRewardHistoryOfTrace (projection trajectory) n)
          stochasticSource.trajectoryMeasure =ᵐ[
            stochasticSource.trajectoryMeasure.map
              (fun trajectory =>
                History.finiteRewardHistoryOfTrace (projection trajectory) n)]
        deterministicSource.batchKernel n := by
    intro n
    simpa [projection, History.finiteRewardHistoryOfTrace] using
      (exploratorySource_trajectoryMeasure_condDistrib_projectedNext
        rewardSource initialTable defaultState transitionBonus explorationRate
          hexplorationRate n)
  simpa [stochasticSource, deterministicSource, projection,
    AdaptiveEpisodeBatchSource.trajectoryMeasure] using
    (RewardKernel.rewardTrace_map_eq_trajMeasure_of_condDistrib
      (mu := stochasticSource.trajectoryMeasure)
      (mu0 := deterministicSource.initialPolicy.iidEpisodeBatchMeasure
        initialState episodes)
      (reward := projection)
      (hreward := fun round =>
        (MDP.MeanCompatibleRewardKernel.measurable_knownRewardEpisodeBatch
          (mdp := mdp) episodes).comp (measurable_pi_apply round))
      (kernel := deterministicSource.batchKernel)
      hzero hcond)

/--
The stochastic count bad event is the inverse image of the deterministic
adaptive count event under complete known-reward projection.
-/
def projectedAdaptiveSimultaneousCountBadEvent
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (transitionBonus : Real)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1)
    (rounds : Nat) (delta : Real) :
    Set (StochasticEpisodeBatchTrajectory mdp episodes) :=
  MDP.MeanCompatibleRewardKernel.knownRewardEpisodeBatchTrajectory
      (mdp := mdp) episodes ⁻¹'
    (AdaptiveEmpiricalOptimisticSource.exploratorySource mdp initialState episodes
      initialTable defaultState transitionBonus explorationRate
        hexplorationRate).adaptiveSimultaneousCountBadEvent rounds delta

omit [Nonempty State] in
/--
Route endpoint: the concrete stochastic source inherits the deterministic
known-mean all-coordinate confidence event, projected optimism, and projected
recommended-policy expected-regret bound.
-/
theorem exploratorySource_trajectoryMeasure_projectedAllCoordinateConfidence_optimism_and_recommendedExpectedRegret
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    [StandardBorelSpace (EpisodeBatch mdp episodes)]
    [Nonempty (EpisodeBatch mdp episodes)]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (rewardBound transitionBonus : Real)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1)
    (hrewardBound : forall state action,
      |mdp.reward state action| <= rewardBound)
    (htransitionBonus_nonneg : 0 <= transitionBonus)
    (rounds : Nat) (hrounds : 0 < rounds)
    (hepisodes : 0 < episodes) (delta : Real) (hdelta : 0 < delta)
    (hdelta_le_one : delta <= 1)
    (calibration :
      let deterministicSource :=
        AdaptiveEmpiricalOptimisticSource.exploratorySource mdp initialState
          episodes initialTable defaultState transitionBonus explorationRate
            hexplorationRate
      AdaptiveEmpiricalOptimisticSource.SourceCalibration
        deterministicSource rounds delta rewardBound transitionBonus) :
    let stochasticSource := exploratorySource mdp initialState episodes rewardSource
      initialTable defaultState transitionBonus explorationRate hexplorationRate
    let projection :=
      MDP.MeanCompatibleRewardKernel.knownRewardEpisodeBatchTrajectory
        (mdp := mdp) episodes
    let bad := projectedAdaptiveSimultaneousCountBadEvent
      (mdp := mdp) (initialState := initialState) (episodes := episodes)
      initialTable defaultState transitionBonus explorationRate
        hexplorationRate rounds delta
    MeasurableSet bad ∧
      stochasticSource.trajectoryMeasure bad <= ENNReal.ofReal delta ∧
      forall trajectory, trajectory ∉ bad ->
        (forall round : Fin rounds, forall state,
          mdp.optimalValueRemaining mdp.horizon le_rfl state <=
            (adaptiveEmpiricalOptimisticPlanAt
              (mdp := mdp) (episodes := episodes)
              (projection trajectory) defaultState transitionBonus round).upperValueRemaining
                mdp.horizon le_rfl state) ∧
        adaptiveEmpiricalOptimisticRecommendedExpectedRegret
            (mdp := mdp) (initialState := initialState) (episodes := episodes)
            (projection trajectory) defaultState transitionBonus rounds <=
          adaptiveEmpiricalOptimisticOccupancyRadiusSum
            (mdp := mdp) (initialState := initialState) (episodes := episodes)
            (projection trajectory) defaultState transitionBonus rounds := by
  dsimp only
  let stochasticSource := exploratorySource mdp initialState episodes rewardSource
    initialTable defaultState transitionBonus explorationRate hexplorationRate
  let deterministicSource :=
    AdaptiveEmpiricalOptimisticSource.exploratorySource mdp initialState episodes
      initialTable defaultState transitionBonus explorationRate hexplorationRate
  let projection :=
    MDP.MeanCompatibleRewardKernel.knownRewardEpisodeBatchTrajectory
      (mdp := mdp) episodes
  let deterministicBad :=
    deterministicSource.adaptiveSimultaneousCountBadEvent rounds delta
  let bad := projection ⁻¹' deterministicBad
  have hdeterministic :=
    AdaptiveEmpiricalOptimisticSource.exploratorySource_trajectoryMeasure_allCoordinateConfidence_optimism_and_recommendedExpectedRegret
      (mdp := mdp) (initialState := initialState) (episodes := episodes)
      initialTable defaultState rewardBound transitionBonus explorationRate
        hexplorationRate hrewardBound htransitionBonus_nonneg rounds hrounds
          hepisodes delta hdelta hdelta_le_one calibration
  change MeasurableSet bad ∧
    stochasticSource.trajectoryMeasure bad <= ENNReal.ofReal delta ∧
    forall trajectory, trajectory ∉ bad ->
      (forall round : Fin rounds, forall state,
        mdp.optimalValueRemaining mdp.horizon le_rfl state <=
          (adaptiveEmpiricalOptimisticPlanAt
            (mdp := mdp) (episodes := episodes)
            (projection trajectory) defaultState transitionBonus round).upperValueRemaining
              mdp.horizon le_rfl state) ∧
      adaptiveEmpiricalOptimisticRecommendedExpectedRegret
          (mdp := mdp) (initialState := initialState) (episodes := episodes)
          (projection trajectory) defaultState transitionBonus rounds <=
        adaptiveEmpiricalOptimisticOccupancyRadiusSum
          (mdp := mdp) (initialState := initialState) (episodes := episodes)
          (projection trajectory) defaultState transitionBonus rounds
  change MeasurableSet deterministicBad ∧
      deterministicSource.trajectoryMeasure deterministicBad <= ENNReal.ofReal delta ∧
      _ at hdeterministic
  obtain ⟨hdeterministicMeasurable, hdeterministicTail, hdeterministicGood⟩ :=
    hdeterministic
  have hprojection : Measurable projection :=
    MDP.MeanCompatibleRewardKernel.measurable_knownRewardEpisodeBatchTrajectory
      (mdp := mdp) episodes
  have htrajectoryMap :
      stochasticSource.trajectoryMeasure.map projection =
        deterministicSource.trajectoryMeasure := by
    simpa [stochasticSource, deterministicSource, projection] using
      (exploratorySource_trajectoryMeasure_map_knownRewardEpisodeBatchTrajectory
        rewardSource initialTable defaultState transitionBonus explorationRate
          hexplorationRate)
  refine ⟨hdeterministicMeasurable.preimage hprojection, ?_, ?_⟩
  · calc
      stochasticSource.trajectoryMeasure bad =
          (stochasticSource.trajectoryMeasure.map projection) deterministicBad := by
        rw [Measure.map_apply hprojection hdeterministicMeasurable]
      _ = deterministicSource.trajectoryMeasure deterministicBad := by
        rw [htrajectoryMap]
      _ <= ENNReal.ofReal delta := hdeterministicTail
  · intro trajectory htrajectory
    exact hdeterministicGood (projection trajectory) htrajectory

end AdaptiveStochasticEmpiricalOptimisticSource
end FiniteHorizonRL
end BanditRLProof
