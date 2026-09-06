import BanditRLProof.RL.FiniteHorizonAdaptiveStochasticRewardSampledEmpiricalOptimisticSource
import BanditRLProof.RL.FiniteHorizonStochasticRewardIIDExplicitCalibration

/-!
# Finite-round confidence for the adaptive sampled empirical optimistic source

This module transports the fixed-policy sampled count-and-reward empirical
model event through the exact history-fiber laws of the adaptive stochastic
source.  The resulting finite-round event controls models computed from the
actual sampled rewards, not their known-mean projection.
-/

open MeasureTheory
open scoped ENNReal ProbabilityTheory

universe u v

namespace BanditRLProof
namespace FiniteHorizonRL

variable {State : Type u} {Action : Type v}
    [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action]
    [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action]

namespace AdaptiveStochasticEpisodeBatchSource

/-- Policy whose iid stochastic law generated a batch coordinate. -/
def policyAt
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveStochasticEpisodeBatchSource mdp initialState episodes)
    (trajectory : StochasticEpisodeBatchTrajectory mdp episodes) :
    Nat -> MarkovPolicy mdp
  | 0 => source.initialPolicy
  | n + 1 => source.successorPolicy n (Preorder.frestrictLe n trajectory)

/-- Pull an initial stochastic-batch event back to the adaptive trajectory. -/
def initialBadEvent
    {mdp : MDP State Action} {episodes : Nat}
    (bad : Set (StochasticEpisodeBatch mdp episodes)) :
    Set (StochasticEpisodeBatchTrajectory mdp episodes) :=
  (Function.eval 0) ⁻¹' bad

/-- Pull a prefix-dependent successor stochastic-batch event back to the trajectory. -/
def successorBadEvent
    {mdp : MDP State Action} {episodes : Nat} (n : Nat)
    (bad : Set (StochasticEpisodeBatchPrefix mdp episodes n ×
      StochasticEpisodeBatch mdp episodes)) :
    Set (StochasticEpisodeBatchTrajectory mdp episodes) :=
  (fun trajectory =>
    (Preorder.frestrictLe n trajectory, trajectory (n + 1))) ⁻¹' bad

/-- Round-indexed adapted stochastic-batch event. -/
def roundBadEvent
    {mdp : MDP State Action} {episodes : Nat}
    (initialBad : Set (StochasticEpisodeBatch mdp episodes))
    (successorBad : (n : Nat) ->
      Set (StochasticEpisodeBatchPrefix mdp episodes n ×
        StochasticEpisodeBatch mdp episodes)) :
    Nat -> Set (StochasticEpisodeBatchTrajectory mdp episodes)
  | 0 => initialBadEvent initialBad
  | n + 1 => successorBadEvent n (successorBad n)

/-- Union of the first `rounds` adapted stochastic-batch events. -/
def finiteHorizonBadEvent
    {mdp : MDP State Action} {episodes : Nat}
    (rounds : Nat)
    (initialBad : Set (StochasticEpisodeBatch mdp episodes))
    (successorBad : (n : Nat) ->
      Set (StochasticEpisodeBatchPrefix mdp episodes n ×
        StochasticEpisodeBatch mdp episodes)) :
    Set (StochasticEpisodeBatchTrajectory mdp episodes) :=
  ⋃ round : Fin rounds, roundBadEvent initialBad successorBad round

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- Measurability of the finite adapted stochastic-batch union. -/
theorem measurableSet_finiteHorizonBadEvent
    {mdp : MDP State Action} {episodes rounds : Nat}
    {initialBad : Set (StochasticEpisodeBatch mdp episodes)}
    {successorBad : (n : Nat) ->
      Set (StochasticEpisodeBatchPrefix mdp episodes n ×
        StochasticEpisodeBatch mdp episodes)}
    (hinitial : MeasurableSet initialBad)
    (hsuccessor : forall n, n + 1 < rounds ->
      MeasurableSet (successorBad n)) :
    MeasurableSet
      (finiteHorizonBadEvent rounds initialBad successorBad) := by
  refine MeasurableSet.iUnion fun round => ?_
  cases round with
  | mk value hvalue =>
      cases value with
      | zero =>
          exact hinitial.preimage (measurable_pi_apply 0)
      | succ n =>
          exact (hsuccessor n hvalue).preimage (by fun_prop)

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- Exact mass of a pulled-back initial stochastic-batch event. -/
theorem trajectoryMeasure_initialBadEvent
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveStochasticEpisodeBatchSource mdp initialState episodes)
    {bad : Set (StochasticEpisodeBatch mdp episodes)}
    (hbad : MeasurableSet bad) :
    source.trajectoryMeasure (initialBadEvent bad) =
      source.rewardSource.iidStochasticTrajectoryFamilyMeasure
        source.initialPolicy initialState episodes bad := by
  change source.trajectoryMeasure ((Function.eval 0) ⁻¹' bad) = _
  rw [← Measure.map_apply (measurable_pi_apply 0) hbad]
  rw [source.trajectoryMeasure_map_eval_zero]

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- A successor event inherits a uniform bound on every history fiber. -/
theorem trajectoryMeasure_successorBadEvent_le
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveStochasticEpisodeBatchSource mdp initialState episodes)
    (n : Nat)
    {bad : Set (StochasticEpisodeBatchPrefix mdp episodes n ×
      StochasticEpisodeBatch mdp episodes)}
    (hbad : MeasurableSet bad) (budget : ENNReal)
    (hfiber : forall history,
      source.batchKernel n history (Prod.mk history ⁻¹' bad) <= budget) :
    source.trajectoryMeasure (successorBadEvent n bad) <= budget := by
  let prefixMeasure :=
    source.trajectoryMeasure.map (Preorder.frestrictLe n)
  let pairMap : StochasticEpisodeBatchTrajectory mdp episodes ->
      StochasticEpisodeBatchPrefix mdp episodes n ×
        StochasticEpisodeBatch mdp episodes :=
    fun trajectory =>
      (Preorder.frestrictLe n trajectory, trajectory (n + 1))
  have hpairMap : Measurable pairMap := by fun_prop
  haveI : IsProbabilityMeasure prefixMeasure := by
    dsimp only [prefixMeasure]
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  calc
    source.trajectoryMeasure (successorBadEvent n bad) =
        source.trajectoryMeasure.map pairMap bad := by
      rw [Measure.map_apply hpairMap hbad]
      rfl
    _ = (prefixMeasure ⊗ₘ source.batchKernel n) bad := by
      rw [source.trajectoryMeasure_prefix_compProd n]
    _ = ∫⁻ history, source.batchKernel n history
          (Prod.mk history ⁻¹' bad) ∂prefixMeasure :=
      Measure.compProd_apply hbad
    _ <= ∫⁻ _history, budget ∂prefixMeasure :=
      lintegral_mono hfiber
    _ = budget := by simp [prefixMeasure]

/-- Initial selected count-and-reward empirical-model event. -/
noncomputable def initialAllCoordinateEmpiricalModelBadEvent
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveStochasticEpisodeBatchSource mdp initialState episodes)
    (rounds : Nat) (varianceProxy : NNReal)
    (countDelta rewardDelta : Real) :
    Set (StochasticEpisodeBatch mdp episodes) :=
  source.rewardSource.stochasticAllCoordinateEmpiricalModelBadEvent
    source.initialPolicy initialState episodes varianceProxy
      (multiBatchLocalDelta rounds countDelta)
      (multiBatchLocalDelta rounds rewardDelta)

/-- Prefix-selected successor count-and-reward empirical-model event. -/
noncomputable def successorAllCoordinateEmpiricalModelBadEvent
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveStochasticEpisodeBatchSource mdp initialState episodes)
    (rounds : Nat) (varianceProxy : NNReal)
    (countDelta rewardDelta : Real) (n : Nat) :
    Set (StochasticEpisodeBatchPrefix mdp episodes n ×
      StochasticEpisodeBatch mdp episodes) :=
  {pair | pair.2 ∈
    source.rewardSource.stochasticAllCoordinateEmpiricalModelBadEvent
      (source.successorPolicy n pair.1) initialState episodes varianceProxy
        (multiBatchLocalDelta rounds countDelta)
        (multiBatchLocalDelta rounds rewardDelta)}

/-- Finite-round selected count-and-reward empirical-model event. -/
noncomputable def adaptiveAllCoordinateEmpiricalModelBadEvent
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveStochasticEpisodeBatchSource mdp initialState episodes)
    (rounds : Nat) (varianceProxy : NNReal)
    (countDelta rewardDelta : Real) :
    Set (StochasticEpisodeBatchTrajectory mdp episodes) :=
  finiteHorizonBadEvent rounds
    (source.initialAllCoordinateEmpiricalModelBadEvent
      rounds varianceProxy countDelta rewardDelta)
    (source.successorAllCoordinateEmpiricalModelBadEvent
      rounds varianceProxy countDelta rewardDelta)

/-- A positive global share gives a positive finite-round local share. -/
theorem multiBatchLocalDelta_pos_of_pos
    {rounds : Nat} (hrounds : 0 < rounds)
    {delta : Real} (hdelta : 0 < delta) :
    0 < multiBatchLocalDelta rounds delta := by
  exact div_pos hdelta (Nat.cast_pos.mpr hrounds)

/-- A global share at most one gives every finite-round local share at most one. -/
theorem multiBatchLocalDelta_le_one_of_le_one
    {rounds : Nat} (hrounds : 0 < rounds)
    {delta : Real} (hdelta_le_one : delta <= 1) :
    multiBatchLocalDelta rounds delta <= 1 := by
  have hroundsReal : 0 < (rounds : Real) := Nat.cast_pos.mpr hrounds
  have hroundsOne : (1 : Real) <= (rounds : Real) := by
    exact_mod_cast hrounds
  unfold multiBatchLocalDelta
  exact (div_le_one hroundsReal).2 (hdelta_le_one.trans hroundsOne)

/-- The initial selected empirical-model event is measurable. -/
theorem measurableSet_initialAllCoordinateEmpiricalModelBadEvent
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveStochasticEpisodeBatchSource mdp initialState episodes)
    (rounds : Nat) (varianceProxy : NNReal)
    (countDelta rewardDelta : Real) :
    MeasurableSet (source.initialAllCoordinateEmpiricalModelBadEvent
      rounds varianceProxy countDelta rewardDelta) := by
  exact source.rewardSource.measurableSet_stochasticAllCoordinateEmpiricalModelBadEvent
    source.initialPolicy initialState episodes varianceProxy
      (multiBatchLocalDelta rounds countDelta)
      (multiBatchLocalDelta rounds rewardDelta)

/-- Measurability of every selected successor event closes the global event. -/
theorem measurableSet_adaptiveAllCoordinateEmpiricalModelBadEvent
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveStochasticEpisodeBatchSource mdp initialState episodes)
    (rounds : Nat) (varianceProxy : NNReal)
    (countDelta rewardDelta : Real)
    (hsuccessor : forall n, n + 1 < rounds ->
      MeasurableSet (source.successorAllCoordinateEmpiricalModelBadEvent
        rounds varianceProxy countDelta rewardDelta n)) :
    MeasurableSet (source.adaptiveAllCoordinateEmpiricalModelBadEvent
      rounds varianceProxy countDelta rewardDelta) := by
  exact measurableSet_finiteHorizonBadEvent
    (source.measurableSet_initialAllCoordinateEmpiricalModelBadEvent
      rounds varianceProxy countDelta rewardDelta)
    hsuccessor

/-- The initial selected empirical-model event receives its two local shares. -/
theorem initialAllCoordinateEmpiricalModelBadEvent_le
    [StandardBorelSpace State] [StandardBorelSpace Action]
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveStochasticEpisodeBatchSource mdp initialState episodes)
    (rounds : Nat) (hrounds : 0 < rounds) (hepisodes : 0 < episodes)
    (varianceProxy : NNReal)
    (law : source.rewardSource.UniformSubgaussianRewardLaw varianceProxy)
    (htotal : 0 < ((((episodes : NNReal) * varianceProxy : NNReal) : Real)))
    (countDelta : Real) (hcountDelta : 0 < countDelta)
    (hcountDelta_le_one : countDelta <= 1)
    (rewardDelta : Real) (hrewardDelta : 0 < rewardDelta)
    (hrewardDelta_le_one : rewardDelta <= 1) :
    (source.rewardSource.iidStochasticTrajectoryFamilyMeasure
      source.initialPolicy initialState episodes)
        (source.initialAllCoordinateEmpiricalModelBadEvent
          rounds varianceProxy countDelta rewardDelta) <=
      ENNReal.ofReal (multiBatchLocalDelta rounds countDelta) +
        ENNReal.ofReal (multiBatchLocalDelta rounds rewardDelta) := by
  exact source.rewardSource.iidStochasticTrajectoryFamilyMeasure_stochasticAllCoordinateEmpiricalModelBadEvent_le
    source.initialPolicy initialState episodes hepisodes varianceProxy law htotal
      (multiBatchLocalDelta rounds countDelta)
      (multiBatchLocalDelta_pos_of_pos hrounds hcountDelta)
      (multiBatchLocalDelta_le_one_of_le_one hrounds hcountDelta_le_one)
      (multiBatchLocalDelta rounds rewardDelta)
      (multiBatchLocalDelta_pos_of_pos hrounds hrewardDelta)
      (multiBatchLocalDelta_le_one_of_le_one hrounds hrewardDelta_le_one)

/-- Every selected successor fiber receives the same two local shares. -/
theorem successorAllCoordinateEmpiricalModelBadEvent_fiber_le
    [StandardBorelSpace State] [StandardBorelSpace Action]
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveStochasticEpisodeBatchSource mdp initialState episodes)
    (rounds : Nat) (hrounds : 0 < rounds) (hepisodes : 0 < episodes)
    (varianceProxy : NNReal)
    (law : source.rewardSource.UniformSubgaussianRewardLaw varianceProxy)
    (htotal : 0 < ((((episodes : NNReal) * varianceProxy : NNReal) : Real)))
    (countDelta : Real) (hcountDelta : 0 < countDelta)
    (hcountDelta_le_one : countDelta <= 1)
    (rewardDelta : Real) (hrewardDelta : 0 < rewardDelta)
    (hrewardDelta_le_one : rewardDelta <= 1)
    (n : Nat) (history : StochasticEpisodeBatchPrefix mdp episodes n) :
    source.batchKernel n history
        (Prod.mk history ⁻¹'
          source.successorAllCoordinateEmpiricalModelBadEvent
            rounds varianceProxy countDelta rewardDelta n) <=
      ENNReal.ofReal (multiBatchLocalDelta rounds countDelta) +
        ENNReal.ofReal (multiBatchLocalDelta rounds rewardDelta) := by
  rw [source.batchKernel_eq_iidStochasticTrajectoryFamilyMeasure]
  change
    (source.rewardSource.iidStochasticTrajectoryFamilyMeasure
      (source.successorPolicy n history) initialState episodes)
        (source.rewardSource.stochasticAllCoordinateEmpiricalModelBadEvent
          (source.successorPolicy n history) initialState episodes varianceProxy
            (multiBatchLocalDelta rounds countDelta)
            (multiBatchLocalDelta rounds rewardDelta)) <= _
  exact source.rewardSource.iidStochasticTrajectoryFamilyMeasure_stochasticAllCoordinateEmpiricalModelBadEvent_le
    (source.successorPolicy n history) initialState episodes hepisodes
      varianceProxy law htotal
      (multiBatchLocalDelta rounds countDelta)
      (multiBatchLocalDelta_pos_of_pos hrounds hcountDelta)
      (multiBatchLocalDelta_le_one_of_le_one hrounds hcountDelta_le_one)
      (multiBatchLocalDelta rounds rewardDelta)
      (multiBatchLocalDelta_pos_of_pos hrounds hrewardDelta)
      (multiBatchLocalDelta_le_one_of_le_one hrounds hrewardDelta_le_one)

/-- The two local shares are the local share of their sum. -/
theorem ofReal_multiBatchLocalDelta_add
    (rounds : Nat) {countDelta rewardDelta : Real}
    (hcountDelta : 0 <= countDelta) (hrewardDelta : 0 <= rewardDelta) :
    ENNReal.ofReal (multiBatchLocalDelta rounds countDelta) +
        ENNReal.ofReal (multiBatchLocalDelta rounds rewardDelta) =
      ENNReal.ofReal
        (multiBatchLocalDelta rounds (countDelta + rewardDelta)) := by
  have hrounds : (0 : Real) <= (rounds : Real) := Nat.cast_nonneg _
  have hcountLocal : 0 <= multiBatchLocalDelta rounds countDelta := by
    exact div_nonneg hcountDelta hrounds
  have hrewardLocal : 0 <= multiBatchLocalDelta rounds rewardDelta := by
    exact div_nonneg hrewardDelta hrounds
  calc
    ENNReal.ofReal (multiBatchLocalDelta rounds countDelta) +
        ENNReal.ofReal (multiBatchLocalDelta rounds rewardDelta) =
      ENNReal.ofReal
        (multiBatchLocalDelta rounds countDelta +
          multiBatchLocalDelta rounds rewardDelta) :=
      (ENNReal.ofReal_add hcountLocal hrewardLocal).symm
    _ = ENNReal.ofReal
        (multiBatchLocalDelta rounds (countDelta + rewardDelta)) := by
      congr 1
      unfold multiBatchLocalDelta
      ring

/--
Finite-round adaptive count-and-reward confidence under exact selected-policy
iid fibers.  The two global shares remain separate in the terminal bound.
-/
theorem trajectoryMeasure_adaptiveAllCoordinateEmpiricalModelBadEvent_le
    [StandardBorelSpace State] [StandardBorelSpace Action]
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveStochasticEpisodeBatchSource mdp initialState episodes)
    (rounds : Nat) (hrounds : 0 < rounds) (hepisodes : 0 < episodes)
    (varianceProxy : NNReal)
    (law : source.rewardSource.UniformSubgaussianRewardLaw varianceProxy)
    (htotal : 0 < ((((episodes : NNReal) * varianceProxy : NNReal) : Real)))
    (countDelta : Real) (hcountDelta : 0 < countDelta)
    (hcountDelta_le_one : countDelta <= 1)
    (rewardDelta : Real) (hrewardDelta : 0 < rewardDelta)
    (hrewardDelta_le_one : rewardDelta <= 1)
    (hsuccessor : forall n, n + 1 < rounds ->
      MeasurableSet (source.successorAllCoordinateEmpiricalModelBadEvent
        rounds varianceProxy countDelta rewardDelta n)) :
    source.trajectoryMeasure
        (source.adaptiveAllCoordinateEmpiricalModelBadEvent
          rounds varianceProxy countDelta rewardDelta) <=
      ENNReal.ofReal countDelta + ENNReal.ofReal rewardDelta := by
  let initialBad := source.initialAllCoordinateEmpiricalModelBadEvent
    rounds varianceProxy countDelta rewardDelta
  let successorBad := source.successorAllCoordinateEmpiricalModelBadEvent
    rounds varianceProxy countDelta rewardDelta
  have hinitialMeasurable : MeasurableSet initialBad := by
    exact source.measurableSet_initialAllCoordinateEmpiricalModelBadEvent
      rounds varianceProxy countDelta rewardDelta
  have hlocal :
      ENNReal.ofReal (multiBatchLocalDelta rounds countDelta) +
          ENNReal.ofReal (multiBatchLocalDelta rounds rewardDelta) =
        ENNReal.ofReal
          ((countDelta + rewardDelta) / ((Finset.univ : Finset (Fin rounds)).card : Real)) := by
    rw [ofReal_multiBatchLocalDelta_add rounds hcountDelta.le hrewardDelta.le]
    simp [multiBatchLocalDelta]
  have hroundTail : forall round : Fin rounds,
      source.trajectoryMeasure
          (roundBadEvent initialBad successorBad round) <=
        ENNReal.ofReal
          ((countDelta + rewardDelta) /
            ((Finset.univ : Finset (Fin rounds)).card : Real)) := by
    intro round
    cases round with
    | mk value hvalue =>
        cases value with
        | zero =>
            rw [roundBadEvent,
              source.trajectoryMeasure_initialBadEvent hinitialMeasurable]
            exact (source.initialAllCoordinateEmpiricalModelBadEvent_le
              rounds hrounds hepisodes varianceProxy law htotal
                countDelta hcountDelta hcountDelta_le_one
                rewardDelta hrewardDelta hrewardDelta_le_one).trans_eq hlocal
        | succ n =>
            exact (source.trajectoryMeasure_successorBadEvent_le n
              (hsuccessor n hvalue)
              (ENNReal.ofReal
                ((countDelta + rewardDelta) /
                  ((Finset.univ : Finset (Fin rounds)).card : Real)))
              (fun history =>
                (source.successorAllCoordinateEmpiricalModelBadEvent_fiber_le
                  rounds hrounds hepisodes varianceProxy law htotal
                    countDelta hcountDelta hcountDelta_le_one
                    rewardDelta hrewardDelta hrewardDelta_le_one n history).trans_eq
                      hlocal)).trans_eq rfl
  letI : Nonempty (Fin rounds) := ⟨⟨0, hrounds⟩⟩
  have hglobal :=
    ProbabilityUnionBound.measure_biUnion_finset_le_of_uniform
      source.trajectoryMeasure (Finset.univ : Finset (Fin rounds))
      Finset.univ_nonempty (countDelta + rewardDelta)
      (fun round => roundBadEvent initialBad successorBad round)
      (fun round _ => hroundTail round)
  rw [← ENNReal.ofReal_add hcountDelta.le hrewardDelta.le]
  simpa [adaptiveAllCoordinateEmpiricalModelBadEvent,
    finiteHorizonBadEvent, initialBad, successorBad] using hglobal

omit [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- Outside the adaptive event, each batch avoids its generating policy's event. -/
theorem policyAt_batch_not_mem_allCoordinateEmpiricalModelBadEvent
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes rounds : Nat}
    (source : AdaptiveStochasticEpisodeBatchSource mdp initialState episodes)
    (trajectory : StochasticEpisodeBatchTrajectory mdp episodes)
    (varianceProxy : NNReal) (countDelta rewardDelta : Real)
    (htrajectory : trajectory ∉
      source.adaptiveAllCoordinateEmpiricalModelBadEvent
        rounds varianceProxy countDelta rewardDelta)
    (round : Fin rounds) :
    trajectory round ∉
      source.rewardSource.stochasticAllCoordinateEmpiricalModelBadEvent
        (source.policyAt trajectory round) initialState episodes varianceProxy
          (multiBatchLocalDelta rounds countDelta)
          (multiBatchLocalDelta rounds rewardDelta) := by
  have hround : trajectory ∉ roundBadEvent
      (source.initialAllCoordinateEmpiricalModelBadEvent
        rounds varianceProxy countDelta rewardDelta)
      (source.successorAllCoordinateEmpiricalModelBadEvent
        rounds varianceProxy countDelta rewardDelta) round := by
    intro hmem
    apply htrajectory
    exact Set.mem_iUnion_of_mem round hmem
  cases round with
  | mk value hvalue =>
      cases value with
      | zero =>
          simpa [roundBadEvent, initialBadEvent,
            initialAllCoordinateEmpiricalModelBadEvent, policyAt] using hround
      | succ n =>
          simpa [roundBadEvent, successorBadEvent,
            successorAllCoordinateEmpiricalModelBadEvent, policyAt] using hround

end AdaptiveStochasticEpisodeBatchSource

namespace AdaptiveStochasticSampledEmpiricalOptimisticSource

/--
Selected exploratory count-and-reward events are measurable after pulling the
stochastic batch back to its raw sampled `EpisodeBatch`.
-/
theorem measurableSet_selectedExploratoryStochasticAllCoordinateEmpiricalModelBadEvent
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    {History : Type*} [MeasurableSpace History]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (selector : History -> DeterministicMarkovPolicyTable mdp)
    (hselector : Measurable selector)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1)
    (varianceProxy : NNReal) (countDelta rewardDelta : Real) :
    MeasurableSet
      {pair : History × StochasticEpisodeBatch mdp episodes |
        pair.2 ∈ rewardSource.stochasticAllCoordinateEmpiricalModelBadEvent
          ((selector pair.1).exploratoryPolicy explorationRate hexplorationRate)
          initialState episodes varianceProxy countDelta rewardDelta} := by
  let projection : History × StochasticEpisodeBatch mdp episodes ->
      History × EpisodeBatch mdp episodes := fun pair =>
    (pair.1,
      mdp.sampledEpisodeBatchOfStochasticTrajectories episodes pair.2)
  have hprojection : Measurable projection :=
    measurable_fst.prodMk
      ((mdp.measurable_sampledEpisodeBatchOfStochasticTrajectories episodes).comp
        measurable_snd)
  have hcount : MeasurableSet
      {pair : History × EpisodeBatch mdp episodes |
        pair.2 ∈
          ((selector pair.1).exploratoryPolicy explorationRate
            hexplorationRate).simultaneousCountBadEvent
              initialState episodes countDelta} :=
    AdaptiveEmpiricalOptimisticSource.measurableSet_selectedExploratorySimultaneousCountBadEvent
      selector hselector explorationRate hexplorationRate countDelta
  have hcount' : MeasurableSet
      {pair : History × StochasticEpisodeBatch mdp episodes |
        pair.2 ∈ rewardSource.stochasticSampledBatchCountBadEvent
          ((selector pair.1).exploratoryPolicy explorationRate hexplorationRate)
          initialState episodes countDelta} := by
    simpa [projection,
      MDP.MeanCompatibleRewardKernel.stochasticSampledBatchCountBadEvent] using
        hcount.preimage hprojection
  have hreward : MeasurableSet
      {pair : History × StochasticEpisodeBatch mdp episodes |
        pair.2 ∈ rewardSource.simultaneousRewardBadEvent
          episodes varianceProxy rewardDelta} :=
    (rewardSource.measurableSet_simultaneousRewardBadEvent
      episodes varianceProxy rewardDelta).preimage measurable_snd
  change MeasurableSet
    ({pair : History × StochasticEpisodeBatch mdp episodes |
        pair.2 ∈ rewardSource.stochasticSampledBatchCountBadEvent
          ((selector pair.1).exploratoryPolicy explorationRate hexplorationRate)
          initialState episodes countDelta} ∪
      {pair : History × StochasticEpisodeBatch mdp episodes |
        pair.2 ∈ rewardSource.simultaneousRewardBadEvent
          episodes varianceProxy rewardDelta})
  exact hcount'.union hreward

/-- Every successor event of the concrete sampled optimistic source is measurable. -/
theorem exploratorySource_measurableSet_successorAllCoordinateEmpiricalModelBadEvent
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (rewardBudget transitionBudget : Real)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1)
    (rounds : Nat) (varianceProxy : NNReal)
    (countDelta rewardDelta : Real) (n : Nat) :
    let source := exploratorySource mdp initialState episodes rewardSource
      initialTable defaultState rewardBudget transitionBudget
        explorationRate hexplorationRate
    MeasurableSet (source.successorAllCoordinateEmpiricalModelBadEvent
      rounds varianceProxy countDelta rewardDelta n) := by
  dsimp only
  change MeasurableSet
    {pair : StochasticEpisodeBatchPrefix mdp episodes n ×
        StochasticEpisodeBatch mdp episodes |
      pair.2 ∈ rewardSource.stochasticAllCoordinateEmpiricalModelBadEvent
        ((successorTable defaultState rewardBudget transitionBudget n pair.1)
          |>.exploratoryPolicy explorationRate hexplorationRate)
        initialState episodes varianceProxy
          (multiBatchLocalDelta rounds countDelta)
          (multiBatchLocalDelta rounds rewardDelta)}
  exact measurableSet_selectedExploratoryStochasticAllCoordinateEmpiricalModelBadEvent
    rewardSource
    (successorTable defaultState rewardBudget transitionBudget n)
    (measurable_successorTable defaultState rewardBudget transitionBudget n)
    explorationRate hexplorationRate varianceProxy
      (multiBatchLocalDelta rounds countDelta)
      (multiBatchLocalDelta rounds rewardDelta)

/--
The concrete sampled optimistic source inherits the finite-round selected
count-and-reward event without any caller-supplied measurability premise.
-/
theorem exploratorySource_trajectoryMeasure_adaptiveAllCoordinateEmpiricalModelBadEvent_le
    [StandardBorelSpace State] [StandardBorelSpace Action]
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (rewardBudget transitionBudget : Real)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1)
    (rounds : Nat) (hrounds : 0 < rounds) (hepisodes : 0 < episodes)
    (varianceProxy : NNReal)
    (law : rewardSource.UniformSubgaussianRewardLaw varianceProxy)
    (htotal : 0 < ((((episodes : NNReal) * varianceProxy : NNReal) : Real)))
    (countDelta : Real) (hcountDelta : 0 < countDelta)
    (hcountDelta_le_one : countDelta <= 1)
    (rewardDelta : Real) (hrewardDelta : 0 < rewardDelta)
    (hrewardDelta_le_one : rewardDelta <= 1) :
    let source := exploratorySource mdp initialState episodes rewardSource
      initialTable defaultState rewardBudget transitionBudget
        explorationRate hexplorationRate
    let event := source.adaptiveAllCoordinateEmpiricalModelBadEvent
      rounds varianceProxy countDelta rewardDelta
    MeasurableSet event /\
      source.trajectoryMeasure event <=
        ENNReal.ofReal countDelta + ENNReal.ofReal rewardDelta := by
  dsimp only
  let source : AdaptiveStochasticEpisodeBatchSource mdp initialState episodes :=
    exploratorySource mdp initialState episodes rewardSource
      initialTable defaultState rewardBudget transitionBudget
        explorationRate hexplorationRate
  have hsuccessor : forall n, n + 1 < rounds ->
      MeasurableSet (source.successorAllCoordinateEmpiricalModelBadEvent
        rounds varianceProxy countDelta rewardDelta n) := by
    intro n _hn
    exact exploratorySource_measurableSet_successorAllCoordinateEmpiricalModelBadEvent
      rewardSource initialTable defaultState rewardBudget transitionBudget
        explorationRate hexplorationRate rounds varianceProxy
        countDelta rewardDelta n
  exact
    ⟨source.measurableSet_adaptiveAllCoordinateEmpiricalModelBadEvent
        rounds varianceProxy countDelta rewardDelta hsuccessor,
      source.trajectoryMeasure_adaptiveAllCoordinateEmpiricalModelBadEvent_le
        rounds hrounds hepisodes varianceProxy law htotal
          countDelta hcountDelta hcountDelta_le_one
          rewardDelta hrewardDelta hrewardDelta_le_one hsuccessor⟩

/--
Finite-round sampled-reward adaptive optimism with explicit exploratory path
support calibration.  Every model is built from the actual observed rewards;
outside one measurable event, every round is optimistic and its recommended
policy satisfies the compiled selected-radius expected-regret bound.
-/
theorem exploratorySource_trajectoryMeasure_finiteRound_allCoordinateConfidence_optimism_and_recommendedExpectedRegret_of_pathSupport_explicitCalibration
    [StandardBorelSpace State] [StandardBorelSpace Action]
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1)
    (rounds : Nat) (hrounds : 0 < rounds) (hepisodes : 0 < episodes)
    (varianceProxy : NNReal)
    (law : rewardSource.UniformSubgaussianRewardLaw varianceProxy)
    (htotal : 0 < ((((episodes : NNReal) * varianceProxy : NNReal) : Real)))
    (countDelta : Real) (hcountDelta : 0 < countDelta)
    (hcountDelta_le_one : countDelta <= 1)
    (rewardDelta : Real) (hrewardDelta : 0 < rewardDelta)
    (hrewardDelta_le_one : rewardDelta <= 1)
    (defaultState : State) (rewardBound : Real)
    (hrewardBound : forall state action,
      |mdp.reward state action| <= rewardBound)
    (support : ExploratoryPathSupport mdp initialState) (visitFloor : Real)
    (hfloor : ExploratoryPathUniformVisitFloor support explorationRate visitFloor)
    (hmargin :
      simultaneousCountConfidenceRadius mdp episodes
          (multiBatchLocalDelta rounds countDelta) <
        (episodes : Real) * visitFloor)
    (hcontraction :
      (Fintype.card State : Real) *
          uniformFloorTransitionCoordinateRadius mdp episodes
            (multiBatchLocalDelta rounds countDelta) visitFloor *
          (mdp.horizon : Real) <=
        1 / 2) :
    let localCountDelta := multiBatchLocalDelta rounds countDelta
    let localRewardDelta := multiBatchLocalDelta rounds rewardDelta
    let rewardBudget :=
      uniformFloorStochasticRewardCoordinateRadius mdp episodes varianceProxy
        localCountDelta localRewardDelta visitFloor
    let transitionBudget :=
      uniformFloorStochasticTransitionBudget rewardBound rewardBudget
    let source := exploratorySource mdp initialState episodes rewardSource
      initialTable defaultState rewardBudget transitionBudget
        explorationRate hexplorationRate
    let event := source.adaptiveAllCoordinateEmpiricalModelBadEvent
      rounds varianceProxy countDelta rewardDelta
    MeasurableSet event /\
      source.trajectoryMeasure event <=
        ENNReal.ofReal countDelta + ENNReal.ofReal rewardDelta /\
      forall trajectory, trajectory ∉ event -> forall round : Fin rounds,
        let model := mdp.stochasticAllCoordinateEmpiricalFiniteBatchModel
          episodes (mdp.sampledEpisodeBatchOfStochasticTrajectories
            episodes (trajectory round))
          defaultState rewardBudget transitionBudget
        (forall state,
            mdp.optimalValueRemaining mdp.horizon le_rfl state <=
              model.plan.upperValueRemaining mdp.horizon le_rfl state) /\
          model.plan.optimisticPolicy.expectedRegret initialState <=
            model.plan.optimisticPolicy.occupancySumRemaining
              (fun remaining hremaining state =>
                2 * model.plan.selectedRadiusRemaining
                  remaining hremaining state)
              mdp.horizon le_rfl initialState := by
  dsimp only
  let localCountDelta := multiBatchLocalDelta rounds countDelta
  let localRewardDelta := multiBatchLocalDelta rounds rewardDelta
  let rewardBudget :=
    uniformFloorStochasticRewardCoordinateRadius mdp episodes varianceProxy
      localCountDelta localRewardDelta visitFloor
  let transitionBudget :=
    uniformFloorStochasticTransitionBudget rewardBound rewardBudget
  let source : AdaptiveStochasticEpisodeBatchSource mdp initialState episodes :=
    exploratorySource mdp initialState episodes rewardSource
      initialTable defaultState rewardBudget transitionBudget
        explorationRate hexplorationRate
  let event : Set (StochasticEpisodeBatchTrajectory mdp episodes) :=
    AdaptiveStochasticEpisodeBatchSource.adaptiveAllCoordinateEmpiricalModelBadEvent
      (mdp := mdp) (initialState := initialState) (episodes := episodes)
      source rounds varianceProxy countDelta rewardDelta
  have hlocalCountPos : 0 < localCountDelta :=
    AdaptiveStochasticEpisodeBatchSource.multiBatchLocalDelta_pos_of_pos
      hrounds hcountDelta
  have hlocalCountLeOne : localCountDelta <= 1 :=
    AdaptiveStochasticEpisodeBatchSource.multiBatchLocalDelta_le_one_of_le_one
      hrounds hcountDelta_le_one
  have hlocalRewardPos : 0 < localRewardDelta :=
    AdaptiveStochasticEpisodeBatchSource.multiBatchLocalDelta_pos_of_pos
      hrounds hrewardDelta
  have hlocalRewardLeOne : localRewardDelta <= 1 :=
    AdaptiveStochasticEpisodeBatchSource.multiBatchLocalDelta_le_one_of_le_one
      hrounds hrewardDelta_le_one
  have hevent : MeasurableSet event /\
      source.trajectoryMeasure event <=
        ENNReal.ofReal countDelta + ENNReal.ofReal rewardDelta := by
    simpa [event, source] using
      (exploratorySource_trajectoryMeasure_adaptiveAllCoordinateEmpiricalModelBadEvent_le
        rewardSource initialTable defaultState rewardBudget transitionBudget
          explorationRate hexplorationRate rounds hrounds hepisodes
          varianceProxy law htotal countDelta hcountDelta hcountDelta_le_one
          rewardDelta hrewardDelta hrewardDelta_le_one)
  refine ⟨hevent.1, hevent.2, ?_⟩
  intro (trajectory : StochasticEpisodeBatchTrajectory mdp episodes)
    (htrajectory : trajectory ∉ event)
    (round : Fin rounds)
  cases round with
  | mk value hvalue =>
      cases value with
      | zero =>
          have hfixed :=
            initialTable.exploratoryPolicy_iidStochasticTrajectoryFamilyMeasure_allCoordinate_optimism_and_expectedRegret_of_pathSupport_explicitCalibration
              rewardSource initialState explorationRate hexplorationRate
                episodes hepisodes varianceProxy law htotal
                localCountDelta hlocalCountPos hlocalCountLeOne
                localRewardDelta hlocalRewardPos hlocalRewardLeOne
                defaultState rewardBound hrewardBound support visitFloor hfloor
                hmargin hcontraction
          have hnot' : trajectory 0 ∉
              rewardSource.stochasticAllCoordinateEmpiricalModelBadEvent
                (initialTable.exploratoryPolicy explorationRate hexplorationRate)
                initialState episodes varianceProxy
                  localCountDelta localRewardDelta := by
            simpa [source, localCountDelta, localRewardDelta,
              AdaptiveStochasticEpisodeBatchSource.policyAt, exploratorySource]
              using
                (AdaptiveStochasticEpisodeBatchSource.policyAt_batch_not_mem_allCoordinateEmpiricalModelBadEvent
                  (mdp := mdp) (initialState := initialState) (episodes := episodes)
                  (rounds := rounds) source trajectory varianceProxy countDelta
                    rewardDelta htrajectory (⟨0, hvalue⟩ : Fin rounds))
          exact hfixed.2.2 (trajectory 0) hnot'
      | succ n =>
          let table := successorTable defaultState rewardBudget transitionBudget n
            (Preorder.frestrictLe n trajectory)
          have hfixed :=
            table.exploratoryPolicy_iidStochasticTrajectoryFamilyMeasure_allCoordinate_optimism_and_expectedRegret_of_pathSupport_explicitCalibration
              rewardSource initialState explorationRate hexplorationRate
                episodes hepisodes varianceProxy law htotal
                localCountDelta hlocalCountPos hlocalCountLeOne
                localRewardDelta hlocalRewardPos hlocalRewardLeOne
                defaultState rewardBound hrewardBound support visitFloor hfloor
                hmargin hcontraction
          have hnot' : trajectory (n + 1) ∉
              rewardSource.stochasticAllCoordinateEmpiricalModelBadEvent
                (table.exploratoryPolicy explorationRate hexplorationRate)
                initialState episodes varianceProxy
                  localCountDelta localRewardDelta := by
            simpa [source, table, localCountDelta, localRewardDelta,
              AdaptiveStochasticEpisodeBatchSource.policyAt, exploratorySource]
              using
                (AdaptiveStochasticEpisodeBatchSource.policyAt_batch_not_mem_allCoordinateEmpiricalModelBadEvent
                  (mdp := mdp) (initialState := initialState) (episodes := episodes)
                  (rounds := rounds) source trajectory varianceProxy countDelta
                    rewardDelta htrajectory (⟨n + 1, hvalue⟩ : Fin rounds))
          exact hfixed.2.2 (trajectory (n + 1)) hnot'

end AdaptiveStochasticSampledEmpiricalOptimisticSource
end FiniteHorizonRL
end BanditRLProof
