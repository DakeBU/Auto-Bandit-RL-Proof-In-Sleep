import BanditRLProof.RL.FiniteHorizonAdaptiveStochasticRewardSampledEmpiricalOptimisticSelfConsistentCausalRealizedSuccessorRegret
import BanditRLProof.RL.FiniteHorizonAdaptiveStochasticRewardSampledEmpiricalOptimisticSelfConsistentExplicitRate
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# Explicit weighted rate for the heterogeneous causal sampled source

The causal source uses a genuinely round-varying batch size.  Its regret rate
therefore cannot reuse the constant-window `episodes * rounds` algebra.  This
module keeps the exact successor mass and proves that the corresponding
positive-weight average of the coordinatewise scheduled rate tends to zero.

The return proxy is also identified exactly as successor episode mass times
the one-episode globally centered proxy.  The final consumer keeps a constant
return share `1 / 2`; the cumulative model-event budget is the existing exact
finite sum and is not claimed to vanish with the prefix.  Consequently this is
a causal finite-prefix rate theorem, not convergence in probability, an
almost-sure result, an anytime theorem, a minimax rate, or complete UCB-VI.
-/

open Asymptotics Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory Topology BigOperators

namespace BanditRLProof

/-- A finite average with positive natural-number weights. -/
noncomputable def natWeightedAverage
    (weight : Nat -> Nat) (value : Nat -> Real) (rounds : Nat) : Real :=
  (Finset.range rounds).sum (fun t => (weight t : Real) * value t) /
    (Finset.range rounds).sum (fun t => (weight t : Real))

/-- Positive natural weights preserve a zero limit under finite weighted averaging. -/
theorem tendsto_natWeightedAverage_zero
    (weight : Nat -> Nat) (hweight : forall t, 0 < weight t)
    (value : Nat -> Real) (hvalue : Tendsto value atTop (nhds 0)) :
    Tendsto (natWeightedAverage weight value) atTop (nhds 0) := by
  have hweightNonneg : 0 <= fun t => (weight t : Real) := by
    intro t
    positivity
  have hweightOne : forall t, (1 : Real) <= (weight t : Real) := by
    intro t
    exact_mod_cast hweight t
  have hsumAtTop : Tendsto
      (fun n => (Finset.range n).sum (fun t => (weight t : Real)))
      atTop atTop := by
    apply tendsto_atTop_mono (fun n => ?_) tendsto_natCast_atTop_atTop
    calc
      (n : Real) = (Finset.range n).sum (fun _ => (1 : Real)) := by simp
      _ <= (Finset.range n).sum (fun t => (weight t : Real)) :=
        Finset.sum_le_sum fun t _ => hweightOne t
  have hvalueLittle : value =o[atTop] fun _ => (1 : Real) :=
    (isLittleO_one_iff Real).2 hvalue
  have hweightedLittle :
      (fun t => (weight t : Real) * value t) =o[atTop]
        fun t => (weight t : Real) := by
    simpa [mul_comm] using hvalueLittle.mul_isBigO
      (isBigO_refl (fun t => (weight t : Real)) atTop)
  have hsumLittle := hweightedLittle.sum_range hweightNonneg hsumAtTop
  simpa [natWeightedAverage] using hsumLittle.tendsto_div_nhds_zero

namespace FiniteHorizonRL

universe u v

variable {State : Type u} {Action : Type v}
    [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action]
    [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action]

namespace HeterogeneousAdaptiveStochasticEpisodeBatchSource

omit [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action]
    [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The successor episode mass is the corresponding range sum. -/
theorem successorEpisodeMass_eq_sum_range
    (episodes : Nat -> Nat) (rounds : Nat) :
    successorEpisodeMass episodes rounds =
      (Finset.range rounds).sum (fun t => (episodes (t + 1) : Real)) := by
  unfold successorEpisodeMass
  rw [← Fin.sum_univ_eq_sum_range]

omit [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action]
    [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- Positive coordinate batch sizes make successor mass diverge. -/
theorem successorEpisodeMass_tendsto_atTop
    (episodes : Nat -> Nat) (hepisodes : forall t, 0 < episodes t) :
    Tendsto (successorEpisodeMass episodes) atTop atTop := by
  rw [show successorEpisodeMass episodes = fun rounds =>
      (Finset.range rounds).sum (fun t => (episodes (t + 1) : Real)) by
    funext rounds
    exact successorEpisodeMass_eq_sum_range episodes rounds]
  apply tendsto_atTop_mono (fun n => ?_) tendsto_natCast_atTop_atTop
  calc
    (n : Real) = (Finset.range n).sum (fun _ => (1 : Real)) := by simp
    _ <= (Finset.range n).sum (fun t => (episodes (t + 1) : Real)) :=
      Finset.sum_le_sum fun t _ => by exact_mod_cast hepisodes (t + 1)

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The heterogeneous global return proxy is exactly linear in successor mass. -/
theorem cumulativeSuccessorGlobalReturnVarianceProxy_coe
    (mdp : MDP State Action) (episodes : Nat -> Nat) (rounds : Nat)
    (rewardBound rewardVarianceProxy : NNReal) :
    ((cumulativeSuccessorGlobalReturnVarianceProxy mdp episodes rounds
        rewardBound rewardVarianceProxy : NNReal) : Real) =
      successorEpisodeMass episodes rounds *
        (mdp.globalReturnDeviationPerEpisodeVarianceProxy
          rewardBound rewardVarianceProxy : Real) := by
  unfold cumulativeSuccessorGlobalReturnVarianceProxy
  rw [Finset.sum_range_succ']
  simp only [MDP.iidGlobalSampledCumulativeReturnDeviationVarianceProxy_eq]
  push_cast
  rw [successorEpisodeMass_eq_sum_range]
  rw [Finset.sum_mul]
  ring

/-- Globally centered successor-return radius divided by actual successor mass. -/
noncomputable def normalizedSuccessorGlobalReturnConfidenceRadius
    (mdp : MDP State Action) (episodes : Nat -> Nat) (rounds : Nat)
    (rewardBound rewardVarianceProxy : NNReal) (delta : Real) : Real :=
  Concentration.subGaussianSumConfidenceRadius
      (cumulativeSuccessorGlobalReturnVarianceProxy mdp episodes rounds
        rewardBound rewardVarianceProxy) delta /
    successorEpisodeMass episodes rounds

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- Exact square-root formula for the heterogeneous normalized return radius. -/
theorem normalizedSuccessorGlobalReturnConfidenceRadius_eq
    (mdp : MDP State Action) (episodes : Nat -> Nat) (rounds : Nat)
    (rewardBound rewardVarianceProxy : NNReal) (delta : Real)
    (hmass : 0 < successorEpisodeMass episodes rounds)
    (hdelta : 0 < delta) (hdelta_le_one : delta <= 1) :
    normalizedSuccessorGlobalReturnConfidenceRadius mdp episodes rounds
        rewardBound rewardVarianceProxy delta =
      Real.sqrt
        (2 * (mdp.globalReturnDeviationPerEpisodeVarianceProxy
              rewardBound rewardVarianceProxy : Real) *
            Real.log (2 / delta) /
          successorEpisodeMass episodes rounds) := by
  have hlog : 0 <= Real.log (2 / delta) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hdelta]
    linarith
  have hradiusSq :=
    Concentration.subGaussianSumConfidenceRadius_sq
      (cumulativeSuccessorGlobalReturnVarianceProxy mdp episodes rounds
        rewardBound rewardVarianceProxy) delta hdelta hdelta_le_one
  rw [cumulativeSuccessorGlobalReturnVarianceProxy_coe] at hradiusSq
  have hsqrtSq :
      (Real.sqrt
        (2 * (mdp.globalReturnDeviationPerEpisodeVarianceProxy
              rewardBound rewardVarianceProxy : Real) *
            Real.log (2 / delta) /
          successorEpisodeMass episodes rounds)) ^ 2 =
        2 * (mdp.globalReturnDeviationPerEpisodeVarianceProxy
              rewardBound rewardVarianceProxy : Real) *
            Real.log (2 / delta) /
          successorEpisodeMass episodes rounds := by
    rw [Real.sq_sqrt]
    positivity
  have hlhsNonneg :
      0 <= normalizedSuccessorGlobalReturnConfidenceRadius mdp episodes rounds
        rewardBound rewardVarianceProxy delta := by
    unfold normalizedSuccessorGlobalReturnConfidenceRadius
    exact div_nonneg
      (Concentration.subGaussianSumConfidenceRadius_nonneg _ _) hmass.le
  have hrhsNonneg :
      0 <= Real.sqrt
        (2 * (mdp.globalReturnDeviationPerEpisodeVarianceProxy
              rewardBound rewardVarianceProxy : Real) *
            Real.log (2 / delta) /
          successorEpisodeMass episodes rounds) := Real.sqrt_nonneg _
  have hsq :
      (normalizedSuccessorGlobalReturnConfidenceRadius mdp episodes rounds
        rewardBound rewardVarianceProxy delta) ^ 2 =
      (Real.sqrt
        (2 * (mdp.globalReturnDeviationPerEpisodeVarianceProxy
              rewardBound rewardVarianceProxy : Real) *
            Real.log (2 / delta) /
          successorEpisodeMass episodes rounds)) ^ 2 := by
    unfold normalizedSuccessorGlobalReturnConfidenceRadius
    rw [div_pow, hradiusSq, hsqrtSq]
    field_simp [ne_of_gt hmass]
  nlinarith

/-- Fixed-half return envelope on the actual heterogeneous successor mass. -/
noncomputable def fixedHalfSuccessorGlobalReturnRateEnvelope
    (mdp : MDP State Action) (episodes : Nat -> Nat) (rounds : Nat)
    (rewardBound rewardVarianceProxy : NNReal) : Real :=
  Real.sqrt
    (2 * (mdp.globalReturnDeviationPerEpisodeVarianceProxy
          rewardBound rewardVarianceProxy : Real) * Real.log 4 /
      successorEpisodeMass episodes rounds)

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- At confidence share one half, the normalized radius is the fixed-half envelope. -/
theorem normalizedSuccessorGlobalReturnConfidenceRadius_half_eq
    (mdp : MDP State Action) (episodes : Nat -> Nat) (rounds : Nat)
    (rewardBound rewardVarianceProxy : NNReal)
    (hmass : 0 < successorEpisodeMass episodes rounds) :
    normalizedSuccessorGlobalReturnConfidenceRadius mdp episodes rounds
        rewardBound rewardVarianceProxy (1 / 2) =
      fixedHalfSuccessorGlobalReturnRateEnvelope mdp episodes rounds
        rewardBound rewardVarianceProxy := by
  rw [normalizedSuccessorGlobalReturnConfidenceRadius_eq mdp episodes rounds
    rewardBound rewardVarianceProxy (1 / 2) hmass (by norm_num) (by norm_num)]
  unfold fixedHalfSuccessorGlobalReturnRateEnvelope
  norm_num

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The fixed-half heterogeneous return envelope vanishes with prefix length. -/
theorem fixedHalfSuccessorGlobalReturnRateEnvelope_tendsto_zero
    (mdp : MDP State Action) (episodes : Nat -> Nat)
    (hepisodes : forall t, 0 < episodes t)
    (rewardBound rewardVarianceProxy : NNReal) :
    Tendsto
      (fun rounds => fixedHalfSuccessorGlobalReturnRateEnvelope mdp episodes
        rounds rewardBound rewardVarianceProxy)
      atTop (nhds 0) := by
  have hmass := successorEpisodeMass_tendsto_atTop episodes hepisodes
  have hdiv : Tendsto
      (fun rounds =>
        (2 * (mdp.globalReturnDeviationPerEpisodeVarianceProxy
              rewardBound rewardVarianceProxy : Real) * Real.log 4) /
          successorEpisodeMass episodes rounds)
      atTop (nhds 0) := tendsto_const_nhds.div_atTop hmass
  simpa [fixedHalfSuccessorGlobalReturnRateEnvelope] using
    (Real.continuous_sqrt.tendsto 0).comp hdiv

end HeterogeneousAdaptiveStochasticEpisodeBatchSource

namespace AdaptiveStochasticSampledEmpiricalOptimisticSource

/-- Coordinatewise planning rate for the genuinely causal successor batch. -/
noncomputable def selfConsistentScheduledCausalPlanningRateAt
    (mdp : MDP State Action) (t : Nat) : Real :=
  (mdp.horizon : Real) *
      (2 *
        (1 / (AdaptiveEpisodeBatchSource.decayingExplorationScale t : Real) ^ 2 +
          AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledTransitionBudgetRateEnvelope
            mdp t)) +
    exploratoryBehaviorRegretCharge mdp
      (AdaptiveEpisodeBatchSource.decayingExplorationRate (t + 1)) 1

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The causal coordinatewise planning rate vanishes. -/
theorem selfConsistentScheduledCausalPlanningRateAt_tendsto_zero
    (mdp : MDP State Action) :
    Tendsto (selfConsistentScheduledCausalPlanningRateAt mdp)
      atTop (nhds 0) := by
  have hinvSq : Tendsto
      (fun n : Nat =>
        1 / (AdaptiveEpisodeBatchSource.decayingExplorationScale n : Real) ^ 2)
      atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop
      AdaptiveStochasticEpisodeBatchSource.decayingExplorationScale_sq_tendsto_atTop
  have htransition : Tendsto
      (AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledTransitionBudgetRateEnvelope
        mdp)
      atTop (nhds 0) := by
    unfold AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledTransitionBudgetRateEnvelope
    simpa using tendsto_const_nhds.mul
      (AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledTransitionContractionEnvelope_tendsto_zero
        mdp)
  have hmodel : Tendsto
      (fun n : Nat => (mdp.horizon : Real) *
        (2 *
          (1 / (AdaptiveEpisodeBatchSource.decayingExplorationScale n : Real) ^ 2 +
            AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledTransitionBudgetRateEnvelope
              mdp n)))
      atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul
      (tendsto_const_nhds.mul (hinvSq.add htransition))
  have hexploration : Tendsto
      (fun n : Nat => exploratoryBehaviorRegretCharge mdp
        (AdaptiveEpisodeBatchSource.decayingExplorationRate (n + 1)) 1)
      atTop (nhds 0) := by
    simpa using
      (AdaptiveEpisodeBatchSource.decayingExplorationBehaviorCharge_tendsto_zero mdp).comp
          (tendsto_add_atTop_nat 1)
  unfold selfConsistentScheduledCausalPlanningRateAt
  simpa using hmodel.add hexploration

/-- Positive scheduled successor weights applied to the coordinatewise rate. -/
noncomputable def selfConsistentScheduledCausalWeightedPlanningRateEnvelope
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (rounds : Nat) : Real :=
  natWeightedAverage
    (fun t => AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
      mdp varianceProxy baseVisitFloor (t + 1))
    (selfConsistentScheduledCausalPlanningRateAt mdp) rounds

/-- The exact causal planning average is controlled by the weighted rate envelope. -/
theorem selfConsistentScheduledCausalSuccessorPlanningAverageBound_le_rateEnvelope
    (mdp : MDP State Action) (varianceProxy : NNReal)
    {baseVisitFloor : Real} (hhorizon : 0 < mdp.horizon)
    (hbaseVisitFloor : 0 < baseVisitFloor) (rounds : Nat) :
    selfConsistentScheduledCausalSuccessorPlanningAverageBound mdp
        varianceProxy baseVisitFloor rounds <=
      selfConsistentScheduledCausalWeightedPlanningRateEnvelope mdp
        varianceProxy baseVisitFloor rounds := by
  let episodes := fun t =>
    AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
      mdp varianceProxy baseVisitFloor t
  let rewardBudget := fun t =>
    AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledRewardBudget
      mdp varianceProxy baseVisitFloor t
  let transitionBudget := fun t =>
    AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledTransitionBudget
      mdp varianceProxy baseVisitFloor t
  have hcoordinate : forall t,
      (mdp.horizon : Real) *
          (2 * (rewardBudget t + transitionBudget t)) +
        exploratoryBehaviorRegretCharge mdp
          (AdaptiveEpisodeBatchSource.decayingExplorationRate (t + 1)) 1 <=
      selfConsistentScheduledCausalPlanningRateAt mdp t := by
    intro t
    have hreward : rewardBudget t <=
        1 / (AdaptiveEpisodeBatchSource.decayingExplorationScale t : Real) ^ 2 := by
      dsimp [rewardBudget]
      exact (AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledRewardBudget_lt_inv_scale_sq
        mdp
          varianceProxy hhorizon hbaseVisitFloor t).le
    have htransition : transitionBudget t <=
        AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledTransitionBudgetRateEnvelope
          mdp t := by
      dsimp [transitionBudget]
      exact AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledTransitionBudget_le_rateEnvelope
        mdp
          varianceProxy hhorizon hbaseVisitFloor t
    have hscaled := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (add_le_add hreward htransition)
        (by norm_num : (0 : Real) <= 2))
      (by positivity : (0 : Real) <= (mdp.horizon : Real))
    unfold selfConsistentScheduledCausalPlanningRateAt
    exact add_le_add hscaled (le_refl _)
  have hcumFin :
      selfConsistentScheduledCausalSuccessorPlanningCumulativeBound mdp
          varianceProxy baseVisitFloor rounds <=
        ∑ round : Fin rounds,
          (episodes ((round : Nat) + 1) : Real) *
            selfConsistentScheduledCausalPlanningRateAt mdp (round : Nat) := by
    unfold selfConsistentScheduledCausalSuccessorPlanningCumulativeBound
    apply Finset.sum_le_sum
    intro round _hround
    dsimp only
    exact mul_le_mul_of_nonneg_left (hcoordinate (round : Nat)) (by positivity)
  have hcum :
      selfConsistentScheduledCausalSuccessorPlanningCumulativeBound mdp
          varianceProxy baseVisitFloor rounds <=
        (Finset.range rounds).sum (fun t =>
          (episodes (t + 1) : Real) *
            selfConsistentScheduledCausalPlanningRateAt mdp t) := by
    calc
      selfConsistentScheduledCausalSuccessorPlanningCumulativeBound mdp
          varianceProxy baseVisitFloor rounds <=
          ∑ round : Fin rounds,
            (episodes ((round : Nat) + 1) : Real) *
              selfConsistentScheduledCausalPlanningRateAt mdp (round : Nat) :=
        hcumFin
      _ = _ := by
        rw [Fin.sum_univ_eq_sum_range (fun t : Nat =>
          (episodes (t + 1) : Real) *
            selfConsistentScheduledCausalPlanningRateAt mdp t)]
  unfold selfConsistentScheduledCausalSuccessorPlanningAverageBound
    selfConsistentScheduledCausalWeightedPlanningRateEnvelope
    natWeightedAverage
  rw [HeterogeneousAdaptiveStochasticEpisodeBatchSource.successorEpisodeMass_eq_sum_range]
  exact div_le_div_of_nonneg_right hcum (Finset.sum_nonneg fun _ _ => by positivity)

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The scheduled weighted causal planning envelope tends to zero. -/
theorem selfConsistentScheduledCausalWeightedPlanningRateEnvelope_tendsto_zero
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseVisitFloor : Real) :
    Tendsto
      (selfConsistentScheduledCausalWeightedPlanningRateEnvelope mdp
        varianceProxy baseVisitFloor)
      atTop (nhds 0) := by
  unfold selfConsistentScheduledCausalWeightedPlanningRateEnvelope
  exact tendsto_natWeightedAverage_zero _
    (fun t => AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes_pos
      mdp varianceProxy baseVisitFloor (t + 1))
    _ (selfConsistentScheduledCausalPlanningRateAt_tendsto_zero mdp)

/-- Fixed-half global return envelope for the scheduled causal source. -/
noncomputable def selfConsistentScheduledCausalReturnRateEnvelope
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (rounds : Nat) : Real :=
  HeterogeneousAdaptiveStochasticEpisodeBatchSource.fixedHalfSuccessorGlobalReturnRateEnvelope
    mdp
      (fun t => AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
        mdp varianceProxy baseVisitFloor t)
      rounds 1 varianceProxy

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The scheduled causal return envelope tends to zero. -/
theorem selfConsistentScheduledCausalReturnRateEnvelope_tendsto_zero
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseVisitFloor : Real) :
    Tendsto
      (selfConsistentScheduledCausalReturnRateEnvelope mdp varianceProxy
        baseVisitFloor)
      atTop (nhds 0) := by
  unfold selfConsistentScheduledCausalReturnRateEnvelope
  exact HeterogeneousAdaptiveStochasticEpisodeBatchSource.fixedHalfSuccessorGlobalReturnRateEnvelope_tendsto_zero
    mdp _
      (fun t => AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes_pos
        mdp varianceProxy baseVisitFloor t)
      1 varianceProxy

/-- Full deterministic realized-regret envelope on the causal successor prefix. -/
noncomputable def selfConsistentScheduledCausalRealizedSuccessorAverageRegretRateEnvelope
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (rounds : Nat) : Real :=
  selfConsistentScheduledCausalWeightedPlanningRateEnvelope mdp varianceProxy
      baseVisitFloor rounds +
    selfConsistentScheduledCausalReturnRateEnvelope mdp varianceProxy
      baseVisitFloor rounds

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The complete deterministic causal realized-regret envelope tends to zero. -/
theorem selfConsistentScheduledCausalRealizedSuccessorAverageRegretRateEnvelope_tendsto_zero
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseVisitFloor : Real) :
    Tendsto
      (selfConsistentScheduledCausalRealizedSuccessorAverageRegretRateEnvelope
        mdp varianceProxy baseVisitFloor)
      atTop (nhds 0) := by
  unfold selfConsistentScheduledCausalRealizedSuccessorAverageRegretRateEnvelope
  simpa using
    (selfConsistentScheduledCausalWeightedPlanningRateEnvelope_tendsto_zero
      mdp varianceProxy baseVisitFloor).add
    (selfConsistentScheduledCausalReturnRateEnvelope_tendsto_zero
      mdp varianceProxy baseVisitFloor)

/-
The deterministic regret envelope vanishes, but the exact finite-prefix model
failure budget below accumulates the early coordinate events.  This theorem
therefore deliberately stops at a finite-prefix certificate.
-/
theorem selfConsistentScheduledCausalSource_trajectoryMeasure_optimism_and_realizedSuccessorAverageRegret_le_explicitRateEnvelope
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace State] [StandardBorelSpace Action]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (varianceProxy : NNReal) (hvarianceProxy : 0 < varianceProxy)
    (law : rewardSource.UniformSubgaussianRewardLaw varianceProxy)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State)
    (support : ExploratoryPathSupport mdp initialState)
    (baseVisitFloor : Real)
    (hbaseFloor : ExploratoryPathUniformVisitFloor support 1 baseVisitFloor)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (hhorizon : 0 < mdp.horizon) (hbaseVisitFloor : 0 < baseVisitFloor)
    (rounds : Nat) (hrounds : 0 < rounds) :
    let episodes := fun t =>
      AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
        mdp varianceProxy baseVisitFloor t
    let rewardBudget := fun t =>
      AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledRewardBudget
        mdp varianceProxy baseVisitFloor t
    let transitionBudget := fun t =>
      AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledTransitionBudget
        mdp varianceProxy baseVisitFloor t
    let source := selfConsistentScheduledCausalSource mdp initialState
      rewardSource initialTable defaultState varianceProxy baseVisitFloor
    let event := selfConsistentScheduledCausalModelReturnBadEvent mdp
      initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor rounds (1 / 2)
    MeasurableSet event /\
      source.trajectoryMeasure event <=
        selfConsistentScheduledCausalModelReturnFailureBudget mdp rounds
          (1 / 2) /\
      forall trajectory, trajectory ∉ event ->
        (forall round : Fin rounds,
          let t := (round : Nat)
          let model := mdp.stochasticAllCoordinateEmpiricalFiniteBatchModel
            (episodes t)
            (mdp.sampledEpisodeBatchOfStochasticTrajectories
              (episodes t) (trajectory t))
            defaultState (rewardBudget t) (transitionBudget t)
          forall state,
            mdp.optimalValueRemaining mdp.horizon le_rfl state <=
              model.plan.upperValueRemaining mdp.horizon le_rfl state) /\
        source.realizedSuccessorAverageRegret trajectory rounds <=
          selfConsistentScheduledCausalRealizedSuccessorAverageRegretRateEnvelope
            mdp varianceProxy baseVisitFloor rounds := by
  dsimp only
  let episodes := fun t =>
    AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
      mdp varianceProxy baseVisitFloor t
  let rewardBudget := fun t =>
    AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledRewardBudget
      mdp varianceProxy baseVisitFloor t
  let transitionBudget := fun t =>
    AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledTransitionBudget
      mdp varianceProxy baseVisitFloor t
  let source := selfConsistentScheduledCausalSource mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor
  let event := selfConsistentScheduledCausalModelReturnBadEvent mdp
    initialState rewardSource initialTable defaultState varianceProxy
      baseVisitFloor rounds (1 / 2)
  have hparent :
      MeasurableSet event /\
        source.trajectoryMeasure event <=
          selfConsistentScheduledCausalModelReturnFailureBudget mdp rounds
            (1 / 2) /\
        forall trajectory, trajectory ∉ event ->
          (forall round : Fin rounds,
            let t := (round : Nat)
            let model := mdp.stochasticAllCoordinateEmpiricalFiniteBatchModel
              (episodes t)
              (mdp.sampledEpisodeBatchOfStochasticTrajectories
                (episodes t) (trajectory t))
              defaultState (rewardBudget t) (transitionBudget t)
            forall state,
              mdp.optimalValueRemaining mdp.horizon le_rfl state <=
                model.plan.upperValueRemaining mdp.horizon le_rfl state) /\
          source.realizedSuccessorAverageRegret trajectory rounds <=
            selfConsistentScheduledCausalSuccessorPlanningAverageBound mdp
                varianceProxy baseVisitFloor rounds +
              Concentration.subGaussianSumConfidenceRadius
                  (HeterogeneousAdaptiveStochasticEpisodeBatchSource.cumulativeSuccessorGlobalReturnVarianceProxy
                    mdp episodes rounds 1 varianceProxy) (1 / 2) /
                HeterogeneousAdaptiveStochasticEpisodeBatchSource.successorEpisodeMass
                  episodes rounds := by
    simpa [episodes, rewardBudget, transitionBudget, source, event] using
      selfConsistentScheduledCausalSource_trajectoryMeasure_optimism_and_realizedSuccessorAverageRegret
        mdp initialState rewardSource varianceProxy hvarianceProxy law
          initialTable defaultState support baseVisitFloor hbaseFloor
          hrewardBound hhorizon hbaseVisitFloor rounds hrounds (1 / 2)
          (by norm_num) (by norm_num)
  refine ⟨hparent.1, hparent.2.1, ?_⟩
  intro trajectory htrajectory
  have hcertificate := hparent.2.2 trajectory htrajectory
  refine ⟨hcertificate.1, ?_⟩
  have hplanning :=
    selfConsistentScheduledCausalSuccessorPlanningAverageBound_le_rateEnvelope
      mdp varianceProxy hhorizon hbaseVisitFloor rounds
  have hepisodes : forall t, 0 < episodes t := fun t =>
    AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes_pos
      mdp varianceProxy baseVisitFloor t
  have hmass : 0 <
      HeterogeneousAdaptiveStochasticEpisodeBatchSource.successorEpisodeMass
        episodes rounds :=
    HeterogeneousAdaptiveStochasticEpisodeBatchSource.successorEpisodeMass_pos
      episodes rounds hrounds hepisodes
  have hreturn :
      HeterogeneousAdaptiveStochasticEpisodeBatchSource.normalizedSuccessorGlobalReturnConfidenceRadius
          mdp episodes rounds 1 varianceProxy (1 / 2) =
        selfConsistentScheduledCausalReturnRateEnvelope mdp varianceProxy
          baseVisitFloor rounds := by
    rw [HeterogeneousAdaptiveStochasticEpisodeBatchSource.normalizedSuccessorGlobalReturnConfidenceRadius_half_eq
      mdp episodes rounds 1 varianceProxy hmass]
    rfl
  calc
    source.realizedSuccessorAverageRegret trajectory rounds <=
        selfConsistentScheduledCausalSuccessorPlanningAverageBound mdp
            varianceProxy baseVisitFloor rounds +
          Concentration.subGaussianSumConfidenceRadius
              (HeterogeneousAdaptiveStochasticEpisodeBatchSource.cumulativeSuccessorGlobalReturnVarianceProxy
                mdp episodes rounds 1 varianceProxy) (1 / 2) /
            HeterogeneousAdaptiveStochasticEpisodeBatchSource.successorEpisodeMass
              episodes rounds := hcertificate.2
    _ <= selfConsistentScheduledCausalWeightedPlanningRateEnvelope mdp
          varianceProxy baseVisitFloor rounds +
        HeterogeneousAdaptiveStochasticEpisodeBatchSource.normalizedSuccessorGlobalReturnConfidenceRadius
          mdp episodes rounds 1 varianceProxy (1 / 2) :=
      add_le_add hplanning (le_refl _)
    _ = selfConsistentScheduledCausalRealizedSuccessorAverageRegretRateEnvelope
          mdp varianceProxy baseVisitFloor rounds := by
      rw [hreturn]
      rfl

end AdaptiveStochasticSampledEmpiricalOptimisticSource

end FiniteHorizonRL

end BanditRLProof
