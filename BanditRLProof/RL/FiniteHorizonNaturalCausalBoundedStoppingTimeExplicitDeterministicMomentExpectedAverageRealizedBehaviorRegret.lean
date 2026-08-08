import BanditRLProof.ExpectationBochnerSums
import BanditRLProof.ConcentrationSubGaussian
import BanditRLProof.RL.FiniteHorizonNaturalCausalBoundedStoppingTimeExplicitExpectedAverageRealizedBehaviorRegret

/-!
# Deterministic-moment expected regret at a bounded stopping time

This module turns the exact stopped second moment from the previous expected
terminal into a finite deterministic budget. It uses finite-coordinate
selection and MGF moment control, not optional stopping.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace BanditRLProof.FiniteHorizonRL

universe u v

variable {State : Type u} {Action : Type v}
    [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action]
    [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action]

namespace AdaptiveStochasticSampledEmpiricalOptimisticSource

/-- The cumulative behavior expected-regret process has its deterministic
finite-prefix envelope. -/
theorem selfConsistentScheduledNaturalCausalCumulativeBehaviorExpectedRegretProcess_le_rounds_mul_two_horizon
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (rounds : Nat)
    (trajectory : HeterogeneousStochasticEpisodeBatchTrajectory mdp
      (fun t =>
        AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
          mdp varianceProxy baseVisitFloor t)) :
    selfConsistentScheduledNaturalCausalCumulativeBehaviorExpectedRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor rounds trajectory <=
      (rounds : Real) * (2 * (mdp.horizon : Real)) := by
  change
    (Finset.range rounds).sum (fun t =>
        selfConsistentScheduledNaturalCausalSuccessorPolicyExpectedRegretProcess
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor t trajectory) <=
      (rounds : Real) * (2 * (mdp.horizon : Real))
  calc
    (Finset.range rounds).sum (fun t =>
        selfConsistentScheduledNaturalCausalSuccessorPolicyExpectedRegretProcess
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor t trajectory) <=
        (Finset.range rounds).sum (fun _ => 2 * (mdp.horizon : Real)) := by
      exact Finset.sum_le_sum fun t _ =>
        selfConsistentScheduledNaturalCausalSuccessorPolicyExpectedRegretProcess_le_two_mul_horizon
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor hrewardBound t trajectory
    _ = (rounds : Real) * (2 * (mdp.horizon : Real)) := by simp

/-- Deterministic envelope for the second moment at one positive prefix. -/
noncomputable def selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretSecondMomentEnvelope
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (rounds : Nat) : Real :=
  8 * (mdp.horizon : Real) ^ 2 +
    (2 / (rounds : Real) ^ 2) *
      (4 *
        (selfConsistentScheduledNaturalCausalCumulativeReturnVarianceProxy mdp
          varianceProxy baseVisitFloor rounds : Real) *
        Real.exp (1 / 2 : Real))

/-- The deterministic coordinate second-moment envelope is nonnegative. -/
theorem selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretSecondMomentEnvelope_nonneg
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (rounds : Nat) :
    0 <= selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretSecondMomentEnvelope
      mdp varianceProxy baseVisitFloor rounds := by
  unfold selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretSecondMomentEnvelope
  positivity

/-- At every positive deterministic prefix, the exact average realized
behavior-regret second moment is bounded by the deterministic envelope. -/
theorem integral_sq_selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess_le_secondMomentEnvelope
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace State] [StandardBorelSpace Action]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (varianceProxy : NNReal)
    (law : rewardSource.UniformSubgaussianRewardLaw varianceProxy)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (baseVisitFloor : Real)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (rounds : Nat) (hrounds : 0 < rounds) :
    integral
        (selfConsistentScheduledCausalSource mdp initialState rewardSource
          initialTable defaultState varianceProxy baseVisitFloor).trajectoryMeasure
        (fun trajectory =>
          selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor rounds trajectory ^ 2) <=
      selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretSecondMomentEnvelope
        mdp varianceProxy baseVisitFloor rounds := by
  let mu := (selfConsistentScheduledCausalSource mdp initialState rewardSource
    initialTable defaultState varianceProxy baseVisitFloor).trajectoryMeasure
  let behavior :=
    selfConsistentScheduledNaturalCausalCumulativeBehaviorExpectedRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor rounds
  let deviation :=
    selfConsistentScheduledNaturalCausalCumulativeReturnDeviationProcess mdp
      initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor rounds
  let r : Real := rounds
  let horizon : Real := mdp.horizon
  let returnProxy :=
    selfConsistentScheduledNaturalCausalCumulativeReturnVarianceProxy mdp
      varianceProxy baseVisitFloor rounds
  have hr : 0 < r := by
    dsimp [r]
    exact_mod_cast hrounds
  have hhorizon : 0 <= horizon := by
    dsimp [horizon]
    positivity
  have hdeviationMGF : HasSubgaussianMGF deviation returnProxy mu := by
    simpa [deviation, returnProxy, mu] using
      selfConsistentScheduledNaturalCausalCumulativeReturnDeviationProcess_hasSubgaussianMGF
        mdp initialState rewardSource varianceProxy law initialTable defaultState
          baseVisitFloor hrewardBound rounds
  have hdeviationMoment :
      integral mu (fun trajectory => deviation trajectory ^ 2) <=
        4 * (returnProxy : Real) * Real.exp (1 / 2 : Real) :=
    Concentration.integral_sq_le_four_mul_proxy_mul_exp_half_of_hasSubgaussianMGF
      mu deviation returnProxy hdeviationMGF
  have hprocessSqIntegrable : Integrable
      (fun trajectory =>
        selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor rounds trajectory ^ 2) mu := by
    exact
      (memLp_two_selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource varianceProxy law initialTable defaultState
          baseVisitFloor hrewardBound rounds).integrable_sq
  have hdeviationSqIntegrable : Integrable
      (fun trajectory => deviation trajectory ^ 2) mu :=
    (hdeviationMGF.memLp 2).integrable_sq
  have hpoint : forall trajectory,
      selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor rounds trajectory ^ 2 <=
        8 * horizon ^ 2 +
          (2 / r ^ 2) * deviation trajectory ^ 2 := by
    intro trajectory
    have hbehavior_nonneg : 0 <= behavior trajectory := by
      exact
        selfConsistentScheduledNaturalCausalCumulativeBehaviorExpectedRegretProcess_nonneg
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor rounds trajectory
    have hbehavior_le :
        behavior trajectory <= r * (2 * horizon) := by
      simpa [behavior, r, horizon] using
        selfConsistentScheduledNaturalCausalCumulativeBehaviorExpectedRegretProcess_le_rounds_mul_two_horizon
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor hrewardBound rounds trajectory
    have hbehaviorBound_nonneg : 0 <= r * (2 * horizon) := by positivity
    have hbehavior_sq :
        behavior trajectory ^ 2 <= (r * (2 * horizon)) ^ 2 :=
      (sq_le_sq₀ hbehavior_nonneg hbehaviorBound_nonneg).2 hbehavior_le
    have hraw :
        (behavior trajectory - deviation trajectory) ^ 2 <=
          8 * horizon ^ 2 * r ^ 2 + 2 * deviation trajectory ^ 2 := by
      have hsub :
          (behavior trajectory - deviation trajectory) ^ 2 <=
            2 * behavior trajectory ^ 2 + 2 * deviation trajectory ^ 2 := by
        nlinarith [sq_nonneg (behavior trajectory + deviation trajectory)]
      calc
        (behavior trajectory - deviation trajectory) ^ 2 <=
            2 * behavior trajectory ^ 2 + 2 * deviation trajectory ^ 2 := hsub
        _ <= 2 * (r * (2 * horizon)) ^ 2 +
            2 * deviation trajectory ^ 2 := by gcongr
        _ = 8 * horizon ^ 2 * r ^ 2 + 2 * deviation trajectory ^ 2 := by ring
    rw [selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess_eq_expected_sub_deviation]
    change ((behavior trajectory - deviation trajectory) / r) ^ 2 <=
      8 * horizon ^ 2 + (2 / r ^ 2) * deviation trajectory ^ 2
    rw [div_pow]
    have hr_sq : 0 < r ^ 2 := sq_pos_of_pos hr
    rw [show 8 * horizon ^ 2 + (2 / r ^ 2) * deviation trajectory ^ 2 =
        (8 * horizon ^ 2 * r ^ 2 + 2 * deviation trajectory ^ 2) / r ^ 2 by
      field_simp]
    exact (div_le_div_iff_of_pos_right hr_sq).2 hraw
  have hrhsIntegrable : Integrable
      (fun trajectory => 8 * horizon ^ 2 +
        (2 / r ^ 2) * deviation trajectory ^ 2) mu :=
    (integrable_const (8 * horizon ^ 2)).add
      (hdeviationSqIntegrable.const_mul (2 / r ^ 2))
  have hintegral :
      integral mu
          (fun trajectory =>
            selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
              mdp initialState rewardSource initialTable defaultState varianceProxy
                baseVisitFloor rounds trajectory ^ 2) <=
        8 * horizon ^ 2 +
          (2 / r ^ 2) *
            integral mu (fun trajectory => deviation trajectory ^ 2) := by
    calc
      integral mu
          (fun trajectory =>
            selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
              mdp initialState rewardSource initialTable defaultState varianceProxy
                baseVisitFloor rounds trajectory ^ 2) <=
          integral mu (fun trajectory => 8 * horizon ^ 2 +
            (2 / r ^ 2) * deviation trajectory ^ 2) :=
        integral_mono hprocessSqIntegrable hrhsIntegrable hpoint
      _ = 8 * horizon ^ 2 +
          (2 / r ^ 2) *
            integral mu (fun trajectory => deviation trajectory ^ 2) := by
        rw [integral_add (integrable_const (8 * horizon ^ 2))
            (hdeviationSqIntegrable.const_mul (2 / r ^ 2)),
          integral_const, integral_const_mul]
        simp [MeasureTheory.probReal_univ]
  calc
    integral mu
        (fun trajectory =>
          selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor rounds trajectory ^ 2) <=
        8 * horizon ^ 2 +
          (2 / r ^ 2) *
            integral mu (fun trajectory => deviation trajectory ^ 2) := hintegral
    _ <= 8 * horizon ^ 2 +
        (2 / r ^ 2) *
          (4 * (returnProxy : Real) * Real.exp (1 / 2 : Real)) := by
      exact add_le_add (le_refl (8 * horizon ^ 2))
        (mul_le_mul_of_nonneg_left hdeviationMoment
          (show 0 <= 2 / r ^ 2 by positivity))
    _ = selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretSecondMomentEnvelope
        mdp varianceProxy baseVisitFloor rounds := by
      rfl

/-- A finite deterministic second-moment budget covering every positive
prefix up to `maxRounds`. -/
noncomputable def selfConsistentScheduledNaturalCausalBoundedStoppingExplicitSecondMomentBudget
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (maxRounds : Nat) : Real :=
  Finset.sum (Finset.Icc 1 maxRounds) fun rounds =>
    selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretSecondMomentEnvelope
      mdp varianceProxy baseVisitFloor rounds

/-- The deterministic finite-prefix second-moment budget is nonnegative. -/
theorem selfConsistentScheduledNaturalCausalBoundedStoppingExplicitSecondMomentBudget_nonneg
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (maxRounds : Nat) :
    0 <= selfConsistentScheduledNaturalCausalBoundedStoppingExplicitSecondMomentBudget
      mdp varianceProxy baseVisitFloor maxRounds := by
  unfold selfConsistentScheduledNaturalCausalBoundedStoppingExplicitSecondMomentBudget
  exact Finset.sum_nonneg fun rounds _ =>
    selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretSecondMomentEnvelope_nonneg
      mdp varianceProxy baseVisitFloor rounds

/-- A positive bounded stopping time selects one coordinate from the finite
prefix sum, so its exact second moment is bounded by the deterministic budget.
No optional-stopping theorem is used. -/
theorem selfConsistentScheduledNaturalCausalStoppedAverageRealizedBehaviorRegretSecondMoment_le_explicitBudget
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace State] [StandardBorelSpace Action]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (varianceProxy : NNReal)
    (law : rewardSource.UniformSubgaussianRewardLaw varianceProxy)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (baseVisitFloor : Real)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (tau : HeterogeneousStochasticEpisodeBatchTrajectory mdp
      (fun t =>
        AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
          mdp varianceProxy baseVisitFloor t) -> WithTop Nat)
    (htau : IsStoppingTime
      (selfConsistentScheduledNaturalCausalTrajectoryFiltration mdp initialState
        rewardSource initialTable defaultState varianceProxy baseVisitFloor) tau)
    (maxRounds : Nat)
    (htau_pos : forall trajectory, (1 : WithTop Nat) <= tau trajectory)
    (htau_le : forall trajectory, tau trajectory <= (maxRounds : WithTop Nat)) :
    selfConsistentScheduledNaturalCausalStoppedAverageRealizedBehaviorRegretSecondMoment
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor tau <=
      selfConsistentScheduledNaturalCausalBoundedStoppingExplicitSecondMomentBudget
        mdp varianceProxy baseVisitFloor maxRounds := by
  let mu := (selfConsistentScheduledCausalSource mdp initialState rewardSource
    initialTable defaultState varianceProxy baseVisitFloor).trajectoryMeasure
  let process :=
    selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor
  let stoppedRegret :=
    selfConsistentScheduledNaturalCausalStoppedAverageRealizedBehaviorRegret
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor tau
  have hcoordinateIntegrable : forall rounds,
      Integrable (fun trajectory => process rounds trajectory ^ 2) mu := by
    intro rounds
    exact
      (memLp_two_selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource varianceProxy law initialTable defaultState
          baseVisitFloor hrewardBound rounds).integrable_sq
  have hsumIntegrable : Integrable
      (fun trajectory =>
        (Finset.Icc 1 maxRounds).sum fun rounds =>
          process rounds trajectory ^ 2) mu := by
    exact IntegrabilitySums.integrable_finset_sum mu (Finset.Icc 1 maxRounds)
      (fun rounds trajectory => process rounds trajectory ^ 2)
      (fun rounds _ => hcoordinateIntegrable rounds)
  have hstoppedIntegrable : Integrable
      (fun trajectory => stoppedRegret trajectory ^ 2) mu := by
    exact
      (memLp_two_selfConsistentScheduledNaturalCausalStoppedAverageRealizedBehaviorRegret
        mdp initialState rewardSource varianceProxy law initialTable defaultState
          baseVisitFloor hrewardBound tau htau maxRounds htau_le).integrable_sq
  have hpoint : forall trajectory,
      stoppedRegret trajectory ^ 2 <=
        (Finset.Icc 1 maxRounds).sum fun rounds =>
          process rounds trajectory ^ 2 := by
    intro trajectory
    have hrange := one_le_untopA_and_untopA_le_of_withTop_bounds
      tau maxRounds htau_pos htau_le trajectory
    change process (tau trajectory).untopA trajectory ^ 2 <= _
    exact Finset.single_le_sum
      (fun rounds _ => sq_nonneg (process rounds trajectory))
      (Finset.mem_Icc.mpr hrange)
  have hintegral :
      integral mu (fun trajectory => stoppedRegret trajectory ^ 2) <=
        (Finset.Icc 1 maxRounds).sum fun rounds =>
          integral mu (fun trajectory => process rounds trajectory ^ 2) := by
    calc
      integral mu (fun trajectory => stoppedRegret trajectory ^ 2) <=
          integral mu (fun trajectory =>
            (Finset.Icc 1 maxRounds).sum fun rounds =>
              process rounds trajectory ^ 2) :=
        integral_mono hstoppedIntegrable hsumIntegrable hpoint
      _ = (Finset.Icc 1 maxRounds).sum fun rounds =>
          integral mu (fun trajectory => process rounds trajectory ^ 2) := by
        exact ExpectationBochnerSums.integral_finset_sum mu
          (Finset.Icc 1 maxRounds)
          (fun rounds trajectory => process rounds trajectory ^ 2)
          (fun rounds _ => hcoordinateIntegrable rounds)
  unfold selfConsistentScheduledNaturalCausalStoppedAverageRealizedBehaviorRegretSecondMoment
    selfConsistentScheduledNaturalCausalBoundedStoppingExplicitSecondMomentBudget
  change integral mu (fun trajectory => stoppedRegret trajectory ^ 2) <= _
  calc
    integral mu (fun trajectory => stoppedRegret trajectory ^ 2) <=
        (Finset.Icc 1 maxRounds).sum fun rounds =>
          integral mu (fun trajectory => process rounds trajectory ^ 2) := hintegral
    _ <= (Finset.Icc 1 maxRounds).sum fun rounds =>
        selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretSecondMomentEnvelope
          mdp varianceProxy baseVisitFloor rounds := by
      exact Finset.sum_le_sum fun rounds hrounds =>
        integral_sq_selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess_le_secondMomentEnvelope
          mdp initialState rewardSource varianceProxy law initialTable defaultState
            baseVisitFloor hrewardBound rounds (Finset.mem_Icc.mp hrounds).1

/-
Terminal deterministic-moment expected-regret route. The exact stopped second
moment is retained as a local quantity but exposed with a finite deterministic
upper budget.
-/
theorem
    selfConsistentScheduledCausalSource_boundedStoppingTimeExplicitDeterministicMomentExpectedAverageRealizedBehaviorRegret
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
    (tau : HeterogeneousStochasticEpisodeBatchTrajectory mdp
      (fun t =>
        AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
          mdp varianceProxy baseVisitFloor t) -> WithTop Nat)
    (htau : IsStoppingTime
      (selfConsistentScheduledNaturalCausalTrajectoryFiltration mdp initialState
        rewardSource initialTable defaultState varianceProxy baseVisitFloor) tau)
    (maxRounds : Nat) (hmaxRounds : 0 < maxRounds)
    (htau_pos : forall trajectory, (1 : WithTop Nat) <= tau trajectory)
    (htau_le : forall trajectory, tau trajectory <= (maxRounds : WithTop Nat)) :
    let source := selfConsistentScheduledCausalSource mdp initialState
      rewardSource initialTable defaultState varianceProxy baseVisitFloor
    let returnDeltaAt := fun _ : Nat =>
      selfConsistentScheduledNaturalCausalBoundedStoppingEqualReturnShare
        maxRounds (1 / 8 : Real)
    let event :=
      selfConsistentScheduledNaturalCausalBoundedStoppingSingleModelReturnBadEvent
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor maxRounds (1 / 8 : Real)
    let goodEvent := event.compl
    let stoppedRegret :=
      selfConsistentScheduledNaturalCausalStoppedAverageRealizedBehaviorRegret
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor tau
    let stoppedRate :=
      selfConsistentScheduledNaturalCausalStoppedRealizedAverageLogarithmicRate
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor returnDeltaAt tau
    let rateBudget :=
      selfConsistentScheduledNaturalCausalBoundedStoppingExplicitExpectedRateBudget
        mdp varianceProxy baseVisitFloor maxRounds
    let secondMoment :=
      selfConsistentScheduledNaturalCausalStoppedAverageRealizedBehaviorRegretSecondMoment
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor tau
    let momentBudget :=
      selfConsistentScheduledNaturalCausalBoundedStoppingExplicitSecondMomentBudget
        mdp varianceProxy baseVisitFloor maxRounds
    MemLp stoppedRegret 2 source.trajectoryMeasure /\
      MeasurableSet event /\
      source.trajectoryMeasure event <= ENNReal.ofReal (1 / 4 : Real) /\
      (3 / 4 : Real) <= source.trajectoryMeasure.real goodEvent /\
      0 <= rateBudget /\
      0 <= momentBudget /\
      secondMoment <= momentBudget /\
      integral source.trajectoryMeasure
          (event.indicator (fun trajectory => |stoppedRegret trajectory|)) <=
        (1 / 2 : Real) * Real.sqrt momentBudget /\
      integral source.trajectoryMeasure stoppedRegret <=
        rateBudget + (1 / 2 : Real) * Real.sqrt momentBudget /\
      forall trajectory, trajectory ∈ goodEvent ->
        stoppedRegret trajectory <= stoppedRate trajectory := by
  dsimp only
  let source := selfConsistentScheduledCausalSource mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor
  let returnDeltaAt := fun _ : Nat =>
    selfConsistentScheduledNaturalCausalBoundedStoppingEqualReturnShare
      maxRounds (1 / 8 : Real)
  let event :=
    selfConsistentScheduledNaturalCausalBoundedStoppingSingleModelReturnBadEvent
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor maxRounds (1 / 8 : Real)
  let goodEvent := event.compl
  let stoppedRegret :=
    selfConsistentScheduledNaturalCausalStoppedAverageRealizedBehaviorRegret
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor tau
  let stoppedRate :=
    selfConsistentScheduledNaturalCausalStoppedRealizedAverageLogarithmicRate
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor returnDeltaAt tau
  let rateBudget :=
    selfConsistentScheduledNaturalCausalBoundedStoppingExplicitExpectedRateBudget
      mdp varianceProxy baseVisitFloor maxRounds
  let secondMoment :=
    selfConsistentScheduledNaturalCausalStoppedAverageRealizedBehaviorRegretSecondMoment
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor tau
  let momentBudget :=
    selfConsistentScheduledNaturalCausalBoundedStoppingExplicitSecondMomentBudget
      mdp varianceProxy baseVisitFloor maxRounds
  have hparent :=
    selfConsistentScheduledCausalSource_boundedStoppingTimeExplicitExpectedAverageRealizedBehaviorRegret
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor tau htau maxRounds hmaxRounds htau_pos htau_le
  rcases hparent with
    ⟨hmem, heventMeasurable, heventTail, hgoodMass, hrateBudget,
      _hsecondMomentNonneg, hoverflow, hexpect, hpathwise⟩
  have hmomentBudget : 0 <= momentBudget := by
    simpa [momentBudget] using
      selfConsistentScheduledNaturalCausalBoundedStoppingExplicitSecondMomentBudget_nonneg
        mdp varianceProxy baseVisitFloor maxRounds
  have hmoment : secondMoment <= momentBudget := by
    simpa [secondMoment, momentBudget] using
      selfConsistentScheduledNaturalCausalStoppedAverageRealizedBehaviorRegretSecondMoment_le_explicitBudget
        mdp initialState rewardSource varianceProxy law initialTable defaultState
          baseVisitFloor hrewardBound tau htau maxRounds htau_pos htau_le
  have hsqrt : Real.sqrt secondMoment <= Real.sqrt momentBudget :=
    Real.sqrt_le_sqrt hmoment
  have hoverflowDeterministic :
      integral source.trajectoryMeasure
          (event.indicator (fun trajectory => |stoppedRegret trajectory|)) <=
        (1 / 2 : Real) * Real.sqrt momentBudget :=
    hoverflow.trans (mul_le_mul_of_nonneg_left hsqrt (by norm_num))
  have hexpectDeterministic :
      integral source.trajectoryMeasure stoppedRegret <=
        rateBudget + (1 / 2 : Real) * Real.sqrt momentBudget :=
    hexpect.trans (add_le_add (le_refl rateBudget)
      (mul_le_mul_of_nonneg_left hsqrt (by norm_num)))
  exact
    ⟨hmem, heventMeasurable, heventTail, hgoodMass, hrateBudget,
      hmomentBudget, hmoment, hoverflowDeterministic, hexpectDeterministic,
      hpathwise⟩

end AdaptiveStochasticSampledEmpiricalOptimisticSource
end BanditRLProof.FiniteHorizonRL
