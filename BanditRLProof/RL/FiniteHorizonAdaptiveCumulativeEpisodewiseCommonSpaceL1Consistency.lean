import BanditRLProof.RL.FiniteHorizonAdaptiveCumulativeEpisodewiseCommonSpaceExpectedConsistency
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# Common-space L1 realized behavior consistency

This module packages the compiled expected absolute realized-regret convergence
in Mathlib's native `MemLp`, `eLpNorm`, and `Lp` interfaces.  The underlying
probability space is still the independent product of complete scheduled
finite-window experiments; no nested causal coupling is constructed here.
-/

open Filter MeasureTheory
open scoped ENNReal NNReal ProbabilityTheory Topology

universe u v

namespace BanditRLProof.FiniteHorizonRL

variable {State : Type u} {Action : Type v}
    [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action]
    [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action]

namespace AdaptiveCumulativeEmpiricalOptimisticSource

/-- Every scheduled common-space realized-regret coordinate belongs to `L1`. -/
theorem memLp_one_decayingExplorationEpisodewiseRealizedBehaviorRegretProcess
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (baseVisitFloor : Real)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (n : Nat) :
    MemLp
      (decayingExplorationEpisodewiseRealizedBehaviorRegretProcess mdp
        initialState initialTable defaultState baseVisitFloor n)
      1
      (decayingExplorationEpisodewiseCommonMeasure mdp initialState
        initialTable defaultState baseVisitFloor) := by
  rw [memLp_one_iff_integrable]
  exact integrable_decayingExplorationEpisodewiseRealizedBehaviorRegretProcess
    mdp initialState initialTable defaultState baseVisitFloor hrewardBound n

/-- At exponent one, the `eLpNorm` is exactly the lifted expected absolute regret. -/
theorem eLpNorm_one_decayingExplorationEpisodewiseRealizedBehaviorRegretProcess_eq
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (baseVisitFloor : Real)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (n : Nat) :
    eLpNorm
        (decayingExplorationEpisodewiseRealizedBehaviorRegretProcess mdp
          initialState initialTable defaultState baseVisitFloor n)
        1
        (decayingExplorationEpisodewiseCommonMeasure mdp initialState
          initialTable defaultState baseVisitFloor) =
      ENNReal.ofReal
        (decayingExplorationEpisodewiseExpectedAbsoluteRealizedBehaviorRegret
          mdp initialState initialTable defaultState baseVisitFloor n) := by
  rw [MemLp.eLpNorm_eq_integral_rpow_norm one_ne_zero ENNReal.one_ne_top
    (memLp_one_decayingExplorationEpisodewiseRealizedBehaviorRegretProcess
      mdp initialState initialTable defaultState baseVisitFloor hrewardBound n)]
  simp [decayingExplorationEpisodewiseExpectedAbsoluteRealizedBehaviorRegret,
    Real.norm_eq_abs]

/-- The exponent-one extended `Lp` norm of the scheduled process tends to zero. -/
theorem eLpNorm_one_decayingExplorationEpisodewiseRealizedBehaviorRegretProcess_tendsto_zero
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (baseVisitFloor : Real)
    (hbatchBorel : forall n, StandardBorelSpace
      (EpisodeBatch mdp
        (AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes
          mdp baseVisitFloor n)))
    (htrajectoryBorel : forall n, StandardBorelSpace
      (EpisodeBatchTrajectory mdp
        (AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes
          mdp baseVisitFloor n)))
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State)
    (support : ExploratoryPathSupport mdp initialState)
    (hbaseFloor : ExploratoryPathUniformVisitFloor support 1 baseVisitFloor)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (hhorizon : 0 < mdp.horizon) (hbaseVisitFloor : 0 < baseVisitFloor) :
    Tendsto
      (fun n => eLpNorm
        (decayingExplorationEpisodewiseRealizedBehaviorRegretProcess mdp
          initialState initialTable defaultState baseVisitFloor n)
        1
        (decayingExplorationEpisodewiseCommonMeasure mdp initialState
          initialTable defaultState baseVisitFloor))
      atTop (nhds 0) := by
  have hexpected :=
    (exploratorySource_decayingExplorationEpisodewiseCommonMeasure_integrable_expectedAbsoluteRealizedBehaviorRegret_tendsto_zero
      mdp initialState baseVisitFloor hbatchBorel htrajectoryBorel initialTable
      defaultState support hbaseFloor hrewardBound hhorizon hbaseVisitFloor).2.2
  have hofReal := (ENNReal.continuous_ofReal.tendsto 0).comp hexpected
  simpa only [ENNReal.ofReal_zero,
    eLpNorm_one_decayingExplorationEpisodewiseRealizedBehaviorRegretProcess_eq
      mdp initialState initialTable defaultState baseVisitFloor hrewardBound]
    using hofReal

/-- Canonical `L1` convergence form: the norm of the difference from zero tends to zero. -/
theorem eLpNorm_one_decayingExplorationEpisodewiseRealizedBehaviorRegretProcess_sub_zero_tendsto_zero
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (baseVisitFloor : Real)
    (hbatchBorel : forall n, StandardBorelSpace
      (EpisodeBatch mdp
        (AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes
          mdp baseVisitFloor n)))
    (htrajectoryBorel : forall n, StandardBorelSpace
      (EpisodeBatchTrajectory mdp
        (AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes
          mdp baseVisitFloor n)))
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State)
    (support : ExploratoryPathSupport mdp initialState)
    (hbaseFloor : ExploratoryPathUniformVisitFloor support 1 baseVisitFloor)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (hhorizon : 0 < mdp.horizon) (hbaseVisitFloor : 0 < baseVisitFloor) :
    Tendsto
      (fun n => eLpNorm
        (decayingExplorationEpisodewiseRealizedBehaviorRegretProcess mdp
            initialState initialTable defaultState baseVisitFloor n -
          (fun _ => 0))
        1
        (decayingExplorationEpisodewiseCommonMeasure mdp initialState
          initialTable defaultState baseVisitFloor))
      atTop (nhds 0) := by
  have h :=
    eLpNorm_one_decayingExplorationEpisodewiseRealizedBehaviorRegretProcess_tendsto_zero
      mdp initialState baseVisitFloor hbatchBorel htrajectoryBorel initialTable
      defaultState support hbaseFloor hrewardBound hhorizon hbaseVisitFloor
  convert h using 1
  funext n
  apply eLpNorm_congr_ae
  exact Filter.Eventually.of_forall fun omega => by simp

/-- The scheduled realized-regret process represented as an `Lp Real 1` value. -/
noncomputable def decayingExplorationEpisodewiseRealizedBehaviorRegretLp
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (baseVisitFloor : Real)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (n : Nat) :
    Lp Real 1
      (decayingExplorationEpisodewiseCommonMeasure mdp initialState
        initialTable defaultState baseVisitFloor) :=
  (memLp_one_decayingExplorationEpisodewiseRealizedBehaviorRegretProcess
    mdp initialState initialTable defaultState baseVisitFloor hrewardBound n).toLp
      (decayingExplorationEpisodewiseRealizedBehaviorRegretProcess mdp
        initialState initialTable defaultState baseVisitFloor n)

/-- The named `Lp` coordinate represents the original process almost everywhere. -/
theorem decayingExplorationEpisodewiseRealizedBehaviorRegretLp_coeFn_ae_eq
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (baseVisitFloor : Real)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (n : Nat) :
    (decayingExplorationEpisodewiseRealizedBehaviorRegretLp mdp initialState
        initialTable defaultState baseVisitFloor hrewardBound n :
      DecayingExplorationEpisodewiseWindowSpace mdp baseVisitFloor -> Real) =ᵐ[
        decayingExplorationEpisodewiseCommonMeasure mdp initialState
          initialTable defaultState baseVisitFloor]
      decayingExplorationEpisodewiseRealizedBehaviorRegretProcess mdp
        initialState initialTable defaultState baseVisitFloor n := by
  exact (memLp_one_decayingExplorationEpisodewiseRealizedBehaviorRegretProcess
    mdp initialState initialTable defaultState baseVisitFloor hrewardBound n).coeFn_toLp

/-- The named `Lp Real 1` scheduled process converges to zero in the `Lp` topology. -/
theorem decayingExplorationEpisodewiseRealizedBehaviorRegretLp_tendsto_zero
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (baseVisitFloor : Real)
    (hbatchBorel : forall n, StandardBorelSpace
      (EpisodeBatch mdp
        (AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes
          mdp baseVisitFloor n)))
    (htrajectoryBorel : forall n, StandardBorelSpace
      (EpisodeBatchTrajectory mdp
        (AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes
          mdp baseVisitFloor n)))
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State)
    (support : ExploratoryPathSupport mdp initialState)
    (hbaseFloor : ExploratoryPathUniformVisitFloor support 1 baseVisitFloor)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (hhorizon : 0 < mdp.horizon) (hbaseVisitFloor : 0 < baseVisitFloor) :
    Tendsto
      (decayingExplorationEpisodewiseRealizedBehaviorRegretLp mdp initialState
        initialTable defaultState baseVisitFloor hrewardBound)
      atTop (nhds 0) := by
  let mu := decayingExplorationEpisodewiseCommonMeasure mdp initialState
    initialTable defaultState baseVisitFloor
  let process := fun n =>
    decayingExplorationEpisodewiseRealizedBehaviorRegretProcess mdp
      initialState initialTable defaultState baseVisitFloor n
  have hmem : forall n, MemLp (process n) 1 mu := fun n =>
    memLp_one_decayingExplorationEpisodewiseRealizedBehaviorRegretProcess
      mdp initialState initialTable defaultState baseVisitFloor hrewardBound n
  have hzero : MemLp (fun _ : DecayingExplorationEpisodewiseWindowSpace mdp
      baseVisitFloor => (0 : Real)) 1 mu := MemLp.zero'
  have hnorm :=
    eLpNorm_one_decayingExplorationEpisodewiseRealizedBehaviorRegretProcess_sub_zero_tendsto_zero
      mdp initialState baseVisitFloor hbatchBorel htrajectoryBorel initialTable
      defaultState support hbaseFloor hrewardBound hhorizon hbaseVisitFloor
  have hLp :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' process hmem (fun _ => (0 : Real))
      hzero).2 (by simpa [process, mu] using hnorm)
  simpa [decayingExplorationEpisodewiseRealizedBehaviorRegretLp, process, mu]
    using hLp

/--
Terminal `L1` theorem: coordinate membership, exact norms, canonical norm
convergence, convergence in the `Lp` topology, and the induced convergence in
measure all hold on the same common probability space.
-/
theorem exploratorySource_decayingExplorationEpisodewiseCommonMeasure_memLp_eLpNorm_L1_tendsto_zero
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (baseVisitFloor : Real)
    (hbatchBorel : forall n, StandardBorelSpace
      (EpisodeBatch mdp
        (AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes
          mdp baseVisitFloor n)))
    (htrajectoryBorel : forall n, StandardBorelSpace
      (EpisodeBatchTrajectory mdp
        (AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes
          mdp baseVisitFloor n)))
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State)
    (support : ExploratoryPathSupport mdp initialState)
    (hbaseFloor : ExploratoryPathUniformVisitFloor support 1 baseVisitFloor)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (hhorizon : 0 < mdp.horizon) (hbaseVisitFloor : 0 < baseVisitFloor) :
    (forall n, MemLp
      (decayingExplorationEpisodewiseRealizedBehaviorRegretProcess mdp
        initialState initialTable defaultState baseVisitFloor n)
      1
      (decayingExplorationEpisodewiseCommonMeasure mdp initialState
        initialTable defaultState baseVisitFloor)) /\
    (forall n, eLpNorm
        (decayingExplorationEpisodewiseRealizedBehaviorRegretProcess mdp
          initialState initialTable defaultState baseVisitFloor n)
        1
        (decayingExplorationEpisodewiseCommonMeasure mdp initialState
          initialTable defaultState baseVisitFloor) =
      ENNReal.ofReal
        (decayingExplorationEpisodewiseExpectedAbsoluteRealizedBehaviorRegret
          mdp initialState initialTable defaultState baseVisitFloor n)) /\
    Tendsto
      (fun n => eLpNorm
        (decayingExplorationEpisodewiseRealizedBehaviorRegretProcess mdp
            initialState initialTable defaultState baseVisitFloor n -
          (fun _ => 0))
        1
        (decayingExplorationEpisodewiseCommonMeasure mdp initialState
          initialTable defaultState baseVisitFloor))
      atTop (nhds 0) /\
    Tendsto
      (decayingExplorationEpisodewiseRealizedBehaviorRegretLp mdp initialState
        initialTable defaultState baseVisitFloor hrewardBound)
      atTop (nhds 0) /\
    TendstoInMeasure
      (decayingExplorationEpisodewiseCommonMeasure mdp initialState
        initialTable defaultState baseVisitFloor)
      (decayingExplorationEpisodewiseRealizedBehaviorRegretProcess mdp
        initialState initialTable defaultState baseVisitFloor)
      atTop (fun _ => 0) := by
  have hmem := fun n =>
    memLp_one_decayingExplorationEpisodewiseRealizedBehaviorRegretProcess
      mdp initialState initialTable defaultState baseVisitFloor hrewardBound n
  have hnorm :=
    eLpNorm_one_decayingExplorationEpisodewiseRealizedBehaviorRegretProcess_sub_zero_tendsto_zero
      mdp initialState baseVisitFloor hbatchBorel htrajectoryBorel initialTable
      defaultState support hbaseFloor hrewardBound hhorizon hbaseVisitFloor
  refine ⟨hmem, fun n =>
    eLpNorm_one_decayingExplorationEpisodewiseRealizedBehaviorRegretProcess_eq
      mdp initialState initialTable defaultState baseVisitFloor hrewardBound n,
    hnorm,
    decayingExplorationEpisodewiseRealizedBehaviorRegretLp_tendsto_zero
      mdp initialState baseVisitFloor hbatchBorel htrajectoryBorel initialTable
      defaultState support hbaseFloor hrewardBound hhorizon hbaseVisitFloor,
    ?_⟩
  exact tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero
    (fun n => (hmem n).aestronglyMeasurable)
    (by fun_prop) hnorm

end AdaptiveCumulativeEmpiricalOptimisticSource

end BanditRLProof.FiniteHorizonRL
