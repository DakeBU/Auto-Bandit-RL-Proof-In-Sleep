import BanditRLProof.Algorithms.StochasticGradientBanditTwoArmTheoremOne
import BanditRLProof.IntegrabilitySums
import BanditRLProof.LeafLemmas
import BanditRLProof.PullCountDecomposition

/-!
# Two-arm SGB Theorem 2: Appendix-C Step-1 starvation consumer

This module isolates the deterministic consumer in Step 1 of Appendix C of
Baudry--Johnson--Vary--Pike-Burke--Rebeschini (NeurIPS 2025).  On the actual
generated SGB action/reward trace, once exactly `n` optimal-arm pulls have
occurred, a path with no later optimal-arm pull has exactly
`Delta * (T - n)` sampled pseudo-regret.

The source also lower-bounds the conditional probability of that no-return
path by `1 / 2` when the post-pull optimal-arm probability is at most
`1 / (2*T)`.  That statement needs a finite-future conditional-law/tower
bridge for the generated adaptive trajectory.  The existing API exposes the
one-step conditional action law but not yet the required stopped-prefix
future cylinder law.  No probability lower bound, phase producer, or
Theorem-2 endpoint is claimed in this file.
-/

namespace BanditRLProof
namespace StochasticGradientBandit

open MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory
noncomputable section
universe v

/-- The action coordinate of the canonical SGB trajectory. -/
def twoArmGeneratedAction
    {Env : Type v}
    (sample : Env × ((k : Nat) → Fin 2 × Real)) : ActionTrace (Fin 2) :=
  fun t => (sample.2 t).1

/-- Number of optimal-arm (`0`) pulls in the first `horizon` generated rounds. -/
def twoArmOptimalPullCount
    {Env : Type v} (horizon : Nat)
    (sample : Env × ((k : Nat) → Fin 2 × Real)) : Nat :=
  pullCount (twoArmGeneratedAction sample) 0 horizon

/-- The source Step-1 threshold `1 / (2*T)`. -/
def twoArmStepOneThreshold (horizon : Nat) : Real :=
  1 / (2 * (horizon : Real))

/--
At a chronological prefix ending at `prefix`, the source Step-1 trigger says
that the next optimal-arm probability is at most `1/(2*T)` and that exactly
`n` optimal-arm pulls have occurred through that prefix.

The distinction between chronological `prefix` and pull index `n` is
intentional and source-critical.
-/
def twoArmStepOneTriggerEvent
    {Env : Type v} [MeasurableSpace Env]
    (eta : Real) (cutoff n horizon : Nat) :
    Set (Env × ((k : Nat) → Fin 2 × Real)) :=
  {sample |
    twoArmSuccessProbability eta cutoff sample ≤
        twoArmStepOneThreshold horizon ∧
      twoArmOptimalPullCount (cutoff + 1) sample = n}

/--
The measurable part of the Appendix-C Step-1 starvation event: a trigger
prefix occurs and the total number of optimal-arm pulls by `horizon` remains
exactly `n`.  Equality of the two pull counts is the finite-trace statement
that there is no later optimal-arm selection.
-/
def twoArmStepOneStarvationEvent
    {Env : Type v} [MeasurableSpace Env]
    (eta : Real) (cutoff n horizon : Nat) :
    Set (Env × ((k : Nat) → Fin 2 × Real)) :=
  {sample |
    sample ∈ twoArmStepOneTriggerEvent (Env := Env) eta cutoff n horizon ∧
      twoArmOptimalPullCount horizon sample = n}

theorem measurable_twoArmGeneratedAction
    {Env : Type v} [MeasurableSpace Env] (t : Nat) :
    Measurable
      (fun sample : Env × ((k : Nat) → Fin 2 × Real) =>
        twoArmGeneratedAction sample t) := by
  exact measurable_fst.comp ((measurable_pi_apply t).comp measurable_snd)

theorem measurable_twoArmOptimalPullCount
    {Env : Type v} [MeasurableSpace Env] (horizon : Nat) :
    Measurable
      (twoArmOptimalPullCount (Env := Env) horizon) := by
  induction horizon with
  | zero =>
      change Measurable
        (fun _sample : Env × ((k : Nat) → Fin 2 × Real) => (0 : Nat))
      exact measurable_const
  | succ t ih =>
      have hselected : Measurable
          (fun sample : Env × ((k : Nat) → Fin 2 × Real) =>
            twoArmGeneratedAction sample t) :=
        measurable_twoArmGeneratedAction t
      have hzero : MeasurableSet
          {sample : Env × ((k : Nat) → Fin 2 × Real) |
            twoArmGeneratedAction sample t = 0} :=
        (measurableSet_singleton (0 : Fin 2)).preimage hselected
      have hincrement : Measurable
          (fun sample : Env × ((k : Nat) → Fin 2 × Real) =>
            if twoArmGeneratedAction sample t = 0 then (1 : Nat) else 0) :=
        Measurable.ite hzero measurable_const measurable_const
      simpa [twoArmOptimalPullCount, pullCount_succ] using ih.add hincrement

theorem measurableSet_twoArmStepOneTriggerEvent
    {Env : Type v} [MeasurableSpace Env]
    (eta : Real) (cutoff n horizon : Nat) :
    MeasurableSet
      (twoArmStepOneTriggerEvent (Env := Env) eta cutoff n horizon) := by
  have hlow : MeasurableSet
      {sample : Env × ((k : Nat) → Fin 2 × Real) |
        twoArmSuccessProbability eta cutoff sample ≤
          twoArmStepOneThreshold horizon} :=
    measurableSet_Iic.preimage
      (measurable_twoArmSuccessProbability (Env := Env) eta cutoff)
  have hcount : MeasurableSet
      {sample : Env × ((k : Nat) → Fin 2 × Real) |
        twoArmOptimalPullCount (cutoff + 1) sample = n} :=
    (measurableSet_singleton n).preimage
      (measurable_twoArmOptimalPullCount (Env := Env) (cutoff + 1))
  exact hlow.inter hcount

theorem measurableSet_twoArmStepOneStarvationEvent
    {Env : Type v} [MeasurableSpace Env]
    (eta : Real) (cutoff n horizon : Nat) :
    MeasurableSet
      (twoArmStepOneStarvationEvent (Env := Env) eta cutoff n horizon) := by
  exact
    (measurableSet_twoArmStepOneTriggerEvent
      (Env := Env) eta cutoff n horizon).inter
      ((measurableSet_singleton n).preimage
        (measurable_twoArmOptimalPullCount (Env := Env) horizon))

private theorem finTwo_eq_zero_or_one (action : Fin 2) :
    action = 0 ∨ action = 1 := by
  fin_cases action <;> simp

theorem twoArmSampledPseudoRegret_nonneg
    {Env : Type v} (Delta : Real) (hDelta : 0 ≤ Delta)
    (horizon : Nat)
    (sample : Env × ((k : Nat) → Fin 2 × Real)) :
    0 ≤ twoArmSampledPseudoRegret Delta horizon sample := by
  unfold twoArmSampledPseudoRegret
  apply Finset.sum_nonneg
  intro t _ht
  by_cases hzero : twoArmGeneratedAction sample t = 0
  · change (sample.2 t).1 = 0 at hzero
    simp [twoArmActionGap, hzero]
  · change (sample.2 t).1 ≠ 0 at hzero
    simpa [twoArmActionGap, hzero] using hDelta

/-- The two-arm sampled pseudo-regret is exactly the gap times arm-`1` pulls. -/
theorem twoArmSampledPseudoRegret_eq_gap_mul_suboptimalPullCount
    {Env : Type v} (Delta : Real) (horizon : Nat)
    (sample : Env × ((k : Nat) → Fin 2 × Real)) :
    twoArmSampledPseudoRegret Delta horizon sample =
      Delta * (pullCount (twoArmGeneratedAction sample) 1 horizon : Real) := by
  induction horizon with
  | zero => simp [twoArmSampledPseudoRegret, pullCount]
  | succ t ih =>
      change
        (Finset.range (t + 1)).sum (fun s =>
          twoArmActionGap Delta (twoArmGeneratedAction sample s)) = _
      rw [Finset.sum_range_succ]
      change twoArmSampledPseudoRegret Delta t sample +
        twoArmActionGap Delta (twoArmGeneratedAction sample t) = _
      rw [ih, pullCount_succ]
      by_cases hzero : twoArmGeneratedAction sample t = 0
      · simp [twoArmActionGap, hzero]
      · have hone : twoArmGeneratedAction sample t = 1 :=
          (finTwo_eq_zero_or_one
            (twoArmGeneratedAction sample t)).resolve_left hzero
        simp [twoArmActionGap, hone]
        ring

theorem twoArmOptimalPullCount_add_suboptimalPullCount_eq_horizon
    {Env : Type v} (horizon : Nat)
    (sample : Env × ((k : Nat) → Fin 2 × Real)) :
    twoArmOptimalPullCount horizon sample +
        pullCount (twoArmGeneratedAction sample) 1 horizon = horizon := by
  simpa [twoArmOptimalPullCount] using
    (finset_sum_pullCount_eq_time
      (action := twoArmGeneratedAction sample) horizon)

/-- Exactly `n` optimal pulls force the exact source starvation charge. -/
theorem twoArmSampledPseudoRegret_eq_gap_mul_horizon_sub_of_optimalPullCount_eq
    {Env : Type v} (Delta : Real) (n horizon : Nat)
    (sample : Env × ((k : Nat) → Fin 2 × Real))
    (hcount : twoArmOptimalPullCount horizon sample = n) :
    twoArmSampledPseudoRegret Delta horizon sample =
      Delta * ((horizon - n : Nat) : Real) := by
  rw [twoArmSampledPseudoRegret_eq_gap_mul_suboptimalPullCount]
  have hpartition :=
    twoArmOptimalPullCount_add_suboptimalPullCount_eq_horizon horizon sample
  have hsuboptimal :
      pullCount (twoArmGeneratedAction sample) 1 horizon = horizon - n := by
    omega
  rw [hsuboptimal]

/--
The explicit chronological no-return premise constructs membership in the
measurable starvation event.  This is the pathwise half of Appendix-C Step 1;
it does not assign a probability to the event.
-/
theorem mem_twoArmStepOneStarvationEvent_of_lowProbability_noFurtherOptimalPull
    {Env : Type v} [MeasurableSpace Env]
    (eta : Real) (cutoff n horizon : Nat)
    (sample : Env × ((k : Nat) → Fin 2 × Real))
    (hcutoff : cutoff + 1 ≤ horizon)
    (hlow : twoArmSuccessProbability eta cutoff sample ≤
      twoArmStepOneThreshold horizon)
    (hcount : twoArmOptimalPullCount (cutoff + 1) sample = n)
    (hnoFurther : ∀ t, cutoff + 1 ≤ t → t < horizon →
      twoArmGeneratedAction sample t ≠ 0) :
    sample ∈
      twoArmStepOneStarvationEvent (Env := Env) eta cutoff n horizon := by
  have hdecompose :
      cutoff + 1 + (horizon - (cutoff + 1)) = horizon :=
    Nat.add_sub_of_le hcutoff
  have hfinal : twoArmOptimalPullCount horizon sample =
      twoArmOptimalPullCount (cutoff + 1) sample := by
    rw [← hdecompose]
    exact pullCount_add_eq_of_forall_ne_between
      (twoArmGeneratedAction sample) 0 (cutoff + 1)
      (horizon - (cutoff + 1))
      (fun t ht hlt => hnoFurther t ht (by simpa [hdecompose] using hlt))
  exact ⟨⟨hlow, hcount⟩, hfinal.trans hcount⟩

/-- Every path in the measurable starvation event has the exact Step-1 charge. -/
theorem twoArmStepOneStarvationEvent_sampledPseudoRegret_eq
    {Env : Type v} [MeasurableSpace Env]
    (eta Delta : Real) (cutoff n horizon : Nat)
    (sample : Env × ((k : Nat) → Fin 2 × Real))
    (hstarve : sample ∈
      twoArmStepOneStarvationEvent (Env := Env) eta cutoff n horizon) :
    twoArmSampledPseudoRegret Delta horizon sample =
      Delta * ((horizon - n : Nat) : Real) := by
  exact
    twoArmSampledPseudoRegret_eq_gap_mul_horizon_sub_of_optimalPullCount_eq
      Delta n horizon sample hstarve.2

/-- Integrability of finite-horizon sampled regret under any finite trace law. -/
theorem integrable_twoArmSampledPseudoRegret_of_finiteMeasure
    {Env : Type v} [MeasurableSpace Env]
    (mu : Measure (Env × ((k : Nat) → Fin 2 × Real)))
    [IsFiniteMeasure mu] (Delta : Real) (horizon : Nat) :
    Integrable (twoArmSampledPseudoRegret (Env := Env) Delta horizon) mu := by
  unfold twoArmSampledPseudoRegret
  apply IntegrabilitySums.integrable_finset_sum mu (Finset.range horizon)
  intro t _ht
  have hmeas : Measurable
      (fun sample : Env × ((k : Nat) → Fin 2 × Real) =>
        twoArmActionGap Delta (sample.2 t).1) :=
    (measurable_twoArmActionGap Delta).comp
      (measurable_fst.comp ((measurable_pi_apply t).comp measurable_snd))
  apply Integrable.of_bound hmeas.aestronglyMeasurable |Delta|
  filter_upwards [] with sample
  by_cases hzero : (sample.2 t).1 = 0 <;>
    simp [twoArmActionGap, hzero]

/--
Expectation-level deterministic Step-1 consumer.  It lower-bounds expected
sampled regret by the exact starvation charge times the probability of the
actual generated starvation event.  The missing source producer is precisely
the separate lower bound on this event probability from the trigger event.
-/
theorem twoArmStepOneStarvationEvent_charge_mul_probability_le_integral
    {Env : Type v} [MeasurableSpace Env]
    (mu : Measure (Env × ((k : Nat) → Fin 2 × Real)))
    [IsFiniteMeasure mu]
    (eta Delta : Real) (hDelta : 0 ≤ Delta)
    (cutoff n horizon : Nat) :
    Delta * ((horizon - n : Nat) : Real) *
        mu.real
          (twoArmStepOneStarvationEvent
            (Env := Env) eta cutoff n horizon) ≤
      integral mu
        (twoArmSampledPseudoRegret (Env := Env) Delta horizon) := by
  let event :=
    twoArmStepOneStarvationEvent (Env := Env) eta cutoff n horizon
  let charge : Real := Delta * ((horizon - n : Nat) : Real)
  have hevent : MeasurableSet event := by
    exact measurableSet_twoArmStepOneStarvationEvent
      (Env := Env) eta cutoff n horizon
  have hregret : Integrable
      (twoArmSampledPseudoRegret (Env := Env) Delta horizon) mu :=
    integrable_twoArmSampledPseudoRegret_of_finiteMeasure mu Delta horizon
  have hindicator : Integrable
      (event.indicator (fun _sample => charge)) mu :=
    (integrable_const charge).indicator hevent
  have hpointwise : ∀ sample : Env × ((k : Nat) → Fin 2 × Real),
      event.indicator (fun _sample => charge) sample ≤
        twoArmSampledPseudoRegret Delta horizon sample := by
    intro sample
    by_cases hsample : sample ∈ event
    · rw [Set.indicator_of_mem hsample]
      exact le_of_eq
        (twoArmStepOneStarvationEvent_sampledPseudoRegret_eq
          eta Delta cutoff n horizon sample hsample).symm
    · simp only [Set.indicator, if_neg hsample]
      exact twoArmSampledPseudoRegret_nonneg Delta hDelta horizon sample
  have hintegral :
      integral mu (event.indicator (fun _sample => charge)) ≤
        integral mu
          (twoArmSampledPseudoRegret (Env := Env) Delta horizon) :=
    integral_mono hindicator hregret hpointwise
  have hindicatorIntegral :
      integral mu (event.indicator (fun _sample => charge)) =
        charge * mu.real event := by
    rw [integral_indicator hevent]
    rw [integral_const]
    simp [Measure.real, mul_comm]
  rw [hindicatorIntegral] at hintegral
  simpa [event, charge, mul_assoc] using hintegral

/--
The same deterministic Step-1 consumer specialized to the canonical generated
fixed-IID trajectory with a Dirac environment prior.  This wrapper covers the
paper's Rademacher/Dirac arm-law instance once that explicit arm-law adapter is
supplied; it still does not lower-bound the starvation-event probability.
-/
theorem twoArmFixedIIDStepOneStarvationEvent_charge_mul_probability_le_integral
    (armLaw : Fin 2 -> Measure Real)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (eta Delta : Real) (hDelta : 0 <= Delta)
    (cutoff n horizon : Nat) :
    Delta * ((horizon - n : Nat) : Real) *
        (twoArmTrajectoryMeasure (Measure.dirac ()) eta
          (twoArmFixedIIDEnvironment armLaw hprob)).real
          (twoArmStepOneStarvationEvent
            (Env := Unit) eta cutoff n horizon) <=
      integral
        (twoArmTrajectoryMeasure (Measure.dirac ()) eta
          (twoArmFixedIIDEnvironment armLaw hprob))
        (twoArmSampledPseudoRegret (Env := Unit) Delta horizon) := by
  exact
    twoArmStepOneStarvationEvent_charge_mul_probability_le_integral
      (twoArmTrajectoryMeasure (Measure.dirac ()) eta
        (twoArmFixedIIDEnvironment armLaw hprob))
      eta Delta hDelta cutoff n horizon

end
end StochasticGradientBandit
end BanditRLProof
