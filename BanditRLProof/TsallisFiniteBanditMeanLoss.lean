import BanditRLProof.FiniteBanditModelInvariants
import BanditRLProof.TsallisSqrtScheduleFixedGap

/-!
# Finite-bandit mean losses for scheduled half-Tsallis FTRL

This module turns a bounded finite-bandit mean-reward model into the
history-independent predictable loss family `1 - mean`.  Its loss differences
are exactly the model gaps, so the compiled square-root-schedule fixed-gap
theorem applies without a caller-supplied predictable gap law.

The generated feedback remains the deterministic mean-loss environment of
`Exp3.PredictableLossVector`; this module does not identify it with a stochastic
reward-kernel trajectory.
-/

namespace BanditRLProof

open MeasureTheory ProbabilityTheory

universe u

namespace Exp3

/-- The stationary predictable loss family obtained from bounded arm means. -/
noncomputable def finiteBanditMeanLoss
    {K : Nat} {Env : Type u} [MeasurableSpace Env]
    (model : FiniteBanditModel K)
    (hmean : forall arm,
      ((model.mean arm : Rat) : Real) ∈ Set.Icc (0 : Real) 1) :
    PredictableLossVector Env (Fin K) where
  initial := fun _ arm => 1 - ((model.mean arm : Rat) : Real)
  successor := fun _ _ _ arm => 1 - ((model.mean arm : Rat) : Real)
  measurable_initial :=
    measurable_const.sub
      ((measurable_of_countable (fun arm : Fin K =>
        ((model.mean arm : Rat) : Real))).comp measurable_snd)
  measurable_successor := fun _ =>
    measurable_const.sub
      ((measurable_of_countable (fun arm : Fin K =>
        ((model.mean arm : Rat) : Real))).comp
          (measurable_snd.comp measurable_snd))
  initial_nonneg := fun _ arm => by
    exact sub_nonneg.mpr (hmean arm).2
  initial_le_one := fun _ arm => by
    linarith [(hmean arm).1]
  successor_nonneg := fun _ _ _ arm => by
    exact sub_nonneg.mpr (hmean arm).2
  successor_le_one := fun _ _ _ arm => by
    linarith [(hmean arm).1]

@[simp]
theorem finiteBanditMeanLoss_initial
    {K : Nat} {Env : Type u} [MeasurableSpace Env]
    (model : FiniteBanditModel K)
    (hmean : forall arm,
      ((model.mean arm : Rat) : Real) ∈ Set.Icc (0 : Real) 1)
    (env : Env) (arm : Fin K) :
    (finiteBanditMeanLoss (Env := Env) model hmean).initial env arm =
      1 - ((model.mean arm : Rat) : Real) := by
  rfl

@[simp]
theorem finiteBanditMeanLoss_successor
    {K : Nat} {Env : Type u} [MeasurableSpace Env]
    (model : FiniteBanditModel K)
    (hmean : forall arm,
      ((model.mean arm : Rat) : Real) ∈ Set.Icc (0 : Real) 1)
    (n : Nat) (env : Env)
    (history : History.FinitePairHistory (Fin K) Real n) (arm : Fin K) :
    (finiteBanditMeanLoss (Env := Env) model hmean).successor
        n env history arm =
      1 - ((model.mean arm : Rat) : Real) := by
  rfl

@[simp]
theorem predictableLossAt_finiteBanditMeanLoss
    {K : Nat} {Env : Type u} [MeasurableSpace Env]
    (model : FiniteBanditModel K)
    (hmean : forall arm,
      ((model.mean arm : Rat) : Real) ∈ Set.Icc (0 : Real) 1)
    (t : Nat) (sample : Env × ((k : Nat) -> Fin K × Real))
    (arm : Fin K) :
    predictableLossAt (finiteBanditMeanLoss (Env := Env) model hmean)
        t sample arm =
      1 - ((model.mean arm : Rat) : Real) := by
  cases t <;> rfl

/-- Mean-loss differences against the selected best arm are model gaps. -/
theorem predictableLossAt_finiteBanditMeanLoss_sub_bestArm_eq_gap
    {K : Nat} {Env : Type u} [MeasurableSpace Env]
    (model : FiniteBanditModel K)
    (hmean : forall arm,
      ((model.mean arm : Rat) : Real) ∈ Set.Icc (0 : Real) 1)
    (t : Nat) (sample : Env × ((k : Nat) -> Fin K × Real))
    (arm : Fin K) :
    predictableLossAt (finiteBanditMeanLoss (Env := Env) model hmean)
          t sample arm -
        predictableLossAt (finiteBanditMeanLoss (Env := Env) model hmean)
          t sample model.bestArm =
      ((model.gap arm : Rat) : Real) := by
  by_cases h : arm = model.bestArm
  · simp [h]
  · simp [FiniteBanditModel.gap, FiniteBanditModel.bestMean, h]

end Exp3

namespace Tsallis

/--
The square-root scheduled half-Tsallis algorithm has logarithmic fixed-gap
regret on the deterministic mean-loss environment of a bounded finite-bandit
model with strictly positive non-best gaps.
-/
theorem integral_sampledScheduledHalfTsallisFiniteBanditMeanLossRegret_le_log_fixedGap
    {K : Nat} {Env : Type u}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (model : FiniteBanditModel K)
    (hmean : forall arm,
      ((model.mean arm : Rat) : Real) ∈ Set.Icc (0 : Real) 1)
    (hgapPos : forall arm, arm ≠ model.bestArm ->
      0 < ((model.gap arm : Rat) : Real))
    (horizon : Nat) (corruption : Real) (hcorruption : 0 <= corruption) :
    letI : Nonempty (Fin K) := ⟨model.bestArm⟩
    let loss := Exp3.finiteBanditMeanLoss (Env := Env) model hmean
    let selector :=
      canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
        (Finset.univ : Finset (Fin K)) Finset.univ_nonempty
        sampledScheduledHalfTsallisSqrtSchedule loss
    let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
      (Finset.univ : Finset (Fin K)) Finset.univ_nonempty
      sampledScheduledHalfTsallisSqrtSchedule
      selector.finiteHistory loss.environment
    integral mu (sampledScheduledHalfTsallisPredictableEnvironmentRegret
        (Finset.univ : Finset (Fin K)) Finset.univ_nonempty
        sampledScheduledHalfTsallisSqrtSchedule loss
        (pointMass model.bestArm) horizon) <=
      (1 + Real.log (((horizon + 1 : Nat) : Real))) *
        (1 + 25 * ((Finset.univ : Finset (Fin K)).erase model.bestArm).sum
          (fun arm => 1 / ((model.gap arm : Rat) : Real))) +
        corruption := by
  letI : Nonempty (Fin K) := ⟨model.bestArm⟩
  dsimp only
  exact
    integral_sampledScheduledHalfTsallisPredictableEnvironmentRegret_pointMass_le_sqrtSchedule_log_fixedGap
      prior (Finset.univ : Finset (Fin K)) Finset.univ_nonempty
      (Exp3.finiteBanditMeanLoss (Env := Env) model hmean)
      (Finset.mem_univ model.bestArm) horizon
      (fun arm => ((model.gap arm : Rat) : Real))
      (fun arm harm => hgapPos arm (Finset.ne_of_mem_erase harm))
      (fun t sample arm _ =>
        Exp3.predictableLossAt_finiteBanditMeanLoss_sub_bestArm_eq_gap
          model hmean t sample arm)
      corruption hcorruption

end Tsallis
end BanditRLProof
