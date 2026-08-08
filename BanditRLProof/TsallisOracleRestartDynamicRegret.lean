import BanditRLProof.TsallisFiniteArmIndependentDriftingMeanDynamicRegret
import Mathlib.Data.Real.Sqrt

/-!
# Oracle-restart dynamic-regret assembly

This module proves the finite-sum assembly behind a switch-aligned restart
route. It does not construct a restarted selector or trajectory kernel:
epoch-local fixed-comparator regret certificates remain explicit inputs.
-/

open scoped ENNReal NNReal Topology ProbabilityTheory
open MeasureTheory ProbabilityTheory Set Filter Finset

namespace BanditRLProof
namespace Tsallis

universe u v w

/-- Included rounds assigned to one epoch. -/
def oracleRestartEpochRounds
    {Epoch : Type w} [DecidableEq Epoch]
    (epochOf : Nat -> Epoch) (horizon : Nat) (epoch : Epoch) : Finset Nat :=
  (Finset.range (horizon + 1)).filter (fun t => epochOf t = epoch)

/-- Predictable fixed-comparator regret contributed by one epoch fiber. -/
noncomputable def sampledScheduledHalfTsallisPredictableOracleRestartEpochRegret
    {Env : Type u} {Action : Type v} {Epoch : Type w}
    [MeasurableSpace Env] [MeasurableSpace Action] [DecidableEq Action]
    [DecidableEq Epoch]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (loss : Exp3.PredictableLossVector Env Action)
    (epochOf : Nat -> Epoch) (epochComparator : Epoch -> Action)
    (horizon : Nat) (epoch : Epoch)
    (sample : Env × ((k : Nat) -> Action × Real)) : Real :=
  (oracleRestartEpochRounds epochOf horizon epoch).sum (fun t =>
    FTRL.linearLoss arms
        (sampledScheduledHalfTsallisProbabilityAtTime
          arms harms eta t sample)
        (Exp3.predictableLossAt loss t sample) -
      Exp3.predictableLossAt loss t sample
        (epochComparator (epochOf t)))

/-- Moving-comparator regret against an epochwise constant comparator is
exactly the sum of its epoch-fiber fixed-comparator regrets. -/
theorem sampledScheduledHalfTsallisPredictableMovingComparatorEnvironmentRegret_eq_sum_oracleRestartEpochRegret
    {Env : Type u} {Action : Type v} {Epoch : Type w}
    [MeasurableSpace Env] [MeasurableSpace Action] [DecidableEq Action]
    [DecidableEq Epoch]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (loss : Exp3.PredictableLossVector Env Action)
    (epochs : Finset Epoch) (epochOf : Nat -> Epoch)
    (epochComparator : Epoch -> Action) (horizon : Nat)
    (hEpochOf : ∀ t ∈ Finset.range (horizon + 1), epochOf t ∈ epochs)
    (sample : Env × ((k : Nat) -> Action × Real)) :
    sampledScheduledHalfTsallisPredictableMovingComparatorEnvironmentRegret
        arms harms eta loss (fun t => epochComparator (epochOf t))
        horizon sample =
      epochs.sum (fun epoch =>
        sampledScheduledHalfTsallisPredictableOracleRestartEpochRegret
          arms harms eta loss epochOf epochComparator horizon epoch sample) := by
  unfold sampledScheduledHalfTsallisPredictableMovingComparatorEnvironmentRegret
    sampledScheduledHalfTsallisPredictableOracleRestartEpochRegret
    oracleRestartEpochRounds
  symm
  exact Finset.sum_fiberwise_of_maps_to hEpochOf (fun t =>
    FTRL.linearLoss arms
        (sampledScheduledHalfTsallisProbabilityAtTime
          arms harms eta t sample)
        (Exp3.predictableLossAt loss t sample) -
      Exp3.predictableLossAt loss t sample
        (epochComparator (epochOf t)))

/-- Cauchy--Schwarz bound for the square roots of epoch-fiber lengths. -/
theorem sum_sqrt_oracleRestartEpochRounds_card_le
    {Epoch : Type w} [DecidableEq Epoch]
    (epochs : Finset Epoch) (epochOf : Nat -> Epoch) (horizon : Nat)
    (hEpochOf : ∀ t ∈ Finset.range (horizon + 1), epochOf t ∈ epochs) :
    epochs.sum (fun epoch =>
        Real.sqrt
          ((oracleRestartEpochRounds epochOf horizon epoch).card : Real)) <=
      Real.sqrt (epochs.card : Real) *
        Real.sqrt (((horizon + 1 : Nat) : Real)) := by
  have hcardNat :
      (Finset.range (horizon + 1)).card =
        epochs.sum (fun epoch =>
          (oracleRestartEpochRounds epochOf horizon epoch).card) := by
    simpa [oracleRestartEpochRounds] using
      (Finset.card_eq_sum_card_fiberwise
        (s := Finset.range (horizon + 1))
        (t := epochs) (f := epochOf) hEpochOf)
  have hcardReal :
      (((horizon + 1 : Nat) : Real)) =
        epochs.sum (fun epoch =>
          ((oracleRestartEpochRounds epochOf horizon epoch).card : Real)) := by
    have hcast := congrArg (fun n : Nat => (n : Real)) hcardNat
    simpa using hcast
  have hcs :=
    Real.sum_sqrt_mul_sqrt_le epochs
      (f := fun _epoch => (1 : Real))
      (g := fun epoch =>
        ((oracleRestartEpochRounds epochOf horizon epoch).card : Real))
      (fun _epoch => by positivity)
      (fun _epoch => by positivity)
  simpa [hcardReal] using hcs

/-- Oracle-restart assembly: epoch-local square-root fixed-comparator
certificates yield a global square-root moving-comparator bound. -/
theorem sampledScheduledHalfTsallisPredictableMovingComparatorEnvironmentRegret_le_oracleRestartSqrt
    {Env : Type u} {Action : Type v} {Epoch : Type w}
    [MeasurableSpace Env] [MeasurableSpace Action] [DecidableEq Action]
    [DecidableEq Epoch]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (loss : Exp3.PredictableLossVector Env Action)
    (epochs : Finset Epoch) (epochOf : Nat -> Epoch)
    (epochComparator : Epoch -> Action) (horizon : Nat)
    (hEpochOf : ∀ t ∈ Finset.range (horizon + 1), epochOf t ∈ epochs)
    (coefficient : Real) (hcoefficient : 0 <= coefficient)
    (sample : Env × ((k : Nat) -> Action × Real))
    (hEpochRegret :
      ∀ epoch ∈ epochs,
        sampledScheduledHalfTsallisPredictableOracleRestartEpochRegret
            arms harms eta loss epochOf epochComparator horizon epoch sample <=
          coefficient *
            Real.sqrt
              ((oracleRestartEpochRounds epochOf horizon epoch).card :
                Real)) :
    sampledScheduledHalfTsallisPredictableMovingComparatorEnvironmentRegret
        arms harms eta loss (fun t => epochComparator (epochOf t))
        horizon sample <=
      coefficient * Real.sqrt (epochs.card : Real) *
        Real.sqrt (((horizon + 1 : Nat) : Real)) := by
  rw [
    sampledScheduledHalfTsallisPredictableMovingComparatorEnvironmentRegret_eq_sum_oracleRestartEpochRegret
      arms harms eta loss epochs epochOf epochComparator horizon hEpochOf sample]
  calc
    _ <= epochs.sum (fun epoch =>
        coefficient *
          Real.sqrt
            ((oracleRestartEpochRounds epochOf horizon epoch).card :
              Real)) := by
      exact Finset.sum_le_sum (fun epoch hepoch =>
        hEpochRegret epoch hepoch)
    _ = coefficient * epochs.sum (fun epoch =>
        Real.sqrt
          ((oracleRestartEpochRounds epochOf horizon epoch).card :
            Real)) := by
      rw [Finset.mul_sum]
    _ <= coefficient *
        (Real.sqrt (epochs.card : Real) *
          Real.sqrt (((horizon + 1 : Nat) : Real))) := by
      exact mul_le_mul_of_nonneg_left
        (sum_sqrt_oracleRestartEpochRounds_card_le
          epochs epochOf horizon hEpochOf)
        hcoefficient
    _ = coefficient * Real.sqrt (epochs.card : Real) *
        Real.sqrt (((horizon + 1 : Nat) : Real)) := by ring

/-- Switch-count-facing oracle-restart assembly. When the epoch partition has
at most one more epoch than switches, the global moving-comparator bound has
the standard `sqrt((switches + 1) * (horizon + 1))` product form. -/
theorem sampledScheduledHalfTsallisPredictableMovingComparatorEnvironmentRegret_le_oracleRestartSwitchCountSqrt
    {Env : Type u} {Action : Type v} {Epoch : Type w}
    [MeasurableSpace Env] [MeasurableSpace Action] [DecidableEq Action]
    [DecidableEq Epoch]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (loss : Exp3.PredictableLossVector Env Action)
    (epochs : Finset Epoch) (epochOf : Nat -> Epoch)
    (epochComparator : Epoch -> Action) (horizon switches : Nat)
    (hEpochOf : ∀ t ∈ Finset.range (horizon + 1), epochOf t ∈ epochs)
    (hEpochCard : epochs.card <= switches + 1)
    (coefficient : Real) (hcoefficient : 0 <= coefficient)
    (sample : Env × ((k : Nat) -> Action × Real))
    (hEpochRegret :
      ∀ epoch ∈ epochs,
        sampledScheduledHalfTsallisPredictableOracleRestartEpochRegret
            arms harms eta loss epochOf epochComparator horizon epoch sample <=
          coefficient *
            Real.sqrt
              ((oracleRestartEpochRounds epochOf horizon epoch).card :
                Real)) :
    sampledScheduledHalfTsallisPredictableMovingComparatorEnvironmentRegret
        arms harms eta loss (fun t => epochComparator (epochOf t))
        horizon sample <=
      coefficient * Real.sqrt (((switches + 1 : Nat) : Real)) *
        Real.sqrt (((horizon + 1 : Nat) : Real)) := by
  have hrestart :=
    sampledScheduledHalfTsallisPredictableMovingComparatorEnvironmentRegret_le_oracleRestartSqrt
      arms harms eta loss epochs epochOf epochComparator horizon hEpochOf
      coefficient hcoefficient sample hEpochRegret
  have hcardReal :
      (epochs.card : Real) <= (((switches + 1 : Nat) : Real)) := by
    exact_mod_cast hEpochCard
  have hsqrt :
      Real.sqrt (epochs.card : Real) <=
        Real.sqrt (((switches + 1 : Nat) : Real)) :=
    Real.sqrt_le_sqrt hcardReal
  calc
    _ <= coefficient * Real.sqrt (epochs.card : Real) *
        Real.sqrt (((horizon + 1 : Nat) : Real)) := hrestart
    _ <= coefficient * Real.sqrt (((switches + 1 : Nat) : Real)) *
        Real.sqrt (((horizon + 1 : Nat) : Real)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsqrt hcoefficient)
        (Real.sqrt_nonneg _)

end Tsallis
end BanditRLProof
