import BanditRLProof.TsallisOracleRestartGeneratedTrajectory
import BanditRLProof.TsallisOracleRestartDynamicRegret

/-!
# Predictable regret for generated oracle-restart trajectories

This module puts the generated restart probability into the pointwise regret
summand and aligns the deterministic epoch assembly with `schedule.start`.
Epoch-local regret certificates remain explicit downstream inputs.
-/

open scoped ENNReal NNReal Topology ProbabilityTheory
open MeasureTheory ProbabilityTheory Set Filter Finset

namespace BanditRLProof
namespace Tsallis

universe u v

/-- Predictable environment regret of the generated restart probabilities
against a fixed comparator distribution through the inclusive horizon. -/
noncomputable def sampledOracleRestartHalfTsallisPredictableEnvironmentRegret
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action] [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (schedule : OracleRestartSchedule)
    (loss : Exp3.PredictableLossVector Env Action)
    (q : Action -> Real) (horizon : Nat)
    (sample : Env × ((k : Nat) -> Action × Real)) : Real :=
  (Finset.range (horizon + 1)).sum (fun t =>
    FTRL.linearLoss arms
        (sampledOracleRestartHalfTsallisProbabilityAtTime
          arms harms eta schedule t sample)
        (Exp3.predictableLossAt loss t sample) -
      FTRL.linearLoss arms q (Exp3.predictableLossAt loss t sample))

/-- Predictable environment regret of the generated restart probabilities
against a deterministic comparator arm that may change with the round. -/
noncomputable def sampledOracleRestartHalfTsallisPredictableMovingComparatorEnvironmentRegret
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action] [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (schedule : OracleRestartSchedule)
    (loss : Exp3.PredictableLossVector Env Action)
    (comparator : Nat -> Action) (horizon : Nat)
    (sample : Env × ((k : Nat) -> Action × Real)) : Real :=
  (Finset.range (horizon + 1)).sum (fun t =>
    FTRL.linearLoss arms
        (sampledOracleRestartHalfTsallisProbabilityAtTime
          arms harms eta schedule t sample)
        (Exp3.predictableLossAt loss t sample) -
      Exp3.predictableLossAt loss t sample (comparator t))

@[simp]
theorem sampledOracleRestartHalfTsallisPredictableEnvironmentRegret_neverRestart
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action] [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (loss : Exp3.PredictableLossVector Env Action)
    (q : Action -> Real) (horizon : Nat)
    (sample : Env × ((k : Nat) -> Action × Real)) :
    sampledOracleRestartHalfTsallisPredictableEnvironmentRegret
        arms harms eta oracleNeverRestartSchedule loss q horizon sample =
      sampledScheduledHalfTsallisPredictableEnvironmentRegret
        arms harms eta loss q horizon sample := by
  simp [sampledOracleRestartHalfTsallisPredictableEnvironmentRegret,
    sampledScheduledHalfTsallisPredictableEnvironmentRegret]

@[simp]
theorem sampledOracleRestartHalfTsallisPredictableMovingComparatorEnvironmentRegret_neverRestart
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action] [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (loss : Exp3.PredictableLossVector Env Action)
    (comparator : Nat -> Action) (horizon : Nat)
    (sample : Env × ((k : Nat) -> Action × Real)) :
    sampledOracleRestartHalfTsallisPredictableMovingComparatorEnvironmentRegret
        arms harms eta oracleNeverRestartSchedule loss comparator horizon
        sample =
      sampledScheduledHalfTsallisPredictableMovingComparatorEnvironmentRegret
        arms harms eta loss comparator horizon sample := by
  simp [
    sampledOracleRestartHalfTsallisPredictableMovingComparatorEnvironmentRegret,
    sampledScheduledHalfTsallisPredictableMovingComparatorEnvironmentRegret]

/-- Restarted moving-comparator regret is fixed point-mass regret plus the
cumulative advantage of the moving comparator over the fixed arm. -/
theorem sampledOracleRestartHalfTsallisPredictableMovingComparatorEnvironmentRegret_eq_fixed_add
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action] [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (schedule : OracleRestartSchedule)
    (loss : Exp3.PredictableLossVector Env Action)
    {best : Action} (hbest : best ∈ arms)
    (comparator : Nat -> Action) (horizon : Nat)
    (sample : Env × ((k : Nat) -> Action × Real)) :
    sampledOracleRestartHalfTsallisPredictableMovingComparatorEnvironmentRegret
        arms harms eta schedule loss comparator horizon sample =
      sampledOracleRestartHalfTsallisPredictableEnvironmentRegret
          arms harms eta schedule loss (pointMass best) horizon sample +
        (Finset.range (horizon + 1)).sum (fun t =>
          Exp3.predictableLossAt loss t sample best -
            Exp3.predictableLossAt loss t sample (comparator t)) := by
  unfold
    sampledOracleRestartHalfTsallisPredictableMovingComparatorEnvironmentRegret
    sampledOracleRestartHalfTsallisPredictableEnvironmentRegret
  simp_rw [linearLoss_pointMass arms hbest]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _ht
  ring

/-- Epoch ids actually visited by the restart schedule through the inclusive
horizon. The epoch assignment is exactly `schedule.start`. -/
def oracleRestartScheduleEpochs
    (schedule : OracleRestartSchedule) (horizon : Nat) : Finset Nat :=
  (Finset.range (horizon + 1)).image schedule.start

theorem oracleRestartSchedule_start_mem_epochs
    (schedule : OracleRestartSchedule) (horizon t : Nat)
    (ht : t ∈ Finset.range (horizon + 1)) :
    schedule.start t ∈ oracleRestartScheduleEpochs schedule horizon := by
  exact Finset.mem_image.mpr ⟨t, ht, rfl⟩

/-- Restart-specific predictable regret contributed by one schedule epoch. -/
noncomputable def sampledOracleRestartHalfTsallisPredictableScheduleEpochRegret
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action] [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (schedule : OracleRestartSchedule)
    (loss : Exp3.PredictableLossVector Env Action)
    (epochComparator : Nat -> Action) (horizon epoch : Nat)
    (sample : Env × ((k : Nat) -> Action × Real)) : Real :=
  (oracleRestartEpochRounds schedule.start horizon epoch).sum (fun t =>
    FTRL.linearLoss arms
        (sampledOracleRestartHalfTsallisProbabilityAtTime
          arms harms eta schedule t sample)
        (Exp3.predictableLossAt loss t sample) -
      Exp3.predictableLossAt loss t sample
        (epochComparator (schedule.start t)))

/-- Schedule-aligned moving regret is exactly the sum of its epoch-fiber
regrets, with no independent `epochOf` compatibility premise. -/
theorem sampledOracleRestartHalfTsallisPredictableMovingComparatorEnvironmentRegret_eq_sum_scheduleEpochRegret
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action] [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (schedule : OracleRestartSchedule)
    (loss : Exp3.PredictableLossVector Env Action)
    (epochComparator : Nat -> Action) (horizon : Nat)
    (sample : Env × ((k : Nat) -> Action × Real)) :
    sampledOracleRestartHalfTsallisPredictableMovingComparatorEnvironmentRegret
        arms harms eta schedule loss
        (fun t => epochComparator (schedule.start t)) horizon sample =
      (oracleRestartScheduleEpochs schedule horizon).sum (fun epoch =>
        sampledOracleRestartHalfTsallisPredictableScheduleEpochRegret
          arms harms eta schedule loss epochComparator horizon epoch sample) := by
  unfold
    sampledOracleRestartHalfTsallisPredictableMovingComparatorEnvironmentRegret
    sampledOracleRestartHalfTsallisPredictableScheduleEpochRegret
    oracleRestartEpochRounds
  symm
  exact Finset.sum_fiberwise_of_maps_to
    (fun t ht => oracleRestartSchedule_start_mem_epochs schedule horizon t ht)
    (fun t =>
      FTRL.linearLoss arms
          (sampledOracleRestartHalfTsallisProbabilityAtTime
            arms harms eta schedule t sample)
          (Exp3.predictableLossAt loss t sample) -
        Exp3.predictableLossAt loss t sample
          (epochComparator (schedule.start t)))

/-- Schedule-aligned epoch certificates assemble into a global square-root
bound for the generated restart regret surface. -/
theorem sampledOracleRestartHalfTsallisPredictableMovingComparatorEnvironmentRegret_le_scheduleSqrt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action] [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (schedule : OracleRestartSchedule)
    (loss : Exp3.PredictableLossVector Env Action)
    (epochComparator : Nat -> Action) (horizon : Nat)
    (coefficient : Real) (hcoefficient : 0 <= coefficient)
    (sample : Env × ((k : Nat) -> Action × Real))
    (hEpochRegret :
      ∀ epoch ∈ oracleRestartScheduleEpochs schedule horizon,
        sampledOracleRestartHalfTsallisPredictableScheduleEpochRegret
            arms harms eta schedule loss epochComparator horizon epoch sample <=
          coefficient *
            Real.sqrt
              ((oracleRestartEpochRounds
                schedule.start horizon epoch).card : Real)) :
    sampledOracleRestartHalfTsallisPredictableMovingComparatorEnvironmentRegret
        arms harms eta schedule loss
        (fun t => epochComparator (schedule.start t)) horizon sample <=
      coefficient *
          Real.sqrt ((oracleRestartScheduleEpochs schedule horizon).card : Real) *
        Real.sqrt (((horizon + 1 : Nat) : Real)) := by
  rw [
    sampledOracleRestartHalfTsallisPredictableMovingComparatorEnvironmentRegret_eq_sum_scheduleEpochRegret
      arms harms eta schedule loss epochComparator horizon sample]
  calc
    _ <= (oracleRestartScheduleEpochs schedule horizon).sum (fun epoch =>
        coefficient *
          Real.sqrt
            ((oracleRestartEpochRounds
              schedule.start horizon epoch).card : Real)) := by
      exact Finset.sum_le_sum (fun epoch hepoch =>
        hEpochRegret epoch hepoch)
    _ = coefficient *
        (oracleRestartScheduleEpochs schedule horizon).sum (fun epoch =>
          Real.sqrt
            ((oracleRestartEpochRounds
              schedule.start horizon epoch).card : Real)) := by
      rw [Finset.mul_sum]
    _ <= coefficient *
        (Real.sqrt
            ((oracleRestartScheduleEpochs schedule horizon).card : Real) *
          Real.sqrt (((horizon + 1 : Nat) : Real))) := by
      exact mul_le_mul_of_nonneg_left
        (sum_sqrt_oracleRestartEpochRounds_card_le
          (oracleRestartScheduleEpochs schedule horizon)
          schedule.start horizon
          (fun t ht =>
            oracleRestartSchedule_start_mem_epochs schedule horizon t ht))
        hcoefficient
    _ = coefficient *
          Real.sqrt
            ((oracleRestartScheduleEpochs schedule horizon).card : Real) *
        Real.sqrt (((horizon + 1 : Nat) : Real)) := by ring

/-- Switch-count-facing schedule assembly under an explicit cardinality
contract on the epochs actually visited by `schedule.start`. -/
theorem sampledOracleRestartHalfTsallisPredictableMovingComparatorEnvironmentRegret_le_scheduleSwitchCountSqrt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action] [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (schedule : OracleRestartSchedule)
    (loss : Exp3.PredictableLossVector Env Action)
    (epochComparator : Nat -> Action) (horizon switches : Nat)
    (hEpochCard :
      (oracleRestartScheduleEpochs schedule horizon).card <= switches + 1)
    (coefficient : Real) (hcoefficient : 0 <= coefficient)
    (sample : Env × ((k : Nat) -> Action × Real))
    (hEpochRegret :
      ∀ epoch ∈ oracleRestartScheduleEpochs schedule horizon,
        sampledOracleRestartHalfTsallisPredictableScheduleEpochRegret
            arms harms eta schedule loss epochComparator horizon epoch sample <=
          coefficient *
            Real.sqrt
              ((oracleRestartEpochRounds
                schedule.start horizon epoch).card : Real)) :
    sampledOracleRestartHalfTsallisPredictableMovingComparatorEnvironmentRegret
        arms harms eta schedule loss
        (fun t => epochComparator (schedule.start t)) horizon sample <=
      coefficient * Real.sqrt (((switches + 1 : Nat) : Real)) *
        Real.sqrt (((horizon + 1 : Nat) : Real)) := by
  have hrestart :=
    sampledOracleRestartHalfTsallisPredictableMovingComparatorEnvironmentRegret_le_scheduleSqrt
      arms harms eta schedule loss epochComparator horizon
      coefficient hcoefficient sample hEpochRegret
  have hcardReal :
      ((oracleRestartScheduleEpochs schedule horizon).card : Real) <=
        (((switches + 1 : Nat) : Real)) := by
    exact_mod_cast hEpochCard
  have hsqrt :
      Real.sqrt
          ((oracleRestartScheduleEpochs schedule horizon).card : Real) <=
        Real.sqrt (((switches + 1 : Nat) : Real)) :=
    Real.sqrt_le_sqrt hcardReal
  calc
    _ <= coefficient *
          Real.sqrt
            ((oracleRestartScheduleEpochs schedule horizon).card : Real) *
        Real.sqrt (((horizon + 1 : Nat) : Real)) := hrestart
    _ <= coefficient * Real.sqrt (((switches + 1 : Nat) : Real)) *
        Real.sqrt (((horizon + 1 : Nat) : Real)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsqrt hcoefficient)
        (Real.sqrt_nonneg _)

end Tsallis
end BanditRLProof
