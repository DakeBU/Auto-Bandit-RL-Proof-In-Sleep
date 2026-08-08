import BanditRLProof.TsallisOracleRestartRefinedStabilityTuning

/-!
# Generated oracle-restart dynamic regret

This module feeds the generated, observed epoch certificate for the square-root
half-Tsallis schedule into the predictable moving-comparator assembly.  The
switch-count-facing theorem keeps schedule cardinality as an explicit contract;
deriving that contract from a concrete restart law is a separate obligation.
-/

namespace BanditRLProof
namespace Tsallis

open MeasureTheory ProbabilityTheory

universe u v

/-- The generated square-root-schedule epoch certificate assembles into the
schedule-cardinality-facing expected moving-comparator regret bound. -/
theorem
    integral_sampledOracleRestartHalfTsallisPredictableMovingComparatorEnvironmentRegret_sqrtSchedule_le_scheduleSqrt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (schedule : OracleRestartSchedule)
    (loss : Exp3.PredictableLossVector Env Action)
    (epochComparator : Nat -> Action)
    (horizon : Nat)
    (hcomparator :
      ∀ epoch ∈ oracleRestartScheduleEpochs schedule horizon,
        epochComparator epoch ∈ arms) :
    let mu := prior ⊗ₘ sampledOracleRestartHalfTsallisTrajectoryKernel
      arms harms sampledScheduledHalfTsallisSqrtSchedule schedule
        loss.environment
    Integrable
        (sampledOracleRestartHalfTsallisPredictableMovingComparatorEnvironmentRegret
          arms harms sampledScheduledHalfTsallisSqrtSchedule schedule loss
          (fun t => epochComparator (schedule.start t)) horizon) mu ∧
      integral mu
          (sampledOracleRestartHalfTsallisPredictableMovingComparatorEnvironmentRegret
            arms harms sampledScheduledHalfTsallisSqrtSchedule schedule loss
            (fun t => epochComparator (schedule.start t)) horizon) <=
        (8 * Real.sqrt (arms.card : Real)) *
            Real.sqrt
              ((oracleRestartScheduleEpochs schedule horizon).card : Real) *
          Real.sqrt (((horizon + 1 : Nat) : Real)) := by
  apply
    integral_sampledOracleRestartHalfTsallisPredictableMovingComparatorEnvironmentRegret_le_scheduleSqrt_of_epochObservedEstimatedRegret
      prior arms harms sampledScheduledHalfTsallisSqrtSchedule schedule loss
      epochComparator horizon hcomparator
      (8 * Real.sqrt (arms.card : Real))
  · positivity
  · intro epoch hepoch
    have h :=
      integral_sampledOracleRestartHalfTsallisObservedScheduleEpochEstimatedRegret_pointMass_sqrtSchedule_le_eight_mul_sqrt_card_of_mem
        prior arms harms schedule loss horizon epoch
          (hcomparator epoch hepoch) hepoch
    dsimp only at h
    exact h.2

/-- Under an explicit schedule-epoch count contract, the same generated
certificate yields the switch-count-facing expected dynamic-regret bound. -/
theorem
    integral_sampledOracleRestartHalfTsallisPredictableMovingComparatorEnvironmentRegret_sqrtSchedule_le_scheduleSwitchCountSqrt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (schedule : OracleRestartSchedule)
    (loss : Exp3.PredictableLossVector Env Action)
    (epochComparator : Nat -> Action)
    (horizon switches : Nat)
    (hcomparator :
      ∀ epoch ∈ oracleRestartScheduleEpochs schedule horizon,
        epochComparator epoch ∈ arms)
    (hEpochCard :
      (oracleRestartScheduleEpochs schedule horizon).card <= switches + 1) :
    let mu := prior ⊗ₘ sampledOracleRestartHalfTsallisTrajectoryKernel
      arms harms sampledScheduledHalfTsallisSqrtSchedule schedule
        loss.environment
    Integrable
        (sampledOracleRestartHalfTsallisPredictableMovingComparatorEnvironmentRegret
          arms harms sampledScheduledHalfTsallisSqrtSchedule schedule loss
          (fun t => epochComparator (schedule.start t)) horizon) mu ∧
      integral mu
          (sampledOracleRestartHalfTsallisPredictableMovingComparatorEnvironmentRegret
            arms harms sampledScheduledHalfTsallisSqrtSchedule schedule loss
            (fun t => epochComparator (schedule.start t)) horizon) <=
        (8 * Real.sqrt (arms.card : Real)) *
            Real.sqrt (((switches + 1 : Nat) : Real)) *
          Real.sqrt (((horizon + 1 : Nat) : Real)) := by
  apply
    integral_sampledOracleRestartHalfTsallisPredictableMovingComparatorEnvironmentRegret_le_scheduleSwitchCountSqrt_of_epochObservedEstimatedRegret
      prior arms harms sampledScheduledHalfTsallisSqrtSchedule schedule loss
      epochComparator horizon switches hcomparator hEpochCard
      (8 * Real.sqrt (arms.card : Real))
  · positivity
  · intro epoch hepoch
    have h :=
      integral_sampledOracleRestartHalfTsallisObservedScheduleEpochEstimatedRegret_pointMass_sqrtSchedule_le_eight_mul_sqrt_card_of_mem
        prior arms harms schedule loss horizon epoch
          (hcomparator epoch hepoch) hepoch
    dsimp only at h
    exact h.2

end Tsallis
end BanditRLProof
