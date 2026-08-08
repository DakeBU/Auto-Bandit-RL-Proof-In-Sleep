import BanditRLProof.TsallisOracleRestartExpectedRegret

/-!
# Oracle-restart local score alignment

This module identifies every actual restart probability and stored-reward
importance-weighted loss with the corresponding scheduled surface after
shifting to the current epoch's local time. It then exposes the pathwise FTRL
certificate on any explicit contiguous prefix of one restart epoch.
-/

namespace BanditRLProof
namespace Tsallis

universe u v

/-- Shift a generated trajectory so that `start` becomes local time zero. -/
def oracleRestartShiftedTrajectory
    {Env : Type u} {Action : Type v}
    (start : Nat) (sample : Env × ((k : Nat) -> Action × Real)) :
    Env × ((k : Nat) -> Action × Real) :=
  (sample.1, fun localTime => sample.2 (start + localTime))

@[simp]
theorem oracleRestartShiftedTrajectory_fst
    {Env : Type u} {Action : Type v}
    (start : Nat) (sample : Env × ((k : Nat) -> Action × Real)) :
    (oracleRestartShiftedTrajectory start sample).1 = sample.1 :=
  rfl

@[simp]
theorem oracleRestartShiftedTrajectory_snd_apply
    {Env : Type u} {Action : Type v}
    (start : Nat) (sample : Env × ((k : Nat) -> Action × Real))
    (localTime : Nat) :
    (oracleRestartShiftedTrajectory start sample).2 localTime =
      sample.2 (start + localTime) :=
  rfl

/-- Restart epoch starts are monotone in actual time. -/
theorem OracleRestartSchedule.monotone_start
    (schedule : OracleRestartSchedule) :
    Monotone schedule.start := by
  apply monotone_nat_of_le_succ
  intro n
  rcases schedule.start_succ n with hcontinue | hrestart
  · exact hcontinue.ge
  · rw [hrestart]
    exact Nat.le_succ_of_le (schedule.start_le n)

/-- Every epoch identifier visited by the schedule is a fixed point of
`schedule.start`. -/
@[simp]
theorem OracleRestartSchedule.start_start
    (schedule : OracleRestartSchedule) (t : Nat) :
    schedule.start (schedule.start t) = schedule.start t := by
  induction t with
  | zero => simp [schedule.start_zero]
  | succ n ih =>
      rcases schedule.start_succ n with hcontinue | hrestart
      · simpa [hcontinue] using ih
      · simp [hrestart]

/-- A restart schedule cannot leave an epoch and later return to it. -/
theorem OracleRestartSchedule.start_eq_of_between
    (schedule : OracleRestartSchedule) {epoch localTime t : Nat}
    (ht : schedule.start t = epoch)
    (hepoch : epoch <= localTime) (hlocalTime : localTime <= t) :
    schedule.start localTime = epoch := by
  have hlow := schedule.monotone_start
    (show schedule.start t <= localTime by simpa [ht] using hepoch)
  have hhigh := schedule.monotone_start hlocalTime
  rw [schedule.start_start, ht] at hlow
  rw [ht] at hhigh
  omega

/-- At every actual time, the restarted probability is exactly the scheduled
probability at local time `t - schedule.start t` on the shifted trajectory. -/
theorem sampledOracleRestartHalfTsallisProbabilityAtTime_eq_scheduled_shift
    {Env : Type u} {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (schedule : OracleRestartSchedule) (t : Nat)
    (sample : Env × ((k : Nat) -> Action × Real)) :
    sampledOracleRestartHalfTsallisProbabilityAtTime
        arms harms eta schedule t sample =
      sampledScheduledHalfTsallisProbabilityAtTime
        arms harms eta (t - schedule.start t)
        (oracleRestartShiftedTrajectory (schedule.start t) sample) := by
  cases t with
  | zero =>
      simp [sampledOracleRestartHalfTsallisProbabilityAtTime,
        sampledScheduledHalfTsallisProbabilityAtTime,
        schedule.start_zero, oracleRestartShiftedTrajectory]
  | succ n =>
      by_cases hboundary : schedule.start (n + 1) = n + 1
      · simp [sampledOracleRestartHalfTsallisProbabilityAtTime,
          sampledScheduledHalfTsallisProbabilityAtTime, hboundary,
          sampledOracleRestartHalfTsallisHistoryDistribution_of_boundary,
          oracleRestartShiftedTrajectory]
      · have hstart : schedule.start (n + 1) <= n :=
          schedule.start_succ_le_of_ne n hboundary
        have hlocalTime :
            n + 1 - schedule.start (n + 1) =
              (n - schedule.start (n + 1)) + 1 := by
          omega
        rw [sampledOracleRestartHalfTsallisProbabilityAtTime,
          sampledOracleRestartHalfTsallisHistoryDistribution_of_continuation
            arms harms eta schedule n hboundary
              (Preorder.frestrictLe n sample.2),
          hlocalTime]
        change
          sampledScheduledHalfTsallisHistoryDistribution
              arms harms eta (n - schedule.start (n + 1))
              (oracleRestartLocalPairHistory
                (schedule.start (n + 1)) n hstart
                (Preorder.frestrictLe n sample.2)) =
            sampledScheduledHalfTsallisHistoryDistribution
              arms harms eta (n - schedule.start (n + 1))
              (Preorder.frestrictLe (n - schedule.start (n + 1))
                (oracleRestartShiftedTrajectory
                  (schedule.start (n + 1)) sample).2)
        congr 1

/-- The stored-reward restart estimator is the scheduled stored-reward
estimator at the current epoch's local time. -/
theorem sampledOracleRestartHalfTsallisObservedEstimatedLossAt_eq_scheduled_shift
    {Env : Type u} {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (schedule : OracleRestartSchedule) (t : Nat)
    (sample : Env × ((k : Nat) -> Action × Real)) :
    sampledOracleRestartHalfTsallisObservedEstimatedLossAt
        arms harms eta schedule t sample =
      sampledScheduledHalfTsallisObservedEstimatedLossAt
        arms harms eta (t - schedule.start t)
        (oracleRestartShiftedTrajectory (schedule.start t) sample) := by
  have hindex :
      schedule.start t + (t - schedule.start t) = t :=
    Nat.add_sub_of_le (schedule.start_le t)
  unfold sampledOracleRestartHalfTsallisObservedEstimatedLossAt
    sampledScheduledHalfTsallisObservedEstimatedLossAt
  rw [sampledOracleRestartHalfTsallisProbabilityAtTime_eq_scheduled_shift]
  simp [oracleRestartShiftedTrajectory, hindex]

/-- On a fixed epoch fiber, the restarted probability is the scheduled local
probability on the trajectory shifted by that epoch. -/
theorem sampledOracleRestartHalfTsallisProbabilityAtTime_add_eq_scheduled_of_start_eq
    {Env : Type u} {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (schedule : OracleRestartSchedule) (epoch localTime : Nat)
    (sample : Env × ((k : Nat) -> Action × Real))
    (hstart : schedule.start (epoch + localTime) = epoch) :
    sampledOracleRestartHalfTsallisProbabilityAtTime
        arms harms eta schedule (epoch + localTime) sample =
      sampledScheduledHalfTsallisProbabilityAtTime
        arms harms eta localTime
        (oracleRestartShiftedTrajectory epoch sample) := by
  simpa [hstart] using
    sampledOracleRestartHalfTsallisProbabilityAtTime_eq_scheduled_shift
      arms harms eta schedule (epoch + localTime) sample

/-- On a fixed epoch fiber, the stored-reward restarted estimator is the
scheduled local estimator on the shifted trajectory. -/
theorem sampledOracleRestartHalfTsallisObservedEstimatedLossAt_add_eq_scheduled_of_start_eq
    {Env : Type u} {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (schedule : OracleRestartSchedule) (epoch localTime : Nat)
    (sample : Env × ((k : Nat) -> Action × Real))
    (hstart : schedule.start (epoch + localTime) = epoch) :
    sampledOracleRestartHalfTsallisObservedEstimatedLossAt
        arms harms eta schedule (epoch + localTime) sample =
      sampledScheduledHalfTsallisObservedEstimatedLossAt
        arms harms eta localTime
        (oracleRestartShiftedTrajectory epoch sample) := by
  simpa [hstart] using
    sampledOracleRestartHalfTsallisObservedEstimatedLossAt_eq_scheduled_shift
      arms harms eta schedule (epoch + localTime) sample

/-- Stored-reward estimated regret on an explicit inclusive prefix of one
restart epoch, indexed by local times `0, ..., localHorizon`. -/
noncomputable def sampledOracleRestartHalfTsallisLocalPrefixObservedEstimatedRegret
    {Env : Type u} {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (schedule : OracleRestartSchedule)
    (q : Action -> Real) (epoch localHorizon : Nat)
    (sample : Env × ((k : Nat) -> Action × Real)) : Real :=
  (Finset.range (localHorizon + 1)).sum (fun localTime =>
    let actualTime := epoch + localTime
    FTRL.linearLoss arms
        (sampledOracleRestartHalfTsallisProbabilityAtTime
          arms harms eta schedule actualTime sample)
        (sampledOracleRestartHalfTsallisObservedEstimatedLossAt
          arms harms eta schedule actualTime sample) -
      FTRL.linearLoss arms q
        (sampledOracleRestartHalfTsallisObservedEstimatedLossAt
          arms harms eta schedule actualTime sample))

/-- A contiguous restart-epoch prefix is definitionally the existing
scheduled estimated regret on the shifted trajectory. -/
theorem sampledOracleRestartHalfTsallisLocalPrefixObservedEstimatedRegret_eq_scheduled
    {Env : Type u} {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (schedule : OracleRestartSchedule)
    (q : Action -> Real) (epoch localHorizon : Nat)
    (sample : Env × ((k : Nat) -> Action × Real))
    (hstart : forall localTime, localTime <= localHorizon ->
      schedule.start (epoch + localTime) = epoch) :
    sampledOracleRestartHalfTsallisLocalPrefixObservedEstimatedRegret
        arms harms eta schedule q epoch localHorizon sample =
      sampledScheduledHalfTsallisEstimatedRegret
        arms harms eta q localHorizon
        (oracleRestartShiftedTrajectory epoch sample) := by
  unfold sampledOracleRestartHalfTsallisLocalPrefixObservedEstimatedRegret
    sampledScheduledHalfTsallisEstimatedRegret
  apply Finset.sum_congr rfl
  intro localTime hlocalTime
  have hlocalTimeLe : localTime <= localHorizon := by
    exact Nat.le_of_lt_succ (Finset.mem_range.mp hlocalTime)
  dsimp only
  rw [
    sampledOracleRestartHalfTsallisProbabilityAtTime_add_eq_scheduled_of_start_eq
      arms harms eta schedule epoch localTime sample
        (hstart localTime hlocalTimeLe),
    sampledOracleRestartHalfTsallisObservedEstimatedLossAt_add_eq_scheduled_of_start_eq
      arms harms eta schedule epoch localTime sample
        (hstart localTime hlocalTimeLe)]

/-- Pathwise FTRL certificate for any explicit contiguous prefix of one
restart epoch. -/
theorem sampledOracleRestartHalfTsallisLocalPrefixObservedEstimatedRegret_pointMass_le_stability_add_penalty
    {Env : Type u} {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (schedule : OracleRestartSchedule)
    (epoch localHorizon : Nat)
    (sample : Env × ((k : Nat) -> Action × Real))
    {best : Action} (hbest : best ∈ arms)
    (hstart : forall localTime, localTime <= localHorizon ->
      schedule.start (epoch + localTime) = epoch)
    (heta : forall localTime, localTime <= localHorizon ->
      0 < eta localTime)
    (hetaMono : forall localTime, localTime < localHorizon ->
      eta (localTime + 1) <= eta localTime) :
    sampledOracleRestartHalfTsallisLocalPrefixObservedEstimatedRegret
        arms harms eta schedule (pointMass best)
        epoch localHorizon sample <=
      (Finset.range (localHorizon + 1)).sum (fun localTime =>
        sampledScheduledHalfTsallisPotentialStabilityAtTime
          arms harms eta
          (oracleRestartShiftedTrajectory epoch sample) localTime) +
        halfTsallisPotentialMass arms
          (sampledScheduledHalfTsallisProbabilityAtTime
            arms harms eta 0
            (oracleRestartShiftedTrajectory epoch sample)) /
          eta localHorizon -
        1 / eta localHorizon := by
  rw [
    sampledOracleRestartHalfTsallisLocalPrefixObservedEstimatedRegret_eq_scheduled
      arms harms eta schedule (pointMass best) epoch localHorizon sample
        hstart]
  exact
    sampledScheduledHalfTsallisEstimatedRegret_pointMass_le_stability_add_penalty
      arms harms eta (oracleRestartShiftedTrajectory epoch sample)
      hbest localHorizon heta hetaMono

/-- Every visited restart epoch fiber is a nonempty contiguous range starting
at its epoch identifier. -/
theorem exists_oracleRestartEpochRounds_eq_image_range
    (schedule : OracleRestartSchedule) (horizon epoch : Nat)
    (hepoch : epoch ∈ oracleRestartScheduleEpochs schedule horizon) :
    ∃ localHorizon,
      oracleRestartEpochRounds schedule.start horizon epoch =
        (Finset.range (localHorizon + 1)).image
          (fun localTime => epoch + localTime) := by
  rw [oracleRestartScheduleEpochs] at hepoch
  rcases Finset.mem_image.mp hepoch with
    ⟨witness, hwitnessRange, hwitnessStart⟩
  let rounds := oracleRestartEpochRounds schedule.start horizon epoch
  have hwitnessRounds : witness ∈ rounds := by
    simp [rounds, oracleRestartEpochRounds, hwitnessRange, hwitnessStart]
  have hroundsNonempty : rounds.Nonempty :=
    ⟨witness, hwitnessRounds⟩
  let last := rounds.max' hroundsNonempty
  have hlastRounds : last ∈ rounds :=
    Finset.max'_mem rounds hroundsNonempty
  have hlastInfo :
      last ∈ Finset.range (horizon + 1) ∧
        schedule.start last = epoch := by
    simpa [rounds, oracleRestartEpochRounds] using hlastRounds
  have hepochLeLast : epoch <= last := by
    have hstartLe := schedule.start_le last
    omega
  refine ⟨last - epoch, ?_⟩
  change rounds =
    (Finset.range (last - epoch + 1)).image
      (fun localTime => epoch + localTime)
  ext actualTime
  constructor
  · intro hactualTime
    have hactualInfo :
        actualTime ∈ Finset.range (horizon + 1) ∧
          schedule.start actualTime = epoch := by
      simpa [rounds, oracleRestartEpochRounds] using hactualTime
    have hepochLeActualTime : epoch <= actualTime := by
      have hstartLe := schedule.start_le actualTime
      omega
    have hactualTimeLeLast : actualTime <= last :=
      rounds.le_max' actualTime hactualTime
    refine Finset.mem_image.mpr
      ⟨actualTime - epoch, Finset.mem_range.mpr ?_, ?_⟩
    · omega
    · omega
  · intro hactualTime
    rcases Finset.mem_image.mp hactualTime with
      ⟨localTime, hlocalTimeRange, hlocalTimeEq⟩
    have hlocalTimeLt : localTime < last - epoch + 1 :=
      Finset.mem_range.mp hlocalTimeRange
    have hactualTimeLeLast : epoch + localTime <= last := by
      omega
    have hactualTimeStart :
        schedule.start (epoch + localTime) = epoch :=
      schedule.start_eq_of_between hlastInfo.2
        (Nat.le_add_right epoch localTime) hactualTimeLeLast
    have hlastLeHorizon : last <= horizon := by
      exact Nat.le_of_lt_succ (Finset.mem_range.mp hlastInfo.1)
    have hactualTimeRange :
        epoch + localTime ∈ Finset.range (horizon + 1) := by
      exact Finset.mem_range.mpr (by omega)
    have hactualTimeRounds : epoch + localTime ∈ rounds := by
      simp [rounds, oracleRestartEpochRounds, hactualTimeRange,
        hactualTimeStart]
    rw [← hlocalTimeEq]
    exact hactualTimeRounds

/-- An explicit range representation of an actual epoch fiber identifies its
stored-reward regret with the local-prefix surface. -/
theorem sampledOracleRestartHalfTsallisObservedScheduleEpochEstimatedRegret_eq_localPrefix_of_epochRounds_eq
    {Env : Type u} {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (schedule : OracleRestartSchedule)
    (q : Action -> Real) (horizon epoch localHorizon : Nat)
    (sample : Env × ((k : Nat) -> Action × Real))
    (hRounds :
      oracleRestartEpochRounds schedule.start horizon epoch =
        (Finset.range (localHorizon + 1)).image
          (fun localTime => epoch + localTime)) :
    sampledOracleRestartHalfTsallisObservedScheduleEpochEstimatedRegret
        arms harms eta schedule q horizon epoch sample =
      sampledOracleRestartHalfTsallisLocalPrefixObservedEstimatedRegret
        arms harms eta schedule q epoch localHorizon sample := by
  unfold
    sampledOracleRestartHalfTsallisObservedScheduleEpochEstimatedRegret
    sampledOracleRestartHalfTsallisLocalPrefixObservedEstimatedRegret
  rw [hRounds, Finset.sum_image]
  intro localTime₁ _hlocalTime₁ localTime₂ _hlocalTime₂ heq
  exact Nat.add_left_cancel heq

/-- Pathwise FTRL certificate for an actual epoch once its finite fiber is
presented as a contiguous local-time range. -/
theorem sampledOracleRestartHalfTsallisObservedScheduleEpochEstimatedRegret_pointMass_le_stability_add_penalty_of_epochRounds_eq
    {Env : Type u} {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (schedule : OracleRestartSchedule)
    (horizon epoch localHorizon : Nat)
    (sample : Env × ((k : Nat) -> Action × Real))
    {best : Action} (hbest : best ∈ arms)
    (hRounds :
      oracleRestartEpochRounds schedule.start horizon epoch =
        (Finset.range (localHorizon + 1)).image
          (fun localTime => epoch + localTime))
    (heta : forall localTime, localTime <= localHorizon ->
      0 < eta localTime)
    (hetaMono : forall localTime, localTime < localHorizon ->
      eta (localTime + 1) <= eta localTime) :
    sampledOracleRestartHalfTsallisObservedScheduleEpochEstimatedRegret
        arms harms eta schedule (pointMass best) horizon epoch sample <=
      (Finset.range (localHorizon + 1)).sum (fun localTime =>
        sampledScheduledHalfTsallisPotentialStabilityAtTime
          arms harms eta
          (oracleRestartShiftedTrajectory epoch sample) localTime) +
        halfTsallisPotentialMass arms
          (sampledScheduledHalfTsallisProbabilityAtTime
            arms harms eta 0
            (oracleRestartShiftedTrajectory epoch sample)) /
          eta localHorizon -
        1 / eta localHorizon := by
  rw [
    sampledOracleRestartHalfTsallisObservedScheduleEpochEstimatedRegret_eq_localPrefix_of_epochRounds_eq
      arms harms eta schedule (pointMass best) horizon epoch localHorizon
        sample hRounds]
  apply
    sampledOracleRestartHalfTsallisLocalPrefixObservedEstimatedRegret_pointMass_le_stability_add_penalty
      arms harms eta schedule epoch localHorizon sample hbest
  · intro localTime hlocalTime
    have hmemRange : localTime ∈ Finset.range (localHorizon + 1) :=
      Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hlocalTime)
    have hmemImage :
        epoch + localTime ∈
          (Finset.range (localHorizon + 1)).image
            (fun localTime => epoch + localTime) :=
      Finset.mem_image.mpr ⟨localTime, hmemRange, rfl⟩
    have hmemRounds :
        epoch + localTime ∈
          oracleRestartEpochRounds schedule.start horizon epoch := by
      rw [hRounds]
      exact hmemImage
    exact (Finset.mem_filter.mp hmemRounds).2
  · exact heta
  · exact hetaMono

/-- Every visited epoch admits a local horizon whose cardinality is the actual
fiber cardinality and whose stored-reward regret satisfies the pathwise FTRL
stability-plus-penalty certificate. -/
theorem exists_sampledOracleRestartHalfTsallisObservedScheduleEpochEstimatedRegret_pointMass_le_stability_add_penalty
    {Env : Type u} {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (schedule : OracleRestartSchedule)
    (horizon epoch : Nat)
    (hepoch : epoch ∈ oracleRestartScheduleEpochs schedule horizon)
    (sample : Env × ((k : Nat) -> Action × Real))
    {best : Action} (hbest : best ∈ arms)
    (heta : forall localTime, 0 < eta localTime)
    (hetaMono : forall localTime, eta (localTime + 1) <= eta localTime) :
    ∃ localHorizon,
      oracleRestartEpochRounds schedule.start horizon epoch =
          (Finset.range (localHorizon + 1)).image
            (fun localTime => epoch + localTime) ∧
        (oracleRestartEpochRounds
            schedule.start horizon epoch).card = localHorizon + 1 ∧
        sampledOracleRestartHalfTsallisObservedScheduleEpochEstimatedRegret
            arms harms eta schedule (pointMass best) horizon epoch sample <=
          (Finset.range (localHorizon + 1)).sum (fun localTime =>
            sampledScheduledHalfTsallisPotentialStabilityAtTime
              arms harms eta
              (oracleRestartShiftedTrajectory epoch sample) localTime) +
            halfTsallisPotentialMass arms
              (sampledScheduledHalfTsallisProbabilityAtTime
                arms harms eta 0
                (oracleRestartShiftedTrajectory epoch sample)) /
              eta localHorizon -
            1 / eta localHorizon := by
  obtain ⟨localHorizon, hRounds⟩ :=
    exists_oracleRestartEpochRounds_eq_image_range
      schedule horizon epoch hepoch
  refine ⟨localHorizon, hRounds, ?_, ?_⟩
  · rw [hRounds, Finset.card_image_of_injective]
    · simp
    · intro localTime₁ localTime₂ heq
      exact Nat.add_left_cancel heq
  · exact
      sampledOracleRestartHalfTsallisObservedScheduleEpochEstimatedRegret_pointMass_le_stability_add_penalty_of_epochRounds_eq
        arms harms eta schedule horizon epoch localHorizon sample hbest
        hRounds
        (fun localTime _hlocalTime => heta localTime)
        (fun localTime _hlocalTime => hetaMono localTime)

end Tsallis
end BanditRLProof
