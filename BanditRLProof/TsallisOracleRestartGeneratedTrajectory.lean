import BanditRLProof.TsallisScheduledScoreAlignment

/-!
# Generated oracle-restart half-Tsallis trajectories

This module constructs the restarted selector and trajectory kernel needed by
the oracle-restart dynamic-regret route. It proves the conditional action law
of that generated process. Epoch-local regret transport remains downstream.
-/

namespace BanditRLProof
namespace Tsallis

open MeasureTheory ProbabilityTheory

universe u v

/-- Start time of the current epoch, with either continuation or a fresh
restart at every successor time. -/
structure OracleRestartSchedule where
  start : Nat -> Nat
  start_zero : start 0 = 0
  start_le : forall t, start t <= t
  start_succ : forall n, start (n + 1) = start n ∨ start (n + 1) = n + 1

/-- One epoch containing the whole trajectory. -/
def oracleNeverRestartSchedule : OracleRestartSchedule where
  start := fun _ => 0
  start_zero := rfl
  start_le := fun t => Nat.zero_le t
  start_succ := fun _ => Or.inl rfl

/-- A fresh one-round epoch at every actual time. -/
def oracleRestartEveryRoundSchedule : OracleRestartSchedule where
  start := id
  start_zero := rfl
  start_le := fun _ => le_rfl
  start_succ := fun _ => Or.inr rfl

/-- Away from a restart boundary, the current epoch starts no later than the
last observed round. -/
theorem OracleRestartSchedule.start_succ_le_of_ne
    (schedule : OracleRestartSchedule) (n : Nat)
    (hboundary : schedule.start (n + 1) ≠ n + 1) :
    schedule.start (n + 1) <= n := by
  have hle := schedule.start_le (n + 1)
  omega

/-- Reindex the inclusive global history segment `start..n` as a local history
through `n-start`. -/
def oracleRestartLocalPairHistory
    {Action Reward : Type*} (start n : Nat) (hstart : start <= n)
    (history : History.FinitePairHistory Action Reward n) :
    History.FinitePairHistory Action Reward (n - start) :=
  fun i =>
    history ⟨start + i.1, Finset.mem_Iic.mpr (by
      have hi := Finset.mem_Iic.mp i.2
      omega)⟩

@[simp]
theorem oracleRestartLocalPairHistory_zero
    {Action Reward : Type*} (n : Nat)
    (history : History.FinitePairHistory Action Reward n) :
    oracleRestartLocalPairHistory 0 n (Nat.zero_le n) history = history := by
  funext i
  simp [oracleRestartLocalPairHistory]

/-- Epoch-suffix reindexing is measurable coordinatewise. -/
theorem measurable_oracleRestartLocalPairHistory
    {Action Reward : Type*}
    [MeasurableSpace Action] [MeasurableSpace Reward]
    (start n : Nat) (hstart : start <= n) :
    Measurable
      (oracleRestartLocalPairHistory
        (Action := Action) (Reward := Reward) start n hstart) := by
  refine measurable_pi_lambda _ ?_
  intro i
  let globalIndex : Finset.Iic n :=
    ⟨start + i.1, Finset.mem_Iic.mpr (by
      have hi := Finset.mem_Iic.mp i.2
      omega)⟩
  exact measurable_pi_apply globalIndex

/-- Restarted successor action distribution. Boundary times use a fresh
initial law; continuation times use only the current epoch's local suffix. -/
noncomputable def sampledOracleRestartHalfTsallisHistoryDistribution
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (schedule : OracleRestartSchedule) (n : Nat) :
    History.FinitePairHistory Action Real n -> Action -> Real :=
  fun history =>
    if hboundary : schedule.start (n + 1) = n + 1 then
      initialHalfTsallisDistribution arms harms (eta 0)
    else
      sampledScheduledHalfTsallisHistoryDistribution
        arms harms eta (n - schedule.start (n + 1))
        (oracleRestartLocalPairHistory
          (schedule.start (n + 1)) n
          (schedule.start_succ_le_of_ne n hboundary) history)

@[simp]
theorem sampledOracleRestartHalfTsallisHistoryDistribution_of_boundary
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (schedule : OracleRestartSchedule) (n : Nat)
    (hboundary : schedule.start (n + 1) = n + 1)
    (history : History.FinitePairHistory Action Real n) :
    sampledOracleRestartHalfTsallisHistoryDistribution
        arms harms eta schedule n history =
      initialHalfTsallisDistribution arms harms (eta 0) := by
  simp [sampledOracleRestartHalfTsallisHistoryDistribution, hboundary]

@[simp]
theorem sampledOracleRestartHalfTsallisHistoryDistribution_of_continuation
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (schedule : OracleRestartSchedule) (n : Nat)
    (hboundary : schedule.start (n + 1) ≠ n + 1)
    (history : History.FinitePairHistory Action Real n) :
    sampledOracleRestartHalfTsallisHistoryDistribution
        arms harms eta schedule n history =
      sampledScheduledHalfTsallisHistoryDistribution
        arms harms eta (n - schedule.start (n + 1))
        (oracleRestartLocalPairHistory
          (schedule.start (n + 1)) n
          (schedule.start_succ_le_of_ne n hboundary) history) := by
  simp [sampledOracleRestartHalfTsallisHistoryDistribution, hboundary]

/-- Every arm in the finite action set keeps strictly positive probability
under either the boundary reset or the continued local scheduled policy. -/
theorem sampledOracleRestartHalfTsallisHistoryDistribution_pos
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (schedule : OracleRestartSchedule) (n : Nat)
    (history : History.FinitePairHistory Action Real n)
    (candidate : Action) (hcandidate : candidate ∈ arms) :
    0 < sampledOracleRestartHalfTsallisHistoryDistribution
      arms harms eta schedule n history candidate := by
  by_cases hboundary : schedule.start (n + 1) = n + 1
  · rw [sampledOracleRestartHalfTsallisHistoryDistribution_of_boundary
      arms harms eta schedule n hboundary history]
    exact isRegularizedMinimizer_pos arms (eta 0) (fun _ => 0)
      (initialHalfTsallisDistribution arms harms (eta 0))
      (halfTsallisMinimizer_isRegularizedMinimizer
        arms harms (eta 0) (fun _ => 0))
      candidate hcandidate
  · rw [sampledOracleRestartHalfTsallisHistoryDistribution_of_continuation
      arms harms eta schedule n hboundary history]
    let localHistory :=
      oracleRestartLocalPairHistory
        (schedule.start (n + 1)) n
        (schedule.start_succ_le_of_ne n hboundary) history
    exact isRegularizedMinimizer_pos arms
      (eta (n - schedule.start (n + 1) + 1))
      (sampledScheduledHalfTsallisHistoryScore
        arms harms eta (n - schedule.start (n + 1)) localHistory)
      (sampledScheduledHalfTsallisHistoryDistribution
        arms harms eta (n - schedule.start (n + 1)) localHistory)
      (halfTsallisMinimizer_isRegularizedMinimizer
        arms harms (eta (n - schedule.start (n + 1) + 1))
        (sampledScheduledHalfTsallisHistoryScore
          arms harms eta (n - schedule.start (n + 1)) localHistory))
      candidate hcandidate

@[simp]
theorem sampledOracleRestartHalfTsallisHistoryDistribution_neverRestart
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (n : Nat) (history : History.FinitePairHistory Action Real n) :
    sampledOracleRestartHalfTsallisHistoryDistribution
        arms harms eta oracleNeverRestartSchedule n history =
      sampledScheduledHalfTsallisHistoryDistribution
        arms harms eta n history := by
  rw [sampledOracleRestartHalfTsallisHistoryDistribution_of_continuation]
  · simp [oracleNeverRestartSchedule]
  · simp [oracleNeverRestartSchedule]

@[simp]
theorem sampledOracleRestartHalfTsallisHistoryDistribution_restartEveryRound
    {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (n : Nat) (history : History.FinitePairHistory Action Real n) :
    sampledOracleRestartHalfTsallisHistoryDistribution
        arms harms eta oracleRestartEveryRoundSchedule n history =
      initialHalfTsallisDistribution arms harms (eta 0) := by
  apply sampledOracleRestartHalfTsallisHistoryDistribution_of_boundary
  rfl

/-- Measurable finite-action source for every restarted successor policy. -/
noncomputable def sampledOracleRestartHalfTsallisHistoryDistributionSource
    {Action : Type u}
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (schedule : OracleRestartSchedule) (n : Nat) :
    Exp3.MeasurableFiniteActionDistribution arms
      (sampledOracleRestartHalfTsallisHistoryDistribution
        arms harms eta schedule n) := by
  classical
  let selector :=
    canonicalHalfTsallisScheduleFiniteHistorySelectorMeasurability
      arms harms eta
  by_cases hboundary : schedule.start (n + 1) = n + 1
  · refine
      { distribution := fun _history => ?_
        measurable_prob := fun _action _haction => ?_ }
    · simpa [sampledOracleRestartHalfTsallisHistoryDistribution, hboundary] using
        finiteActionDistribution_initialHalfTsallisDistribution
          arms harms (eta 0)
    · simp [sampledOracleRestartHalfTsallisHistoryDistribution, hboundary]
  · let hstart := schedule.start_succ_le_of_ne n hboundary
    let localSource :=
      sampledScheduledHalfTsallisHistoryDistributionSource
        arms harms eta selector (n - schedule.start (n + 1))
    refine
      { distribution := fun history => ?_
        measurable_prob := fun action haction => ?_ }
    · simpa [sampledOracleRestartHalfTsallisHistoryDistribution, hboundary,
        hstart, localSource] using
        localSource.distribution
          (oracleRestartLocalPairHistory
            (schedule.start (n + 1)) n hstart history)
    · simpa [sampledOracleRestartHalfTsallisHistoryDistribution, hboundary,
        hstart, localSource] using
        (localSource.measurable_prob action haction).comp
          (measurable_oracleRestartLocalPairHistory
            (Action := Action) (Reward := Real)
            (schedule.start (n + 1)) n hstart)

/-- Stochastic finite-history algorithm whose score resets at every scheduled
epoch boundary. -/
noncomputable def sampledOracleRestartHalfTsallisHistoryAlgorithm
    {Action : Type u}
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (schedule : OracleRestartSchedule) :
    Thompson.HistoryAlgorithm Action Real where
  policy n := Exp3.finiteActionKernel arms
    (sampledOracleRestartHalfTsallisHistoryDistribution
      arms harms eta schedule n)
    (sampledOracleRestartHalfTsallisHistoryDistributionSource
      arms harms eta schedule n)
  policy_isMarkov n := Exp3.instFiniteActionKernelIsMarkovKernel
    arms
    (sampledOracleRestartHalfTsallisHistoryDistribution
      arms harms eta schedule n)
    (sampledOracleRestartHalfTsallisHistoryDistributionSource
      arms harms eta schedule n)
  initialAction := Exp3.finiteActionMeasure arms
    (initialHalfTsallisDistribution arms harms (eta 0))
  initialAction_isProbability :=
    Exp3.finiteActionMeasure_isProbabilityMeasure
      arms (initialHalfTsallisDistribution arms harms (eta 0))
      (finiteActionDistribution_initialHalfTsallisDistribution
        arms harms (eta 0))

@[simp]
theorem sampledOracleRestartHalfTsallisHistoryAlgorithm_policy
    {Action : Type u}
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (schedule : OracleRestartSchedule) (n : Nat) :
    (sampledOracleRestartHalfTsallisHistoryAlgorithm
      arms harms eta schedule).policy n =
      Exp3.finiteActionKernel arms
        (sampledOracleRestartHalfTsallisHistoryDistribution
          arms harms eta schedule n)
        (sampledOracleRestartHalfTsallisHistoryDistributionSource
          arms harms eta schedule n) :=
  rfl

/-- Restarted sampling probabilities at actual trajectory times. -/
noncomputable def sampledOracleRestartHalfTsallisProbabilityAtTime
    {Env : Type v} {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (schedule : OracleRestartSchedule) :
    Nat -> Env × ((k : Nat) -> Action × Real) -> Action -> Real
  | 0, _sample => initialHalfTsallisDistribution arms harms (eta 0)
  | n + 1, sample =>
      sampledOracleRestartHalfTsallisHistoryDistribution
        arms harms eta schedule n (Preorder.frestrictLe n sample.2)

@[simp]
theorem sampledOracleRestartHalfTsallisProbabilityAtTime_neverRestart
    {Env : Type v} {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (t : Nat) (sample : Env × ((k : Nat) -> Action × Real)) :
    sampledOracleRestartHalfTsallisProbabilityAtTime
        arms harms eta oracleNeverRestartSchedule t sample =
      sampledScheduledHalfTsallisProbabilityAtTime
        arms harms eta t sample := by
  cases t with
  | zero => rfl
  | succ n =>
      simp [sampledOracleRestartHalfTsallisProbabilityAtTime,
        sampledScheduledHalfTsallisProbabilityAtTime]

@[simp]
theorem sampledOracleRestartHalfTsallisProbabilityAtTime_restartEveryRound
    {Env : Type v} {Action : Type u} [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (t : Nat) (sample : Env × ((k : Nat) -> Action × Real)) :
    sampledOracleRestartHalfTsallisProbabilityAtTime
        arms harms eta oracleRestartEveryRoundSchedule t sample =
      initialHalfTsallisDistribution arms harms (eta 0) := by
  cases t with
  | zero => rfl
  | succ n =>
      simp [sampledOracleRestartHalfTsallisProbabilityAtTime]

/-- Full environment-indexed trajectory generated by the restarted policy. -/
noncomputable def sampledOracleRestartHalfTsallisTrajectoryKernel
    {Env : Type v} {Action : Type u}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action] [Nonempty Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (schedule : OracleRestartSchedule)
    (environment : Thompson.MeasurableHistoryEnvironment Env Action Real) :
    Kernel Env ((n : Nat) -> Action × Real) :=
  Thompson.canonicalMeasurableEnvironmentTrajectoryKernel
    (sampledOracleRestartHalfTsallisHistoryAlgorithm
      arms harms eta schedule) environment

instance instSampledOracleRestartHalfTsallisTrajectoryKernelIsMarkov
    {Env : Type v} {Action : Type u}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action] [Nonempty Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (schedule : OracleRestartSchedule)
    (environment : Thompson.MeasurableHistoryEnvironment Env Action Real) :
    IsMarkovKernel
      (sampledOracleRestartHalfTsallisTrajectoryKernel
        arms harms eta schedule environment) := by
  unfold sampledOracleRestartHalfTsallisTrajectoryKernel
  infer_instance

/-- The generated successor action has the restarted finite-action law
conditional on the complete visible global history. -/
theorem sampledOracleRestartHalfTsallisTrajectoryMeasure_condDistrib_action
    {Env : Type v} {Action : Type u}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (schedule : OracleRestartSchedule)
    (environment : Thompson.MeasurableHistoryEnvironment Env Action Real)
    (n : Nat) :
    condDistrib
        (fun sample : Env × ((k : Nat) -> Action × Real) =>
          (sample.2 (n + 1)).1)
        (fun sample => Preorder.frestrictLe n sample.2)
        (prior ⊗ₘ sampledOracleRestartHalfTsallisTrajectoryKernel
          arms harms eta schedule environment) =ᵐ[
      (prior ⊗ₘ sampledOracleRestartHalfTsallisTrajectoryKernel
        arms harms eta schedule environment).map
          (fun sample => Preorder.frestrictLe n sample.2)]
      Exp3.finiteActionKernel arms
        (sampledOracleRestartHalfTsallisHistoryDistribution
          arms harms eta schedule n)
        (sampledOracleRestartHalfTsallisHistoryDistributionSource
          arms harms eta schedule n) := by
  simpa [sampledOracleRestartHalfTsallisTrajectoryKernel,
    sampledOracleRestartHalfTsallisHistoryAlgorithm_policy] using
    (Thompson.canonicalMeasurableEnvironmentTrajectoryMeasure_condDistrib_action
      prior
      (sampledOracleRestartHalfTsallisHistoryAlgorithm
        arms harms eta schedule)
      environment n)

/-- The restarted successor action law after retaining both the environment
and the visible global prefix. This is the conditioning surface needed by
predictable-loss first-moment transport. -/
theorem sampledOracleRestartHalfTsallisTrajectoryMeasure_condDistrib_action_given_environment
    {Env : Type v} {Action : Type u}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (schedule : OracleRestartSchedule)
    (environment : Thompson.MeasurableHistoryEnvironment Env Action Real)
    (n : Nat) :
    condDistrib
        (fun sample : Env × ((k : Nat) -> Action × Real) =>
          (sample.2 (n + 1)).1)
        (fun sample : Env × ((k : Nat) -> Action × Real) =>
          (sample.1, Preorder.frestrictLe n sample.2))
        (prior ⊗ₘ sampledOracleRestartHalfTsallisTrajectoryKernel
          arms harms eta schedule environment) =ᵐ[
      (prior ⊗ₘ sampledOracleRestartHalfTsallisTrajectoryKernel
        arms harms eta schedule environment).map
          (fun sample : Env × ((k : Nat) -> Action × Real) =>
            (sample.1, Preorder.frestrictLe n sample.2))]
      (Exp3.finiteActionKernel arms
        (sampledOracleRestartHalfTsallisHistoryDistribution
          arms harms eta schedule n)
        (sampledOracleRestartHalfTsallisHistoryDistributionSource
          arms harms eta schedule n)).comap
        (fun input :
          Env × History.FinitePairHistory Action Real n => input.2)
        (measurable_snd : Measurable
          (fun input :
            Env × History.FinitePairHistory Action Real n => input.2)) := by
  simpa [sampledOracleRestartHalfTsallisTrajectoryKernel,
    sampledOracleRestartHalfTsallisHistoryAlgorithm_policy] using
    (Exp3.trajectoryMixture_condDistrib_action_given_environment_history
      prior
      (sampledOracleRestartHalfTsallisTrajectoryKernel
        arms harms eta schedule environment)
      (Preorder.frestrictLe n) (Preorder.measurable_frestrictLe n)
      (fun trajectory => (trajectory (n + 1)).1)
      (measurable_fst.comp (measurable_pi_apply (n + 1)))
      ((sampledOracleRestartHalfTsallisHistoryAlgorithm
        arms harms eta schedule).policy n)
      (fun env =>
        Thompson.canonicalMeasurableEnvironmentTrajectoryKernel_map_history_action_eq_compProd
          (sampledOracleRestartHalfTsallisHistoryAlgorithm
            arms harms eta schedule)
          environment env n))

end Tsallis
end BanditRLProof
