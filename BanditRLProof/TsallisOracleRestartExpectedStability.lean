import BanditRLProof.TsallisOracleRestartScoreAlignment
import BanditRLProof.TsallisScheduledAllRateExpectedStability

/-!
# Oracle-restart expected local stability

This module transports one restart-local half-Tsallis potential-stability term
through the conditional action law of the single generated restart
trajectory. The shifted trajectory is used only for pathwise reindexing; no
fresh independent epoch law is introduced.
-/

namespace BanditRLProof
namespace Tsallis

open MeasureTheory ProbabilityTheory

universe u v

/-- Local time of an actual round in its restart epoch. -/
def oracleRestartLocalTime
    (schedule : OracleRestartSchedule) (t : Nat) : Nat :=
  t - schedule.start t

/-- Environment and visible global prefix before actual action `n + 1`. -/
def sampledOracleRestartHalfTsallisHistoryAt
    {Env : Type u} {Action : Type v}
    (n : Nat) (sample : Env × ((k : Nat) -> Action × Real)) :
    Env × History.FinitePairHistory Action Real n :=
  (sample.1, Preorder.frestrictLe n sample.2)

/-- Actual successor action after the visible global prefix through `n`. -/
def sampledOracleRestartHalfTsallisActionAt
    {Env : Type u} {Action : Type v}
    (n : Nat) (sample : Env × ((k : Nat) -> Action × Real)) : Action :=
  (sample.2 (n + 1)).1

/-- Restricting a shifted trajectory to its local predecessor prefix is the
same finite history as reindexing the corresponding global prefix. -/
theorem frestrictLe_oracleRestartShiftedTrajectory_eq_localPairHistory
    {Env : Type u} {Action : Type v}
    (start n : Nat) (hstart : start <= n)
    (sample : Env × ((k : Nat) -> Action × Real)) :
    Preorder.frestrictLe (n - start)
        (oracleRestartShiftedTrajectory start sample).2 =
      oracleRestartLocalPairHistory start n hstart
        (Preorder.frestrictLe n sample.2) := by
  funext i
  rfl

/-- Restart-local cumulative score before actual action `n + 1`. -/
noncomputable def sampledOracleRestartHalfTsallisScoreAt
    {Env : Type u} {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (schedule : OracleRestartSchedule) (n : Nat) :
    Env × History.FinitePairHistory Action Real n -> Action -> Real :=
  if hboundary : schedule.start (n + 1) = n + 1 then
    fun _input _candidate => 0
  else
    fun input =>
      sampledScheduledHalfTsallisHistoryScore arms harms eta
        (n - schedule.start (n + 1))
        (oracleRestartLocalPairHistory
          (schedule.start (n + 1)) n
          (schedule.start_succ_le_of_ne n hboundary) input.2)

/-- Predictable loss at actual successor time `n + 1`. -/
def sampledOracleRestartHalfTsallisPredictableLossAt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action]
    (loss : Exp3.PredictableLossVector Env Action) (n : Nat) :
    Env × History.FinitePairHistory Action Real n -> Action -> Real :=
  sampledScheduledHalfTsallisPredictableLossAt loss n

/-- Same-local-rate update after actual action `n + 1`. -/
noncomputable def sampledOracleRestartHalfTsallisUpdatedAt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action] [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (schedule : OracleRestartSchedule)
    (loss : Exp3.PredictableLossVector Env Action) (n : Nat) :
    Env × History.FinitePairHistory Action Real n ->
      Action -> Action -> Real :=
  fun input chosen =>
    halfTsallisMinimizer arms harms
      (eta (oracleRestartLocalTime schedule (n + 1)))
      (fun candidate =>
        sampledOracleRestartHalfTsallisScoreAt
            arms harms eta schedule n input candidate +
          Exp3.importanceWeightedLoss
            (sampledOracleRestartHalfTsallisProbabilityAt
              arms harms eta schedule n input)
            (sampledOracleRestartHalfTsallisPredictableLossAt loss n input)
            chosen candidate)

/-- Restart-local predictable history/action potential-stability score. -/
noncomputable def
    sampledOracleRestartHalfTsallisHistoryActionPotentialStabilityAt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action] [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (schedule : OracleRestartSchedule)
    (loss : Exp3.PredictableLossVector Env Action) (n : Nat) :
    (Env × History.FinitePairHistory Action Real n) × Action -> Real :=
  importanceWeightedPotentialStabilityScore arms
    (eta (oracleRestartLocalTime schedule (n + 1)))
    (sampledOracleRestartHalfTsallisScoreAt arms harms eta schedule n)
    (sampledOracleRestartHalfTsallisProbabilityAt
      (Env := Env) arms harms eta schedule n)
    (sampledOracleRestartHalfTsallisPredictableLossAt loss n)
    (sampledOracleRestartHalfTsallisUpdatedAt
      arms harms eta schedule loss n)

/-- Refined restart-local one-round stability budget. -/
noncomputable def
    sampledOracleRestartHalfTsallisRefinedPotentialStabilityBoundAt
    {Env : Type u} {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (schedule : OracleRestartSchedule) (n : Nat) :
    Env × History.FinitePairHistory Action Real n -> Real :=
  refinedPotentialStabilityBound arms
    (eta (oracleRestartLocalTime schedule (n + 1)))
    (sampledOracleRestartHalfTsallisProbabilityAt
      (Env := Env) arms harms eta schedule n)

/-- Restart-local potential stability at actual successor time `n + 1`,
written with the stored reward before the predictable-law rewrite. -/
noncomputable def
    sampledOracleRestartHalfTsallisObservedPotentialStabilityAtSuccessor
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action] [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (schedule : OracleRestartSchedule) (n : Nat)
    (sample : Env × ((k : Nat) -> Action × Real)) : Real :=
  let input := sampledOracleRestartHalfTsallisHistoryAt n sample
  let chosen := sampledOracleRestartHalfTsallisActionAt n sample
  let probability :=
    sampledOracleRestartHalfTsallisProbabilityAt
      arms harms eta schedule n input
  let estimate :=
    Exp3.importanceWeightedLoss probability
      (fun _candidate => (sample.2 (n + 1)).2) chosen
  let next :=
    halfTsallisMinimizer arms harms
      (eta (oracleRestartLocalTime schedule (n + 1)))
      (fun candidate =>
        sampledOracleRestartHalfTsallisScoreAt
            arms harms eta schedule n input candidate +
          estimate candidate)
  halfTsallisPotentialStability arms
    (eta (oracleRestartLocalTime schedule (n + 1)))
    (sampledOracleRestartHalfTsallisScoreAt
      arms harms eta schedule n input)
    probability estimate next

/-- The stored-reward restart-local potential term is exactly the scheduled
potential term on the path shifted to the current epoch. -/
theorem
    sampledOracleRestartHalfTsallisObservedPotentialStabilityAtSuccessor_eq_shifted
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action] [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (schedule : OracleRestartSchedule) (n : Nat)
    (sample : Env × ((k : Nat) -> Action × Real)) :
    sampledOracleRestartHalfTsallisObservedPotentialStabilityAtSuccessor
        arms harms eta schedule n sample =
      sampledScheduledHalfTsallisPotentialStabilityAtTime
        arms harms eta
        (oracleRestartShiftedTrajectory
          (schedule.start (n + 1)) sample)
        (oracleRestartLocalTime schedule (n + 1)) := by
  let start := schedule.start (n + 1)
  let localTime := oracleRestartLocalTime schedule (n + 1)
  let shifted := oracleRestartShiftedTrajectory start sample
  have hprobability :
      sampledOracleRestartHalfTsallisProbabilityAt
          arms harms eta schedule n
          (sampledOracleRestartHalfTsallisHistoryAt n sample) =
        sampledScheduledHalfTsallisProbabilityAtTime
          arms harms eta localTime shifted := by
    simpa [sampledOracleRestartHalfTsallisProbabilityAt,
      sampledOracleRestartHalfTsallisHistoryAt, start, localTime, shifted,
      sampledOracleRestartHalfTsallisProbabilityAtTime] using
      (sampledOracleRestartHalfTsallisProbabilityAtTime_eq_scheduled_shift
        arms harms eta schedule (n + 1) sample)
  have hestimate :
      Exp3.importanceWeightedLoss
          (sampledOracleRestartHalfTsallisProbabilityAt
            arms harms eta schedule n
            (sampledOracleRestartHalfTsallisHistoryAt n sample))
          (fun _candidate => (sample.2 (n + 1)).2)
          (sampledOracleRestartHalfTsallisActionAt n sample) =
        sampledScheduledHalfTsallisObservedEstimatedLossAt
          arms harms eta localTime shifted := by
    simpa [sampledOracleRestartHalfTsallisObservedEstimatedLossAt,
      sampledOracleRestartHalfTsallisProbabilityAt,
      sampledOracleRestartHalfTsallisHistoryAt,
      sampledOracleRestartHalfTsallisActionAt,
      start, localTime, shifted] using
      (sampledOracleRestartHalfTsallisObservedEstimatedLossAt_eq_scheduled_shift
        arms harms eta schedule (n + 1) sample)
  have hcumulative :
      sampledOracleRestartHalfTsallisScoreAt
          arms harms eta schedule n
          (sampledOracleRestartHalfTsallisHistoryAt n sample) =
        FTRL.cumulativeLoss
          (fun t => sampledScheduledHalfTsallisObservedEstimatedLossAt
            arms harms eta t shifted) localTime := by
    classical
    by_cases hboundary : schedule.start (n + 1) = n + 1
    · have hlocal : localTime = 0 := by
        simp [localTime, oracleRestartLocalTime, hboundary]
      rw [hlocal]
      funext candidate
      simp [sampledOracleRestartHalfTsallisScoreAt, hboundary]
    · have hstart : start <= n := by
        simpa [start] using schedule.start_succ_le_of_ne n hboundary
      have hlocal : localTime = n - start + 1 := by
        unfold localTime oracleRestartLocalTime start
        omega
      rw [hlocal,
        cumulativeLoss_sampledScheduledHalfTsallisObservedEstimatedLossAt_succ]
      unfold sampledOracleRestartHalfTsallisScoreAt
      simp only [hboundary, ↓reduceDIte]
      rw [frestrictLe_oracleRestartShiftedTrajectory_eq_localPairHistory
        start n hstart sample]
      rfl
  unfold sampledOracleRestartHalfTsallisObservedPotentialStabilityAtSuccessor
    sampledScheduledHalfTsallisPotentialStabilityAtTime
    sampledScheduledHalfTsallisSameRateNextAt
    halfTsallisScheduledSameRateNext
  dsimp only
  rw [hestimate, hprobability, hcumulative, FTRL.cumulativeLoss_succ]

/-- On the global generated restart law, the shifted stored-reward local
stability term agrees almost surely with the predictable restart-local
history/action score. -/
theorem
    sampledOracleRestartHalfTsallisShiftedPotentialStabilityAtSuccessor_eq_historyAction_ae
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (schedule : OracleRestartSchedule)
    (loss : Exp3.PredictableLossVector Env Action) (n : Nat) :
    let mu := prior ⊗ₘ sampledOracleRestartHalfTsallisTrajectoryKernel
      arms harms eta schedule loss.environment
    (fun sample =>
      sampledScheduledHalfTsallisPotentialStabilityAtTime
        arms harms eta
        (oracleRestartShiftedTrajectory
          (schedule.start (n + 1)) sample)
        (oracleRestartLocalTime schedule (n + 1))) =ᵐ[mu]
      (fun sample =>
        sampledOracleRestartHalfTsallisHistoryActionPotentialStabilityAt
          arms harms eta schedule loss n
          (sampledOracleRestartHalfTsallisHistoryAt n sample,
            sampledOracleRestartHalfTsallisActionAt n sample)) := by
  dsimp only
  let mu := prior ⊗ₘ sampledOracleRestartHalfTsallisTrajectoryKernel
    arms harms eta schedule loss.environment
  have hestimate :=
    sampledOracleRestartHalfTsallisObservedEstimatedLossAt_eq_predictable_ae
      prior arms harms eta schedule loss (n + 1)
  dsimp only at hestimate
  filter_upwards [hestimate] with sample hsample
  have hestimate' :
      Exp3.importanceWeightedLoss
          (sampledOracleRestartHalfTsallisProbabilityAt
            arms harms eta schedule n
            (sampledOracleRestartHalfTsallisHistoryAt n sample))
          (fun _candidate => (sample.2 (n + 1)).2)
          (sampledOracleRestartHalfTsallisActionAt n sample) =
        Exp3.importanceWeightedLoss
          (sampledOracleRestartHalfTsallisProbabilityAt
            arms harms eta schedule n
            (sampledOracleRestartHalfTsallisHistoryAt n sample))
          (sampledOracleRestartHalfTsallisPredictableLossAt loss n
            (sampledOracleRestartHalfTsallisHistoryAt n sample))
          (sampledOracleRestartHalfTsallisActionAt n sample) := by
    simpa [sampledOracleRestartHalfTsallisObservedEstimatedLossAt,
      sampledOracleRestartHalfTsallisPredictableEstimatedLossAt,
      sampledOracleRestartHalfTsallisProbabilityAtTime,
      sampledOracleRestartHalfTsallisProbabilityAt,
      sampledOracleRestartHalfTsallisHistoryAt,
      sampledOracleRestartHalfTsallisActionAt,
      sampledOracleRestartHalfTsallisPredictableLossAt,
      Exp3.predictableLossAt] using hsample
  rw [←
    sampledOracleRestartHalfTsallisObservedPotentialStabilityAtSuccessor_eq_shifted
      arms harms eta schedule n sample]
  unfold
    sampledOracleRestartHalfTsallisObservedPotentialStabilityAtSuccessor
    sampledOracleRestartHalfTsallisHistoryActionPotentialStabilityAt
    importanceWeightedPotentialStabilityScore
    sampledOracleRestartHalfTsallisUpdatedAt
  dsimp only
  rw [hestimate']

/-- Supported coordinates of the restart-local cumulative score are
measurable on the visible global prefix. -/
theorem measurable_sampledOracleRestartHalfTsallisScoreAt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (schedule : OracleRestartSchedule) (n : Nat)
    (candidate : Action) (hcandidate : candidate ∈ arms) :
    Measurable (fun input : Env × History.FinitePairHistory Action Real n =>
      sampledOracleRestartHalfTsallisScoreAt
        arms harms eta schedule n input candidate) := by
  classical
  unfold sampledOracleRestartHalfTsallisScoreAt
  split_ifs with hboundary
  · exact measurable_const
  · let selector :=
      canonicalHalfTsallisScheduleFiniteHistorySelectorMeasurability
        arms harms eta
    exact
      ((measurable_sampledScheduledHalfTsallisHistoryScore
        arms harms eta selector
        (n - schedule.start (n + 1)) candidate hcandidate).comp
          (measurable_oracleRestartLocalPairHistory
            (Action := Action) (Reward := Real)
            (schedule.start (n + 1)) n
            (schedule.start_succ_le_of_ne n hboundary))).comp measurable_snd

/-- Supported coordinates of the restart-local same-rate update are
measurable. -/
theorem measurable_sampledOracleRestartHalfTsallisUpdatedAt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (schedule : OracleRestartSchedule)
    (loss : Exp3.PredictableLossVector Env Action) (n : Nat)
    (candidate : Action) (hcandidate : candidate ∈ arms) :
    Measurable (fun sample :
        (Env × History.FinitePairHistory Action Real n) × Action =>
      sampledOracleRestartHalfTsallisUpdatedAt
        arms harms eta schedule loss n sample.1 sample.2 candidate) := by
  let updatedScore :
      ((Env × History.FinitePairHistory Action Real n) × Action) ->
        Action -> Real :=
    fun sample selected =>
      sampledOracleRestartHalfTsallisScoreAt
          arms harms eta schedule n sample.1 selected +
        Exp3.importanceWeightedLoss
          (sampledOracleRestartHalfTsallisProbabilityAt
            arms harms eta schedule n sample.1)
          (sampledOracleRestartHalfTsallisPredictableLossAt loss n sample.1)
          sample.2 selected
  have hupdatedScore : forall selected, selected ∈ arms ->
      Measurable (fun sample => updatedScore sample selected) := by
    intro selected hselected
    have hscore : Measurable (fun sample :
        ((Env × History.FinitePairHistory Action Real n) × Action) =>
        sampledOracleRestartHalfTsallisScoreAt
          arms harms eta schedule n sample.1 selected) :=
      (measurable_sampledOracleRestartHalfTsallisScoreAt
        arms harms eta schedule n selected hselected).comp measurable_fst
    have hprob : Measurable (fun sample :
        ((Env × History.FinitePairHistory Action Real n) × Action) =>
        sampledOracleRestartHalfTsallisProbabilityAt
          arms harms eta schedule n sample.1 selected) :=
      ((sampledOracleRestartHalfTsallisEnvironmentHistoryDistributionSource
        (Env := Env) arms harms eta schedule n).measurable_prob
          selected hselected).comp measurable_fst
    have hloss : Measurable (fun sample :
        ((Env × History.FinitePairHistory Action Real n) × Action) =>
        sampledOracleRestartHalfTsallisPredictableLossAt loss n
          sample.1 selected) :=
      (measurable_sampledHalfTsallisPredictableLossAt
        loss n selected).comp measurable_fst
    have hincrement : Measurable (fun sample :
        ((Env × History.FinitePairHistory Action Real n) × Action) =>
        Exp3.importanceWeightedLoss
          (sampledOracleRestartHalfTsallisProbabilityAt
            arms harms eta schedule n sample.1)
          (sampledOracleRestartHalfTsallisPredictableLossAt loss n sample.1)
          sample.2 selected) := by
      unfold Exp3.importanceWeightedLoss
      refine Measurable.ite ?_ (hloss.div hprob) measurable_const
      simpa only [Set.mem_setOf_eq] using
        measurable_snd (measurableSet_singleton selected)
    exact hscore.add hincrement
  have hcanonical : Measurable (fun sample =>
      halfTsallisMinimizer arms harms
        (eta (oracleRestartLocalTime schedule (n + 1)))
        (updatedScore sample) candidate) :=
    measurable_halfTsallisMinimizer_comp arms harms
      (eta (oracleRestartLocalTime schedule (n + 1)))
      updatedScore hupdatedScore candidate hcandidate
  simpa only [updatedScore, sampledOracleRestartHalfTsallisUpdatedAt,
    halfTsallisUpdatedMinimizer] using
      hcanonical

/-- The restart-local predictable history/action potential score is
measurable. -/
theorem
    measurable_sampledOracleRestartHalfTsallisHistoryActionPotentialStabilityAt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (schedule : OracleRestartSchedule)
    (loss : Exp3.PredictableLossVector Env Action) (n : Nat) :
    Measurable
      (sampledOracleRestartHalfTsallisHistoryActionPotentialStabilityAt
        arms harms eta schedule loss n) := by
  unfold sampledOracleRestartHalfTsallisHistoryActionPotentialStabilityAt
  apply measurable_importanceWeightedPotentialStabilityScore
  · intro candidate hcandidate
    exact measurable_sampledOracleRestartHalfTsallisScoreAt
      arms harms eta schedule n candidate hcandidate
  · intro candidate hcandidate
    exact
      (sampledOracleRestartHalfTsallisEnvironmentHistoryDistributionSource
        (Env := Env) arms harms eta schedule n).measurable_prob
          candidate hcandidate
  · intro candidate _hcandidate
    exact measurable_sampledHalfTsallisPredictableLossAt loss n candidate
  · intro candidate hcandidate
    exact measurable_sampledOracleRestartHalfTsallisUpdatedAt
      arms harms eta schedule loss n candidate hcandidate

/-- The refined restart-local budget is integrable under every finite visible
history law when the local rate is positive. -/
theorem
    integrable_sampledOracleRestartHalfTsallisRefinedPotentialStabilityBoundAt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (n : Nat)
    (historyMu : Measure
      (Env × History.FinitePairHistory Action Real n))
    [IsFiniteMeasure historyMu]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (schedule : OracleRestartSchedule)
    (heta : 0 < eta (oracleRestartLocalTime schedule (n + 1))) :
    Integrable
      (sampledOracleRestartHalfTsallisRefinedPotentialStabilityBoundAt
        (Env := Env) arms harms eta schedule n) historyMu := by
  unfold sampledOracleRestartHalfTsallisRefinedPotentialStabilityBoundAt
  exact integrable_refinedPotentialStabilityBound_of_finiteSimplex
    historyMu arms (eta (oracleRestartLocalTime schedule (n + 1)))
    (sampledOracleRestartHalfTsallisProbabilityAt
      (Env := Env) arms harms eta schedule n)
    (sampledOracleRestartHalfTsallisEnvironmentHistoryDistributionSource
      (Env := Env) arms harms eta schedule n) heta

/-- The actual restart probability is the regularized minimizer of the
restart-local pre-action score at the local learning rate. -/
theorem
    sampledOracleRestartHalfTsallisProbabilityAt_isRegularizedMinimizer
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action] [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (schedule : OracleRestartSchedule) (n : Nat)
    (input : Env × History.FinitePairHistory Action Real n) :
    FTRL.IsRegularizedMinimizer (FTRL.finiteSimplex arms)
      arms (eta (oracleRestartLocalTime schedule (n + 1)))
      (negEntropyRegularizer arms (1 / 2 : Real))
      (sampledOracleRestartHalfTsallisScoreAt
        arms harms eta schedule n input)
      (sampledOracleRestartHalfTsallisProbabilityAt
        arms harms eta schedule n input) := by
  classical
  by_cases hboundary : schedule.start (n + 1) = n + 1
  · have hlocal : oracleRestartLocalTime schedule (n + 1) = 0 := by
      simp [oracleRestartLocalTime, hboundary]
    rw [hlocal]
    simpa [sampledOracleRestartHalfTsallisScoreAt, hboundary,
      sampledOracleRestartHalfTsallisProbabilityAt,
      sampledOracleRestartHalfTsallisHistoryDistribution_of_boundary
        arms harms eta schedule n hboundary] using
      (halfTsallisMinimizer_isRegularizedMinimizer
        arms harms (eta 0) (fun _candidate => 0))
  · have hstart := schedule.start_succ_le_of_ne n hboundary
    have hlocal :
        oracleRestartLocalTime schedule (n + 1) =
          n - schedule.start (n + 1) + 1 := by
      unfold oracleRestartLocalTime
      omega
    rw [hlocal]
    simpa [sampledOracleRestartHalfTsallisScoreAt, hboundary,
      sampledOracleRestartHalfTsallisProbabilityAt,
      sampledOracleRestartHalfTsallisHistoryDistribution_of_continuation
        arms harms eta schedule n hboundary,
      sampledScheduledHalfTsallisHistoryDistribution,
      halfTsallisHistoryMinimizer] using
      (halfTsallisMinimizer_isRegularizedMinimizer
        arms harms (eta (n - schedule.start (n + 1) + 1))
        (sampledScheduledHalfTsallisHistoryScore arms harms eta
          (n - schedule.start (n + 1))
          (oracleRestartLocalPairHistory
            (schedule.start (n + 1)) n hstart input.2)))

/-- The same-local-rate restart update is the regularized minimizer after the
predictable ordinary-IW increment. -/
theorem sampledOracleRestartHalfTsallisUpdatedAt_isRegularizedMinimizer
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action] [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (schedule : OracleRestartSchedule)
    (loss : Exp3.PredictableLossVector Env Action) (n : Nat)
    (input : Env × History.FinitePairHistory Action Real n)
    (chosen : Action) :
    FTRL.IsRegularizedMinimizer (FTRL.finiteSimplex arms)
      arms (eta (oracleRestartLocalTime schedule (n + 1)))
      (negEntropyRegularizer arms (1 / 2 : Real))
      (fun candidate =>
        sampledOracleRestartHalfTsallisScoreAt
            arms harms eta schedule n input candidate +
          Exp3.importanceWeightedLoss
            (sampledOracleRestartHalfTsallisProbabilityAt
              arms harms eta schedule n input)
            (sampledOracleRestartHalfTsallisPredictableLossAt loss n input)
            chosen candidate)
      (sampledOracleRestartHalfTsallisUpdatedAt
        arms harms eta schedule loss n input chosen) := by
  unfold sampledOracleRestartHalfTsallisUpdatedAt
  exact halfTsallisMinimizer_isRegularizedMinimizer
    arms harms (eta (oracleRestartLocalTime schedule (n + 1))) _

/-- The restart-local predictable potential score is automatically
integrable under its visible-history/action finite kernel. -/
theorem
    integrable_sampledOracleRestartHalfTsallisHistoryActionPotentialStabilityAt
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (schedule : OracleRestartSchedule)
    (loss : Exp3.PredictableLossVector Env Action) (n : Nat)
    (heta : 0 < eta (oracleRestartLocalTime schedule (n + 1))) :
    let mu := prior ⊗ₘ sampledOracleRestartHalfTsallisTrajectoryKernel
      arms harms eta schedule loss.environment
    Integrable
      (sampledOracleRestartHalfTsallisHistoryActionPotentialStabilityAt
        arms harms eta schedule loss n)
      (mu.map (sampledOracleRestartHalfTsallisHistoryAt n) ⊗ₘ
        sampledOracleRestartHalfTsallisPolicyAt
          (Env := Env) arms harms eta schedule n) := by
  dsimp only
  let mu := prior ⊗ₘ sampledOracleRestartHalfTsallisTrajectoryKernel
    arms harms eta schedule loss.environment
  have hfinite :=
    integrable_importanceWeightedPotentialStabilityScore_finiteActionKernel_coarse
      (mu.map (sampledOracleRestartHalfTsallisHistoryAt n))
      arms (eta (oracleRestartLocalTime schedule (n + 1)))
      (sampledOracleRestartHalfTsallisScoreAt arms harms eta schedule n)
      (sampledOracleRestartHalfTsallisProbabilityAt
        (Env := Env) arms harms eta schedule n)
      (sampledOracleRestartHalfTsallisPredictableLossAt loss n)
      (sampledOracleRestartHalfTsallisUpdatedAt
        arms harms eta schedule loss n)
      (sampledOracleRestartHalfTsallisEnvironmentHistoryDistributionSource
        (Env := Env) arms harms eta schedule n)
      heta
      (sampledOracleRestartHalfTsallisProbabilityAt_isRegularizedMinimizer
        arms harms eta schedule n)
      (fun input chosen _ =>
        sampledOracleRestartHalfTsallisUpdatedAt_isRegularizedMinimizer
          arms harms eta schedule loss n input chosen)
      (fun input candidate _ =>
        loss.successor_mem_unitInterval n input.1 input.2 candidate)
      (measurable_sampledOracleRestartHalfTsallisHistoryActionPotentialStabilityAt
        arms harms eta schedule loss n)
  rw [sampledOracleRestartHalfTsallisPolicyAt_eq_finiteActionKernel
    arms harms eta schedule n]
  simpa [sampledOracleRestartHalfTsallisHistoryActionPotentialStabilityAt,
    mu] using hfinite

/-- Under the single generated restart law, the predictable restart-local
successor stability score is integrable and has coarse expected budget one. -/
theorem
    integral_sampledOracleRestartHalfTsallisHistoryActionPotentialStabilityAt_le_one
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (schedule : OracleRestartSchedule)
    (loss : Exp3.PredictableLossVector Env Action) (n : Nat)
    (heta : 0 < eta (oracleRestartLocalTime schedule (n + 1))) :
    let mu := prior ⊗ₘ sampledOracleRestartHalfTsallisTrajectoryKernel
      arms harms eta schedule loss.environment
    let term := fun sample =>
      sampledOracleRestartHalfTsallisHistoryActionPotentialStabilityAt
        arms harms eta schedule loss n
        (sampledOracleRestartHalfTsallisHistoryAt n sample,
          sampledOracleRestartHalfTsallisActionAt n sample)
    Integrable term mu ∧
      integral mu term <= integral mu (fun _sample => (1 : Real)) := by
  dsimp only
  let mu := prior ⊗ₘ sampledOracleRestartHalfTsallisTrajectoryKernel
    arms harms eta schedule loss.environment
  let history := sampledOracleRestartHalfTsallisHistoryAt
    (Env := Env) (Action := Action) n
  let action := sampledOracleRestartHalfTsallisActionAt
    (Env := Env) (Action := Action) n
  let policy := sampledOracleRestartHalfTsallisPolicyAt
    (Env := Env) arms harms eta schedule n
  have hhistory : Measurable history :=
    measurable_fst.prodMk
      ((Preorder.measurable_frestrictLe n).comp measurable_snd)
  have haction : Measurable action :=
    measurable_fst.comp
      ((measurable_pi_apply (n + 1)).comp measurable_snd)
  have hpolicy :
      policy =ᵐ[mu.map history]
        fun input => Exp3.finiteActionMeasure arms
          (sampledOracleRestartHalfTsallisProbabilityAt
            (Env := Env) arms harms eta schedule n input) := by
    filter_upwards [] with input
    unfold policy
    rw [sampledOracleRestartHalfTsallisPolicyAt_eq_finiteActionKernel,
      Exp3.finiteActionKernel_apply]
  have hcond : condDistrib action history mu =ᵐ[mu.map history] policy := by
    simpa [mu, history, action, policy,
      sampledOracleRestartHalfTsallisHistoryAt,
      sampledOracleRestartHalfTsallisActionAt] using
      (sampledOracleRestartHalfTsallisTrajectoryMeasure_condDistrib_action_given_environment
        prior arms harms eta schedule loss.environment n)
  have hproduct :
      Integrable
        (sampledOracleRestartHalfTsallisHistoryActionPotentialStabilityAt
          arms harms eta schedule loss n)
        (mu.map history ⊗ₘ policy) := by
    simpa [mu, history, policy] using
      (integrable_sampledOracleRestartHalfTsallisHistoryActionPotentialStabilityAt
        prior arms harms eta schedule loss n heta)
  have hcanonical :=
    integral_importanceWeightedPotentialStabilityScore_le_integral_one_of_condDistrib_of_minimizers
      mu history hhistory action haction arms
      (eta (oracleRestartLocalTime schedule (n + 1)))
      (sampledOracleRestartHalfTsallisScoreAt arms harms eta schedule n)
      (sampledOracleRestartHalfTsallisProbabilityAt
        (Env := Env) arms harms eta schedule n)
      (sampledOracleRestartHalfTsallisPredictableLossAt loss n)
      (sampledOracleRestartHalfTsallisUpdatedAt
        arms harms eta schedule loss n)
      policy hpolicy hcond heta
      (sampledOracleRestartHalfTsallisProbabilityAt_isRegularizedMinimizer
        arms harms eta schedule n)
      (fun input chosen _ =>
        sampledOracleRestartHalfTsallisUpdatedAt_isRegularizedMinimizer
          arms harms eta schedule loss n input chosen)
      (fun input candidate _ =>
        loss.successor_mem_unitInterval n input.1 input.2 candidate)
      (measurable_sampledOracleRestartHalfTsallisHistoryActionPotentialStabilityAt
        arms harms eta schedule loss n)
      hproduct
  have htermIntegrable :=
    integrable_score_comp_history_action_of_condDistrib_generic
      mu history hhistory action haction
      (sampledOracleRestartHalfTsallisHistoryActionPotentialStabilityAt
        arms harms eta schedule loss n)
      policy hcond hproduct
  refine ⟨htermIntegrable, ?_⟩
  calc
    integral mu (fun sample =>
        sampledOracleRestartHalfTsallisHistoryActionPotentialStabilityAt
          arms harms eta schedule loss n
          (sampledOracleRestartHalfTsallisHistoryAt n sample,
            sampledOracleRestartHalfTsallisActionAt n sample)) =
      integral mu (fun sample =>
        importanceWeightedPotentialStabilityScore arms
          (eta (oracleRestartLocalTime schedule (n + 1)))
          (sampledOracleRestartHalfTsallisScoreAt
            arms harms eta schedule n)
          (sampledOracleRestartHalfTsallisProbabilityAt
            (Env := Env) arms harms eta schedule n)
          (sampledOracleRestartHalfTsallisPredictableLossAt loss n)
          (sampledOracleRestartHalfTsallisUpdatedAt
            arms harms eta schedule loss n)
          (history sample, action sample)) := by
        rfl
    _ <= integral (mu.map history) (fun _input => (1 : Real)) := hcanonical
    _ = integral mu (fun _sample => (1 : Real)) := by
      rw [integral_map hhistory.aemeasurable
        (integrable_const 1).aestronglyMeasurable]

/-- The actual shifted restart-local successor stability term is integrable
and has coarse expected budget one under the single global restart law. -/
theorem
    integral_sampledOracleRestartHalfTsallisShiftedPotentialStabilityAtSuccessor_le_one
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (schedule : OracleRestartSchedule)
    (loss : Exp3.PredictableLossVector Env Action) (n : Nat)
    (heta : 0 < eta (oracleRestartLocalTime schedule (n + 1))) :
    let mu := prior ⊗ₘ sampledOracleRestartHalfTsallisTrajectoryKernel
      arms harms eta schedule loss.environment
    let term := fun sample =>
      sampledScheduledHalfTsallisPotentialStabilityAtTime
        arms harms eta
        (oracleRestartShiftedTrajectory
          (schedule.start (n + 1)) sample)
        (oracleRestartLocalTime schedule (n + 1))
    Integrable term mu ∧
      integral mu term <= integral mu (fun _sample => (1 : Real)) := by
  dsimp only
  let mu := prior ⊗ₘ sampledOracleRestartHalfTsallisTrajectoryKernel
    arms harms eta schedule loss.environment
  let shiftedTerm := fun
      (sample : Env × ((k : Nat) -> Action × Real)) =>
    sampledScheduledHalfTsallisPotentialStabilityAtTime
      arms harms eta
      (oracleRestartShiftedTrajectory
        (schedule.start (n + 1)) sample)
      (oracleRestartLocalTime schedule (n + 1))
  let predictableTerm := fun
      (sample : Env × ((k : Nat) -> Action × Real)) =>
    sampledOracleRestartHalfTsallisHistoryActionPotentialStabilityAt
      arms harms eta schedule loss n
      (sampledOracleRestartHalfTsallisHistoryAt n sample,
        sampledOracleRestartHalfTsallisActionAt n sample)
  have hbase :=
    integral_sampledOracleRestartHalfTsallisHistoryActionPotentialStabilityAt_le_one
      prior arms harms eta schedule loss n heta
  dsimp only at hbase
  have hae :=
    sampledOracleRestartHalfTsallisShiftedPotentialStabilityAtSuccessor_eq_historyAction_ae
      prior arms harms eta schedule loss n
  dsimp only at hae
  have hae' : shiftedTerm =ᵐ[mu] predictableTerm := by
    simpa [shiftedTerm, predictableTerm, mu] using hae
  refine ⟨hbase.1.congr hae'.symm, ?_⟩
  calc
    integral mu shiftedTerm = integral mu predictableTerm :=
      integral_congr_ae hae'
    _ <= integral mu (fun _sample => (1 : Real)) := by
      simpa [predictableTerm, mu] using hbase.2

/-- At local rates at most one half, the actual shifted restart-local
successor stability term has the refined expected conjugate-potential bound
under the single global restart law. -/
theorem
    integral_sampledOracleRestartHalfTsallisShiftedPotentialStabilityAtSuccessor_le_refined
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (schedule : OracleRestartSchedule)
    (loss : Exp3.PredictableLossVector Env Action) (n : Nat)
    (heta : 0 < eta (oracleRestartLocalTime schedule (n + 1)))
    (heta_le : eta (oracleRestartLocalTime schedule (n + 1)) <= 1 / 2) :
    let mu := prior ⊗ₘ sampledOracleRestartHalfTsallisTrajectoryKernel
      arms harms eta schedule loss.environment
    let term := fun sample =>
      sampledScheduledHalfTsallisPotentialStabilityAtTime
        arms harms eta
        (oracleRestartShiftedTrajectory
          (schedule.start (n + 1)) sample)
        (oracleRestartLocalTime schedule (n + 1))
    let bound := fun sample =>
      sampledOracleRestartHalfTsallisRefinedPotentialStabilityBoundAt
        (Env := Env) arms harms eta schedule n
        (sampledOracleRestartHalfTsallisHistoryAt n sample)
    Integrable term mu ∧ Integrable bound mu ∧
      integral mu term <= integral mu bound := by
  dsimp only
  let mu := prior ⊗ₘ sampledOracleRestartHalfTsallisTrajectoryKernel
    arms harms eta schedule loss.environment
  let history := sampledOracleRestartHalfTsallisHistoryAt
    (Env := Env) (Action := Action) n
  let action := sampledOracleRestartHalfTsallisActionAt
    (Env := Env) (Action := Action) n
  let policy := sampledOracleRestartHalfTsallisPolicyAt
    (Env := Env) arms harms eta schedule n
  let shiftedTerm := fun
      (sample : Env × ((k : Nat) -> Action × Real)) =>
    sampledScheduledHalfTsallisPotentialStabilityAtTime
      arms harms eta
      (oracleRestartShiftedTrajectory
        (schedule.start (n + 1)) sample)
      (oracleRestartLocalTime schedule (n + 1))
  let predictableTerm := fun
      (sample : Env × ((k : Nat) -> Action × Real)) =>
    sampledOracleRestartHalfTsallisHistoryActionPotentialStabilityAt
      arms harms eta schedule loss n
      (history sample, action sample)
  let bound := fun
      (sample : Env × ((k : Nat) -> Action × Real)) =>
    sampledOracleRestartHalfTsallisRefinedPotentialStabilityBoundAt
      (Env := Env) arms harms eta schedule n (history sample)
  have hhistory : Measurable history :=
    measurable_fst.prodMk
      ((Preorder.measurable_frestrictLe n).comp measurable_snd)
  have haction : Measurable action :=
    measurable_fst.comp
      ((measurable_pi_apply (n + 1)).comp measurable_snd)
  have hpolicy :
      policy =ᵐ[mu.map history]
        fun input => Exp3.finiteActionMeasure arms
          (sampledOracleRestartHalfTsallisProbabilityAt
            (Env := Env) arms harms eta schedule n input) := by
    filter_upwards [] with input
    unfold policy
    rw [sampledOracleRestartHalfTsallisPolicyAt_eq_finiteActionKernel,
      Exp3.finiteActionKernel_apply]
  have hcond : condDistrib action history mu =ᵐ[mu.map history] policy := by
    simpa [mu, history, action, policy,
      sampledOracleRestartHalfTsallisHistoryAt,
      sampledOracleRestartHalfTsallisActionAt] using
      (sampledOracleRestartHalfTsallisTrajectoryMeasure_condDistrib_action_given_environment
        prior arms harms eta schedule loss.environment n)
  have hscore : Measurable
      (sampledOracleRestartHalfTsallisHistoryActionPotentialStabilityAt
        arms harms eta schedule loss n) :=
    measurable_sampledOracleRestartHalfTsallisHistoryActionPotentialStabilityAt
      arms harms eta schedule loss n
  have hproduct :
      Integrable
        (sampledOracleRestartHalfTsallisHistoryActionPotentialStabilityAt
          arms harms eta schedule loss n)
        (mu.map history ⊗ₘ policy) := by
    simpa [mu, history, policy] using
      (integrable_sampledOracleRestartHalfTsallisHistoryActionPotentialStabilityAt
        prior arms harms eta schedule loss n heta)
  have hboundMap :
      Integrable
        (sampledOracleRestartHalfTsallisRefinedPotentialStabilityBoundAt
          (Env := Env) arms harms eta schedule n)
        (mu.map history) :=
    integrable_sampledOracleRestartHalfTsallisRefinedPotentialStabilityBoundAt
      n (mu.map history) arms harms eta schedule heta
  have hboundComp : Integrable bound mu := by
    simpa [bound, Function.comp_def] using
      hboundMap.comp_measurable hhistory
  have hcanonical :=
    integral_importanceWeightedPotentialStabilityScore_le_integral_refinedBound_of_condDistrib_of_minimizers
      mu history hhistory action haction arms
      (eta (oracleRestartLocalTime schedule (n + 1)))
      (sampledOracleRestartHalfTsallisScoreAt arms harms eta schedule n)
      (sampledOracleRestartHalfTsallisProbabilityAt
        (Env := Env) arms harms eta schedule n)
      (sampledOracleRestartHalfTsallisPredictableLossAt loss n)
      (sampledOracleRestartHalfTsallisUpdatedAt
        arms harms eta schedule loss n)
      policy hpolicy hcond heta heta_le
      (sampledOracleRestartHalfTsallisProbabilityAt_isRegularizedMinimizer
        arms harms eta schedule n)
      (fun input chosen _ =>
        sampledOracleRestartHalfTsallisUpdatedAt_isRegularizedMinimizer
          arms harms eta schedule loss n input chosen)
      (fun input candidate _ =>
        loss.successor_mem_unitInterval n input.1 input.2 candidate)
      hscore hproduct hboundMap
  have hscoreComp : Integrable predictableTerm mu := by
    simpa [predictableTerm] using
      (integrable_score_comp_history_action_of_condDistrib_generic
        mu history hhistory action haction
        (sampledOracleRestartHalfTsallisHistoryActionPotentialStabilityAt
          arms harms eta schedule loss n)
        policy hcond hproduct)
  have hae :=
    sampledOracleRestartHalfTsallisShiftedPotentialStabilityAtSuccessor_eq_historyAction_ae
      prior arms harms eta schedule loss n
  dsimp only at hae
  have hae' : shiftedTerm =ᵐ[mu] predictableTerm := by
    simpa [shiftedTerm, predictableTerm, history, action, mu] using hae
  refine ⟨hscoreComp.congr hae'.symm, hboundComp, ?_⟩
  calc
    integral mu shiftedTerm = integral mu predictableTerm :=
      integral_congr_ae hae'
    _ <= integral (mu.map history)
        (sampledOracleRestartHalfTsallisRefinedPotentialStabilityBoundAt
          (Env := Env) arms harms eta schedule n) := by
      simpa [predictableTerm,
        sampledOracleRestartHalfTsallisHistoryActionPotentialStabilityAt,
        sampledOracleRestartHalfTsallisRefinedPotentialStabilityBoundAt] using
        hcanonical
    _ = integral mu bound := by
      rw [integral_map hhistory.aemeasurable
        hboundMap.aestronglyMeasurable]

/-- At global time zero, the restart process has the canonical initial
half-Tsallis action law and the usual coarse expected stability budget. -/
theorem
    integral_sampledOracleRestartHalfTsallisInitialPotentialStabilityAtTime_le_one
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (schedule : OracleRestartSchedule) (heta : 0 < eta 0)
    (loss : Exp3.PredictableLossVector Env Action) :
    let mu := prior ⊗ₘ sampledOracleRestartHalfTsallisTrajectoryKernel
      arms harms eta schedule loss.environment
    Integrable (fun sample =>
        sampledScheduledHalfTsallisPotentialStabilityAtTime
          arms harms eta (oracleRestartShiftedTrajectory 0 sample) 0) mu ∧
      integral mu (fun sample =>
          sampledScheduledHalfTsallisPotentialStabilityAtTime
            arms harms eta (oracleRestartShiftedTrajectory 0 sample) 0) <=
        integral mu (fun _sample => (1 : Real)) := by
  dsimp only
  let algorithm :=
    sampledOracleRestartHalfTsallisHistoryAlgorithm
      arms harms eta schedule
  let mu := prior ⊗ₘ sampledOracleRestartHalfTsallisTrajectoryKernel
    arms harms eta schedule loss.environment
  let history := fun sample : Env × ((k : Nat) -> Action × Real) => sample.1
  let action := fun sample : Env × ((k : Nat) -> Action × Real) =>
    (sample.2 0).1
  let score := fun _env : Env => fun _candidate : Action => (0 : Real)
  let prob := fun _env : Env =>
    initialHalfTsallisDistribution arms harms (eta 0)
  let roundLoss := loss.initial
  let next := sampledHalfTsallisInitialUpdatedAt arms harms (eta 0) loss
  let source := initialHalfTsallisEnvironmentDistributionSource
    (Env := Env) arms harms (eta 0)
  let policy := Exp3.finiteActionKernel arms prob source
  have hhistory : Measurable history := measurable_fst
  have haction : Measurable action :=
    measurable_fst.comp ((measurable_pi_apply 0).comp measurable_snd)
  have hkernel : Kernel.const Env algorithm.initialAction = policy := by
    ext env event hevent
    rw [Kernel.const_apply, Exp3.finiteActionKernel_apply]
    rfl
  have hcond : condDistrib action history mu =ᵐ[mu.map history] policy := by
    have hbase :=
      Exp3.canonicalMeasurableEnvironmentTrajectoryMeasure_condDistrib_action_zero_given_environment
        prior algorithm loss.environment
    rw [hkernel] at hbase
    simpa [mu, algorithm, history, action,
      sampledOracleRestartHalfTsallisTrajectoryKernel] using hbase
  have hpolicy : policy =ᵐ[mu.map history]
      fun env => Exp3.finiteActionMeasure arms (prob env) :=
    Exp3.finiteActionKernel_ae_eq_finiteActionMeasure
      (mu.map history) arms prob source
  have hprobMin (env : Env) :
      FTRL.IsRegularizedMinimizer (FTRL.finiteSimplex arms)
        arms (eta 0) (negEntropyRegularizer arms (1 / 2 : Real))
        (score env) (prob env) :=
    halfTsallisMinimizer_isRegularizedMinimizer
      arms harms (eta 0) (score env)
  have hnextMin (env : Env) (chosen : Action) (_hchosen : chosen ∈ arms) :
      FTRL.IsRegularizedMinimizer (FTRL.finiteSimplex arms)
        arms (eta 0) (negEntropyRegularizer arms (1 / 2 : Real))
        (fun candidate => score env candidate +
          Exp3.importanceWeightedLoss
            (prob env) (roundLoss env) chosen candidate)
        (next env chosen) := by
    simpa [score, prob, roundLoss, next,
      sampledHalfTsallisInitialUpdatedAt,
      halfTsallisHistoryUpdatedMinimizer, halfTsallisUpdatedMinimizer] using
      (halfTsallisUpdatedMinimizer_isRegularizedMinimizer
        arms harms (eta 0) (fun _candidate => 0) (loss.initial env) chosen)
  have hloss (env : Env) (candidate : Action) (_hcandidate : candidate ∈ arms) :
      0 <= roundLoss env candidate ∧ roundLoss env candidate <= 1 :=
    loss.initial_mem_unitInterval env candidate
  have hscore : Measurable
      (importanceWeightedPotentialStabilityScore
        arms (eta 0) score prob roundLoss next) := by
    simpa [score, prob, roundLoss, next,
      sampledScheduledHalfTsallisInitialHistoryActionPotentialStability] using
      (measurable_sampledScheduledHalfTsallisInitialHistoryActionPotentialStability
        arms harms eta loss)
  have hproduct : Integrable
      (importanceWeightedPotentialStabilityScore
        arms (eta 0) score prob roundLoss next)
      (mu.map history ⊗ₘ policy) := by
    have hfinite :=
      integrable_importanceWeightedPotentialStabilityScore_finiteActionKernel_coarse
        (mu.map history) arms (eta 0) score prob roundLoss next source
        heta hprobMin hnextMin hloss hscore
    simpa [policy] using hfinite
  have hcanonical :=
    integral_importanceWeightedPotentialStabilityScore_le_integral_one_of_condDistrib_of_minimizers
      mu history hhistory action haction arms (eta 0)
      score prob roundLoss next policy hpolicy hcond heta
      hprobMin hnextMin hloss hscore hproduct
  have hscoreComp : Integrable (fun sample =>
      importanceWeightedPotentialStabilityScore
        arms (eta 0) score prob roundLoss next
        (history sample, action sample)) mu :=
    integrable_score_comp_history_action_of_condDistrib_generic
      mu history hhistory action haction
      (importanceWeightedPotentialStabilityScore
        arms (eta 0) score prob roundLoss next)
      policy hcond hproduct
  have hreward :=
    Exp3.canonicalPredictableTrajectoryMeasure_reward_zero_eq_initialLoss_ae
      prior algorithm loss
  have hreward' :
      (fun sample : Env × ((k : Nat) -> Action × Real) =>
        (sample.2 0).2) =ᵐ[mu]
      (fun sample => loss.initial sample.1 (sample.2 0).1) := by
    simpa [mu, algorithm,
      sampledOracleRestartHalfTsallisTrajectoryKernel] using hreward
  have hterm :
      (fun sample =>
        sampledScheduledHalfTsallisPotentialStabilityAtTime
          arms harms eta (oracleRestartShiftedTrajectory 0 sample) 0) =ᵐ[mu]
      (fun sample =>
        importanceWeightedPotentialStabilityScore
          arms (eta 0) score prob roundLoss next
          (history sample, action sample)) := by
    filter_upwards [hreward'] with sample hrewardSample
    have hestimate :
        sampledScheduledHalfTsallisObservedEstimatedLossAt
            arms harms eta 0 (oracleRestartShiftedTrajectory 0 sample) =
          Exp3.importanceWeightedLoss
            (initialHalfTsallisDistribution arms harms (eta 0))
            (loss.initial sample.1) (sample.2 0).1 := by
      funext candidate
      unfold sampledScheduledHalfTsallisObservedEstimatedLossAt
        sampledScheduledHalfTsallisProbabilityAtTime
      by_cases hchosen : (sample.2 0).1 = candidate
      · simp [oracleRestartShiftedTrajectory,
          Exp3.importanceWeightedLoss, hchosen, hrewardSample]
      · simp [oracleRestartShiftedTrajectory,
          Exp3.importanceWeightedLoss, hchosen]
    have hnext :
        sampledScheduledHalfTsallisSameRateNextAt
            arms harms eta (oracleRestartShiftedTrajectory 0 sample) 0 =
          sampledHalfTsallisInitialUpdatedAt
            arms harms (eta 0) loss sample.1 (sample.2 0).1 := by
      unfold sampledScheduledHalfTsallisSameRateNextAt
        halfTsallisScheduledSameRateNext
        sampledHalfTsallisInitialUpdatedAt
        halfTsallisHistoryUpdatedMinimizer halfTsallisUpdatedMinimizer
      rw [FTRL.cumulativeLoss_succ]
      simp only [FTRL.cumulativeLoss_zero, zero_add]
      rw [hestimate]
      simp [initialHalfTsallisDistribution]
    unfold sampledScheduledHalfTsallisPotentialStabilityAtTime
      importanceWeightedPotentialStabilityScore
    dsimp only
    rw [hestimate, hnext]
    simp [FTRL.cumulativeLoss_zero,
      sampledScheduledHalfTsallisProbabilityAtTime,
      oracleRestartShiftedTrajectory, history, action, score, prob,
      roundLoss, next]
    congr 1
  refine ⟨hscoreComp.congr hterm.symm, ?_⟩
  calc
    integral mu (fun sample =>
        sampledScheduledHalfTsallisPotentialStabilityAtTime
          arms harms eta (oracleRestartShiftedTrajectory 0 sample) 0) =
      integral mu (fun sample =>
        importanceWeightedPotentialStabilityScore
          arms (eta 0) score prob roundLoss next
          (history sample, action sample)) := integral_congr_ae hterm
    _ <= integral (mu.map history) (fun _env => (1 : Real)) := hcanonical
    _ = integral mu (fun _sample => (1 : Real)) := by
      rw [integral_map hhistory.aemeasurable
        (integrable_const 1).aestronglyMeasurable]

/-- Every actual restart time, including global time zero and later restart
boundaries, has the mass-scaled coarse local stability budget under the one
global generated law. -/
theorem
    integral_sampledOracleRestartHalfTsallisShiftedPotentialStabilityAtTime_le_integral_one
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (schedule : OracleRestartSchedule)
    (loss : Exp3.PredictableLossVector Env Action) (t : Nat)
    (heta : 0 < eta (oracleRestartLocalTime schedule t)) :
    let mu := prior ⊗ₘ sampledOracleRestartHalfTsallisTrajectoryKernel
      arms harms eta schedule loss.environment
    let term := fun sample =>
      sampledScheduledHalfTsallisPotentialStabilityAtTime
        arms harms eta
        (oracleRestartShiftedTrajectory (schedule.start t) sample)
        (oracleRestartLocalTime schedule t)
    Integrable term mu ∧
      integral mu term <= integral mu (fun _sample => (1 : Real)) := by
  cases t with
  | zero =>
      have heta0 : 0 < eta 0 := by
        simpa [oracleRestartLocalTime, schedule.start_zero] using heta
      simpa [oracleRestartLocalTime, schedule.start_zero] using
        (integral_sampledOracleRestartHalfTsallisInitialPotentialStabilityAtTime_le_one
          prior arms harms eta schedule heta0 loss)
  | succ n =>
      exact
        integral_sampledOracleRestartHalfTsallisShiftedPotentialStabilityAtSuccessor_le_one
          prior arms harms eta schedule loss n heta

/-- On a deterministic contiguous restart epoch, the complete shifted local
stability prefix is integrable and its expectation is at most the prefix
cardinality. The probability assumption turns the finite-measure one-round
budget into the literal constant `1`. -/
theorem
    integral_sum_sampledOracleRestartHalfTsallisShiftedPotentialStabilityAtLocalPrefix_le_card
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (schedule : OracleRestartSchedule)
    (loss : Exp3.PredictableLossVector Env Action)
    (epoch localHorizon : Nat)
    (hstart : ∀ localTime, localTime ≤ localHorizon ->
      schedule.start (epoch + localTime) = epoch)
    (heta : ∀ localTime, localTime ≤ localHorizon ->
      0 < eta localTime) :
    let mu := prior ⊗ₘ sampledOracleRestartHalfTsallisTrajectoryKernel
      arms harms eta schedule loss.environment
    let stabilitySum := fun sample =>
      (Finset.range (localHorizon + 1)).sum (fun localTime =>
        sampledScheduledHalfTsallisPotentialStabilityAtTime
          arms harms eta
          (oracleRestartShiftedTrajectory epoch sample) localTime)
    Integrable stabilitySum mu ∧
      integral mu stabilitySum ≤ (localHorizon + 1 : Nat) := by
  dsimp only
  let mu := prior ⊗ₘ sampledOracleRestartHalfTsallisTrajectoryKernel
    arms harms eta schedule loss.environment
  let term := fun localTime
      (sample : Env × ((k : Nat) → Action × Real)) =>
    sampledScheduledHalfTsallisPotentialStabilityAtTime
      arms harms eta
      (oracleRestartShiftedTrajectory epoch sample) localTime
  have hterm (localTime : Nat)
      (hlocalTime : localTime ∈ Finset.range (localHorizon + 1)) :
      Integrable (term localTime) mu ∧
        integral mu (term localTime) ≤ 1 := by
    have hle : localTime ≤ localHorizon :=
      Nat.lt_succ_iff.mp (Finset.mem_range.mp hlocalTime)
    have hlocal :
        oracleRestartLocalTime schedule (epoch + localTime) = localTime := by
      simp [oracleRestartLocalTime, hstart localTime hle]
    have hround :=
      integral_sampledOracleRestartHalfTsallisShiftedPotentialStabilityAtTime_le_integral_one
        prior arms harms eta schedule loss (epoch + localTime) (by
          simpa [hlocal] using heta localTime hle)
    have hmass :
        integral mu (fun _sample => (1 : Real)) = 1 := by
      simp [mu]
    refine ⟨?_, ?_⟩
    · simpa [term, mu, hstart localTime hle, hlocal] using hround.1
    · calc
        integral mu (term localTime) ≤
            integral mu (fun _sample => (1 : Real)) := by
          simpa [term, mu, hstart localTime hle, hlocal] using hround.2
        _ = 1 := hmass
  have hsum : Integrable
      (fun sample => (Finset.range (localHorizon + 1)).sum
        (fun localTime => term localTime sample)) mu :=
    IntegrabilitySums.integrable_finset_sum mu
      (Finset.range (localHorizon + 1)) term
      (fun localTime hlocalTime => (hterm localTime hlocalTime).1)
  refine ⟨by simpa [term, mu] using hsum, ?_⟩
  calc
    integral mu (fun sample => (Finset.range (localHorizon + 1)).sum
        (fun localTime => term localTime sample)) =
        (Finset.range (localHorizon + 1)).sum
          (fun localTime => integral mu (term localTime)) := by
      exact ExpectationBochnerSums.integral_finset_sum mu
        (Finset.range (localHorizon + 1)) term
        (fun localTime hlocalTime => (hterm localTime hlocalTime).1)
    _ ≤ (Finset.range (localHorizon + 1)).sum (fun _localTime => (1 : Real)) :=
      Finset.sum_le_sum (fun localTime hlocalTime =>
        (hterm localTime hlocalTime).2)
    _ = (localHorizon + 1 : Nat) := by simp

/-- A contiguous actual restart epoch inherits an expected observed
estimated-regret certificate from the one global generated law. This coarse
endpoint is linear in the epoch cardinality; obtaining the target square-root
certificate still requires summing and tuning the refined one-round bounds. -/
theorem
    integral_sampledOracleRestartHalfTsallisObservedScheduleEpochEstimatedRegret_pointMass_le_card_add_penalty_of_epochRounds_eq
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty) (eta : Nat -> Real)
    (schedule : OracleRestartSchedule)
    (loss : Exp3.PredictableLossVector Env Action)
    (horizon epoch localHorizon : Nat)
    {best : Action} (hbest : best ∈ arms)
    (hRounds :
      oracleRestartEpochRounds schedule.start horizon epoch =
        (Finset.range (localHorizon + 1)).image
          (fun localTime => epoch + localTime))
    (heta : ∀ localTime, localTime ≤ localHorizon ->
      0 < eta localTime)
    (hetaMono : ∀ localTime, localTime < localHorizon ->
      eta (localTime + 1) ≤ eta localTime) :
    let mu := prior ⊗ₘ sampledOracleRestartHalfTsallisTrajectoryKernel
      arms harms eta schedule loss.environment
    let observed :=
      sampledOracleRestartHalfTsallisObservedScheduleEpochEstimatedRegret
        (Env := Env) arms harms eta schedule (pointMass best) horizon epoch
    Integrable observed mu ∧
      integral mu observed ≤
        (localHorizon + 1 : Nat) +
          halfTsallisPotentialMass arms
              (initialHalfTsallisDistribution arms harms (eta 0)) /
            eta localHorizon -
          1 / eta localHorizon := by
  dsimp only
  let mu := prior ⊗ₘ sampledOracleRestartHalfTsallisTrajectoryKernel
    arms harms eta schedule loss.environment
  let observed :=
    sampledOracleRestartHalfTsallisObservedScheduleEpochEstimatedRegret
      (Env := Env) arms harms eta schedule (pointMass best) horizon epoch
  let stabilitySum := fun
      (sample : Env × ((k : Nat) → Action × Real)) =>
    (Finset.range (localHorizon + 1)).sum (fun localTime =>
      sampledScheduledHalfTsallisPotentialStabilityAtTime
        arms harms eta
        (oracleRestartShiftedTrajectory epoch sample) localTime)
  let penalty :=
    halfTsallisPotentialMass arms
        (initialHalfTsallisDistribution arms harms (eta 0)) /
      eta localHorizon -
    1 / eta localHorizon
  let rhs := fun
      (sample : Env × ((k : Nat) → Action × Real)) =>
    stabilitySum sample + penalty
  have hstart (localTime : Nat) (hle : localTime ≤ localHorizon) :
      schedule.start (epoch + localTime) = epoch := by
    have hmemRange :
        localTime ∈ Finset.range (localHorizon + 1) :=
      Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hle)
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
  have hstability :=
    integral_sum_sampledOracleRestartHalfTsallisShiftedPotentialStabilityAtLocalPrefix_le_card
      prior arms harms eta schedule loss epoch localHorizon hstart heta
  dsimp only at hstability
  have hstabilityIntegrable : Integrable stabilitySum mu := by
    simpa [stabilitySum, mu] using hstability.1
  have hstabilityBound :
      integral mu stabilitySum ≤ (localHorizon + 1 : Nat) := by
    simpa [stabilitySum, mu] using hstability.2
  have hobservedData :=
    integral_sampledOracleRestartHalfTsallisObservedScheduleEpochEstimatedRegret_pointMass_eq_epochRegret
      prior arms harms eta schedule loss (fun _epoch => best) epoch hbest
      horizon
  dsimp only at hobservedData
  have hobserved : Integrable observed mu := by
    simpa [observed, mu] using hobservedData.1
  have hrhsIntegrable : Integrable rhs mu := by
    exact hstabilityIntegrable.add (integrable_const _)
  have hpathwise : ∀ᵐ sample ∂mu, observed sample ≤ rhs sample := by
    filter_upwards [] with sample
    have hbase :=
      sampledOracleRestartHalfTsallisObservedScheduleEpochEstimatedRegret_pointMass_le_stability_add_penalty_of_epochRounds_eq
        arms harms eta schedule horizon epoch localHorizon sample hbest
        hRounds heta hetaMono
    unfold observed rhs stabilitySum penalty
    simp only [sampledScheduledHalfTsallisProbabilityAtTime] at hbase
    linarith
  have hintegrated :=
    integral_mono_ae hobserved hrhsIntegrable hpathwise
  have hrhsIntegral :
      integral mu rhs = integral mu stabilitySum + penalty := by
    unfold rhs
    rw [integral_add hstabilityIntegrable (integrable_const _)]
    simp
  refine ⟨hobserved, ?_⟩
  calc
    integral mu observed ≤ integral mu rhs := hintegrated
    _ = integral mu stabilitySum + penalty := hrhsIntegral
    _ ≤ (localHorizon + 1 : Nat) + penalty := by
      linarith
    _ = (localHorizon + 1 : Nat) +
          halfTsallisPotentialMass arms
              (initialHalfTsallisDistribution arms harms (eta 0)) /
            eta localHorizon -
          1 / eta localHorizon := by
      unfold penalty
      ring

end Tsallis
end BanditRLProof
