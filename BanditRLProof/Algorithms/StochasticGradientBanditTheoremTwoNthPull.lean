import Mathlib.Probability.Process.HittingTime
import BanditRLProof.Algorithms.StochasticGradientBanditTheoremTwoStarvation
import BanditRLProof.MeasurablePullCount

/-!
# Two-arm SGB Theorem 2: chronological nth-pull bridge

Appendix C of Baudry--Johnson--Vary--Pike-Burke--Rebeschini reindexes the
optimal-arm dynamics by the number of times that arm has been selected.  The
generated Lean trajectory is instead indexed by chronological time.  This
module supplies the missing bridge without assuming that the adaptively
selected reward subsequence is IID.

The `pullIndex` argument below is zero based: `pullIndex = 0` denotes the
first optimal-arm pull.  Its time is a `WithTop Nat`; `top` is the explicit
value when that pull never occurs.  At a finite value `t`, the prefix before
`t` contains exactly `pullIndex` optimal pulls, action `t` is optimal, and the
inclusive prefix through `t` contains exactly `pullIndex + 1` optimal pulls.

The extracted reward and post-pull success probability are stopped values on
the same generated trajectory.  Their declarations establish only
measurability and the chronological identification.  No IID, independence,
future-cylinder probability, ballot, or Theorem-2 endpoint is claimed here.
-/

namespace BanditRLProof
namespace StochasticGradientBandit

open MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory
noncomputable section
universe v

/-- Complete an inclusive finite prefix to an action trace, using arm `0`
outside the prefix.  Only coordinates through `prefix` are consumed below. -/
def twoArmPrefixGeneratedAction
    {Env : Type v} (chron : Nat)
    (context : Env × History.FinitePairHistory (Fin 2) Real chron) :
    ActionTrace (Fin 2) :=
  fun t =>
    if h : t <= chron then
      (context.2 ⟨t, Finset.mem_Iic.mpr h⟩).1
    else
      0

/-- Optimal-arm pulls visible in an inclusive finite prefix. -/
def twoArmPrefixOptimalPullCount
    {Env : Type v} (chron : Nat)
    (context : Env × History.FinitePairHistory (Fin 2) Real chron) : Nat :=
  pullCount (twoArmPrefixGeneratedAction chron context) 0 (chron + 1)

theorem measurable_twoArmPrefixGeneratedAction
    {Env : Type v} [MeasurableSpace Env] (chron t : Nat) :
    Measurable
      (fun context : Env × History.FinitePairHistory (Fin 2) Real chron =>
        twoArmPrefixGeneratedAction chron context t) := by
  by_cases ht : t <= chron
  · let index : Finset.Iic chron := ⟨t, Finset.mem_Iic.mpr ht⟩
    have hcoordinate : Measurable
        (fun context : Env × History.FinitePairHistory (Fin 2) Real chron =>
          (context.2 index).1) :=
      measurable_fst.comp ((measurable_pi_apply index).comp measurable_snd)
    simpa [twoArmPrefixGeneratedAction, ht, index] using hcoordinate
  · simp [twoArmPrefixGeneratedAction, ht]

theorem measurable_twoArmPrefixOptimalPullCount
    {Env : Type v} [MeasurableSpace Env] (chron : Nat) :
    Measurable
      (twoArmPrefixOptimalPullCount (Env := Env) chron) := by
  exact measurable_pullCount
    (fun context : Env × History.FinitePairHistory (Fin 2) Real chron =>
      twoArmPrefixGeneratedAction chron context)
    (fun t => measurable_twoArmPrefixGeneratedAction chron t)
    0 (chron + 1)

/-- The finite-prefix count is exactly the chronological count on the ambient
trajectory. -/
@[simp] theorem twoArmPrefixOptimalPullCount_environmentPrefix_eq
    {Env : Type v} [MeasurableSpace Env] (chron : Nat)
    (sample : Env × ((k : Nat) -> Fin 2 × Real)) :
    twoArmPrefixOptimalPullCount chron
        (twoArmEnvironmentPrefix chron sample) =
      twoArmOptimalPullCount (chron + 1) sample := by
  unfold twoArmPrefixOptimalPullCount twoArmOptimalPullCount
  apply pullCount_eq_of_forall_lt
  intro t ht
  have htprefix : t <= chron := Nat.le_of_lt_succ (by simpa using ht)
  simp [twoArmPrefixGeneratedAction, twoArmEnvironmentPrefix,
    twoArmGeneratedAction, htprefix, Preorder.frestrictLe_apply]

/-- Inclusive optimal-arm pull count as a chronological stochastic process. -/
def twoArmInclusiveOptimalPullCountProcess
    {Env : Type v} [MeasurableSpace Env] (chron : Nat)
    (sample : Env × ((k : Nat) -> Fin 2 × Real)) : Nat :=
  twoArmOptimalPullCount (chron + 1) sample

/-- The inclusive count process is adapted to the canonical environment and
generated-prefix filtration. -/
theorem adapted_twoArmInclusiveOptimalPullCountProcess
    {Env : Type v} [MeasurableSpace Env] :
    Adapted (twoArmPrefixFiltration (Env := Env))
      (twoArmInclusiveOptimalPullCountProcess (Env := Env)) := by
  intro chron
  have hprefix :
      @Measurable
        (Env × ((k : Nat) -> Fin 2 × Real))
        (Env × History.FinitePairHistory (Fin 2) Real chron)
        (twoArmPrefixSigma (Env := Env) chron)
        inferInstance
        (twoArmEnvironmentPrefix chron) :=
    comap_measurable _
  have hcomp :=
    (measurable_twoArmPrefixOptimalPullCount
      (Env := Env) chron).comp hprefix
  have hfun :
      twoArmInclusiveOptimalPullCountProcess (Env := Env) chron =
        twoArmPrefixOptimalPullCount chron ∘
          twoArmEnvironmentPrefix chron := by
    funext sample
    exact
      (twoArmPrefixOptimalPullCount_environmentPrefix_eq
        chron sample).symm
  rw [hfun]
  exact hcomp

/-- Zero-based time of the requested optimal-arm pull.  The value is `top`
when that pull never occurs. -/
def twoArmNthOptimalPullTime
    {Env : Type v} [MeasurableSpace Env] (pullIndex : Nat) :
    Env × ((k : Nat) -> Fin 2 × Real) -> WithTop Nat :=
  hittingAfter
    (twoArmInclusiveOptimalPullCountProcess (Env := Env))
    ({pullIndex + 1} : Set Nat) 0

theorem isStoppingTime_twoArmNthOptimalPullTime
    {Env : Type v} [MeasurableSpace Env] (pullIndex : Nat) :
    IsStoppingTime (twoArmPrefixFiltration (Env := Env))
      (twoArmNthOptimalPullTime (Env := Env) pullIndex) := by
  exact
    adapted_twoArmInclusiveOptimalPullCountProcess.isStoppingTime_hittingAfter
      (measurableSet_singleton (pullIndex + 1))

theorem measurable_twoArmNthOptimalPullTime
    {Env : Type v} [MeasurableSpace Env] (pullIndex : Nat) :
    Measurable (twoArmNthOptimalPullTime (Env := Env) pullIndex) :=
  (isStoppingTime_twoArmNthOptimalPullTime
    (Env := Env) pullIndex).measurable'

/-- `top` is precisely the explicit not-yet-pulled case. -/
theorem twoArmNthOptimalPullTime_eq_top_iff
    {Env : Type v} [MeasurableSpace Env] (pullIndex : Nat)
    (sample : Env × ((k : Nat) -> Fin 2 × Real)) :
    twoArmNthOptimalPullTime pullIndex sample = (⊤ : WithTop Nat) <->
      forall chron : Nat,
        twoArmOptimalPullCount (chron + 1) sample ≠ pullIndex + 1 := by
  simp [twoArmNthOptimalPullTime, hittingAfter_eq_top_iff,
    twoArmInclusiveOptimalPullCountProcess]

/-- A missing zero-based requested pull keeps every finite-horizon count below
the corresponding positive count level. -/
theorem twoArmOptimalPullCount_lt_succ_of_nthOptimalPullTime_eq_top
    {Env : Type v} [MeasurableSpace Env] (pullIndex horizon : Nat)
    (sample : Env × ((k : Nat) -> Fin 2 × Real))
    (htop : twoArmNthOptimalPullTime pullIndex sample = (⊤ : WithTop Nat)) :
    twoArmOptimalPullCount horizon sample < pullIndex + 1 := by
  have hnever : ∀ chron,
      pullCount (twoArmGeneratedAction sample) 0 (chron + 1) ≠
        pullIndex + 1 := by
    intro chron
    simpa [twoArmOptimalPullCount] using
      ((twoArmNthOptimalPullTime_eq_top_iff pullIndex sample).mp htop chron)
  simpa [twoArmOptimalPullCount] using
    (pullCount_lt_of_forall_succ_ne
      (twoArmGeneratedAction sample) (0 : Fin 2) horizon
      (pullIndex + 1) (Nat.succ_pos pullIndex) hnever)

/-- If one of the first `m` requested optimal-arm pulls is missing, every
finite-horizon optimal-arm count is strictly below `m`. -/
theorem twoArmOptimalPullCount_lt_of_fin_nthOptimalPullTime_eq_top
    {Env : Type v} [MeasurableSpace Env] (m horizon : Nat) (i : Fin m)
    (sample : Env × ((k : Nat) -> Fin 2 × Real))
    (htop : twoArmNthOptimalPullTime (i : Nat) sample = (⊤ : WithTop Nat)) :
    twoArmOptimalPullCount horizon sample < m := by
  exact lt_of_lt_of_le
    (twoArmOptimalPullCount_lt_succ_of_nthOptimalPullTime_eq_top
      (i : Nat) horizon sample htop)
    (Nat.succ_le_of_lt i.isLt)

/-- At every finite nth-pull time, the inclusive count hits its target. -/
theorem twoArmNthOptimalPullTime_count_succ_eq
    {Env : Type v} [MeasurableSpace Env] (pullIndex : Nat)
    (sample : Env × ((k : Nat) -> Fin 2 × Real))
    (hfinite : twoArmNthOptimalPullTime pullIndex sample ≠ (⊤ : WithTop Nat)) :
    twoArmOptimalPullCount
        ((twoArmNthOptimalPullTime pullIndex sample).untopA + 1) sample =
      pullIndex + 1 := by
  have hmem := hittingAfter_mem_set_of_ne_top
    (u := twoArmInclusiveOptimalPullCountProcess (Env := Env))
    (s := ({pullIndex + 1} : Set Nat))
    (n := 0) hfinite
  simpa [twoArmNthOptimalPullTime,
    twoArmInclusiveOptimalPullCountProcess] using hmem

theorem twoArmNthOptimalPullTime_count_succ_eq_of_eq
    {Env : Type v} [MeasurableSpace Env] (pullIndex t : Nat)
    (sample : Env × ((k : Nat) -> Fin 2 × Real))
    (htime : twoArmNthOptimalPullTime pullIndex sample = (t : WithTop Nat)) :
    twoArmOptimalPullCount (t + 1) sample = pullIndex + 1 := by
  have hfinite :
      twoArmNthOptimalPullTime pullIndex sample ≠ (⊤ : WithTop Nat) := by
    rw [htime]
    exact WithTop.coe_ne_top
  simpa [htime] using
    (twoArmNthOptimalPullTime_count_succ_eq
      pullIndex sample hfinite)

/-- A finite nth-pull time is a genuine selection of the optimal arm. -/
theorem twoArmNthOptimalPullTime_action_eq_zero
    {Env : Type v} [MeasurableSpace Env] (pullIndex t : Nat)
    (sample : Env × ((k : Nat) -> Fin 2 × Real))
    (htime : twoArmNthOptimalPullTime pullIndex sample = (t : WithTop Nat)) :
    twoArmGeneratedAction sample t = 0 := by
  have hcount :
      twoArmOptimalPullCount (t + 1) sample = pullIndex + 1 :=
    twoArmNthOptimalPullTime_count_succ_eq_of_eq
      pullIndex t sample htime
  by_contra haction
  have hprevious :
      twoArmOptimalPullCount t sample = pullIndex + 1 := by
    simpa [twoArmOptimalPullCount, pullCount_succ, haction] using hcount
  cases t with
  | zero =>
      simp [twoArmOptimalPullCount] at hprevious
  | succ t =>
      have hmem :
          twoArmInclusiveOptimalPullCountProcess t sample ∈
            ({pullIndex + 1} : Set Nat) := by
        simpa [twoArmInclusiveOptimalPullCountProcess] using hprevious
      have hle :
          twoArmNthOptimalPullTime pullIndex sample <= (t : WithTop Nat) :=
        hittingAfter_le_of_mem (Nat.zero_le t) hmem
      rw [htime] at hle
      exact (Nat.not_succ_le_self t) (by exact_mod_cast hle)

/-- Immediately before the finite nth-pull time there are exactly
`pullIndex` optimal pulls. -/
theorem twoArmNthOptimalPullTime_count_eq
    {Env : Type v} [MeasurableSpace Env] (pullIndex t : Nat)
    (sample : Env × ((k : Nat) -> Fin 2 × Real))
    (htime : twoArmNthOptimalPullTime pullIndex sample = (t : WithTop Nat)) :
    twoArmOptimalPullCount t sample = pullIndex := by
  have hcount :
      twoArmOptimalPullCount (t + 1) sample = pullIndex + 1 :=
    twoArmNthOptimalPullTime_count_succ_eq_of_eq
      pullIndex t sample htime
  have haction : twoArmGeneratedAction sample t = 0 :=
    twoArmNthOptimalPullTime_action_eq_zero
      pullIndex t sample htime
  simpa [twoArmOptimalPullCount, pullCount_succ, haction] using hcount

/-- The complete deterministic chronological-to-pull-index bridge. -/
theorem twoArmNthOptimalPullTime_spec
    {Env : Type v} [MeasurableSpace Env] (pullIndex t : Nat)
    (sample : Env × ((k : Nat) -> Fin 2 × Real))
    (htime : twoArmNthOptimalPullTime pullIndex sample = (t : WithTop Nat)) :
    twoArmOptimalPullCount t sample = pullIndex /\
      twoArmGeneratedAction sample t = 0 /\
      twoArmOptimalPullCount (t + 1) sample = pullIndex + 1 := by
  exact
    ⟨twoArmNthOptimalPullTime_count_eq pullIndex t sample htime,
      twoArmNthOptimalPullTime_action_eq_zero pullIndex t sample htime,
      twoArmNthOptimalPullTime_count_succ_eq_of_eq
        pullIndex t sample htime⟩

/-- Reward observed at the requested optimal-arm pull.  The value at `top` is
Mathlib's totalized stopped-value default and is never used without a finite
time witness. -/
def twoArmNthOptimalPullReward
    {Env : Type v} [MeasurableSpace Env] (pullIndex : Nat)
    (sample : Env × ((k : Nat) -> Fin 2 × Real)) : Real :=
  stoppedValue
    (fun t sample => (sample.2 t).2)
    (twoArmNthOptimalPullTime pullIndex) sample

theorem adapted_twoArmGeneratedReward
    {Env : Type v} [MeasurableSpace Env] :
    Adapted (twoArmPrefixFiltration (Env := Env))
      (fun (t : Nat)
          (sample : Env × ((k : Nat) -> Fin 2 × Real)) =>
        (sample.2 t).2) := by
  intro t
  have hprefix :
      @Measurable
        (Env × ((k : Nat) -> Fin 2 × Real))
        (Env × History.FinitePairHistory (Fin 2) Real t)
        (twoArmPrefixSigma (Env := Env) t)
        inferInstance
        (twoArmEnvironmentPrefix t) :=
    comap_measurable _
  let index : Finset.Iic t := ⟨t, Finset.mem_Iic.mpr le_rfl⟩
  have hcoordinate : Measurable
      (fun context : Env × History.FinitePairHistory (Fin 2) Real t =>
        (context.2 index).2) :=
    measurable_snd.comp ((measurable_pi_apply index).comp measurable_snd)
  simpa [twoArmEnvironmentPrefix, index, Preorder.frestrictLe_apply] using
    hcoordinate.comp hprefix

theorem measurable_twoArmNthOptimalPullReward
    {Env : Type v} [MeasurableSpace Env] (pullIndex : Nat) :
    Measurable (twoArmNthOptimalPullReward (Env := Env) pullIndex) := by
  have hprogressive :
      ProgMeasurable (twoArmPrefixFiltration (Env := Env))
        (fun (t : Nat)
            (sample : Env × ((k : Nat) -> Fin 2 × Real)) =>
          (sample.2 t).2) :=
    (adapted_twoArmGeneratedReward
      (Env := Env)).stronglyAdapted.progMeasurable_of_discrete
  have hstop := isStoppingTime_twoArmNthOptimalPullTime
    (Env := Env) pullIndex
  have hstopped := measurable_stoppedValue hprogressive
    hstop
  exact hstopped.mono hstop.measurableSpace_le le_rfl

@[simp] theorem twoArmNthOptimalPullReward_eq_of_time_eq
    {Env : Type v} [MeasurableSpace Env] (pullIndex t : Nat)
    (sample : Env × ((k : Nat) -> Fin 2 × Real))
    (htime : twoArmNthOptimalPullTime pullIndex sample = (t : WithTop Nat)) :
    twoArmNthOptimalPullReward pullIndex sample = (sample.2 t).2 := by
  unfold twoArmNthOptimalPullReward
  simp only [stoppedValue]
  rw [htime]
  change (sample.2 t).2 = (sample.2 t).2
  rfl

/-- Post-pull optimal-arm probability at the requested optimal-arm pull. -/
def twoArmNthOptimalPullSuccessProbability
    {Env : Type v} [MeasurableSpace Env] (eta : Real) (pullIndex : Nat)
    (sample : Env × ((k : Nat) -> Fin 2 × Real)) : Real :=
  stoppedValue
    (twoArmSuccessProbability eta)
    (twoArmNthOptimalPullTime pullIndex) sample

theorem adapted_twoArmSuccessProbability
    {Env : Type v} [MeasurableSpace Env] (eta : Real) :
    Adapted (twoArmPrefixFiltration (Env := Env))
      (twoArmSuccessProbability (Env := Env) eta) := by
  intro t
  have hprefix :
      @Measurable
        (Env × ((k : Nat) -> Fin 2 × Real))
        (Env × History.FinitePairHistory (Fin 2) Real t)
        (twoArmPrefixSigma (Env := Env) t)
        inferInstance
        (twoArmEnvironmentPrefix t) :=
    comap_measurable _
  let theta := fun context : Env ×
      History.FinitePairHistory (Fin 2) Real t =>
    historyParameter (fun _ : Fin 2 => 0) eta t context.2
  have htheta (arm : Fin 2) :
      Measurable (fun context => theta context arm) :=
    (measurable_historyParameter
      (fun _ : Fin 2 => 0) eta t arm).comp measurable_snd
  have hprob : Measurable
      (fun context => softmaxProbability (theta context) 0) :=
    measurable_softmaxProbability theta htheta 0
  simpa [twoArmSuccessProbability, theta] using hprob.comp hprefix

theorem measurable_twoArmNthOptimalPullSuccessProbability
    {Env : Type v} [MeasurableSpace Env] (eta : Real) (pullIndex : Nat) :
    Measurable
      (twoArmNthOptimalPullSuccessProbability
        (Env := Env) eta pullIndex) := by
  have hprogressive :
      ProgMeasurable (twoArmPrefixFiltration (Env := Env))
        (twoArmSuccessProbability (Env := Env) eta) :=
    (adapted_twoArmSuccessProbability
      (Env := Env) eta).stronglyAdapted.progMeasurable_of_discrete
  have hstop := isStoppingTime_twoArmNthOptimalPullTime
    (Env := Env) pullIndex
  have hstopped := measurable_stoppedValue hprogressive
    hstop
  exact hstopped.mono hstop.measurableSpace_le le_rfl

@[simp] theorem twoArmNthOptimalPullSuccessProbability_eq_of_time_eq
    {Env : Type v} [MeasurableSpace Env]
    (eta : Real) (pullIndex t : Nat)
    (sample : Env × ((k : Nat) -> Fin 2 × Real))
    (htime : twoArmNthOptimalPullTime pullIndex sample = (t : WithTop Nat)) :
    twoArmNthOptimalPullSuccessProbability eta pullIndex sample =
      twoArmSuccessProbability eta t sample := by
  unfold twoArmNthOptimalPullSuccessProbability
  simp only [stoppedValue]
  rw [htime]
  change twoArmSuccessProbability eta t sample =
    twoArmSuccessProbability eta t sample
  rfl

end
end StochasticGradientBandit
end BanditRLProof
