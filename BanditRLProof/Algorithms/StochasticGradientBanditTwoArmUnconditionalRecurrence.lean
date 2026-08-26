import BanditRLProof.Algorithms.StochasticGradientBanditTwoArmPathIntegrability

/-!
# Unconditional and iterated two-arm SGB recurrences

This module integrates the tower-ready conditional-expectation recurrences on
the canonical trajectory and performs the finite scalar iterations used by the
two-arm Theorem-1 proof.

The source-time fence is explicit.  For an inclusive Lean prefix index `n`,
`twoArmTrajectoryParameterZero eta n` is the source parameter
`theta_{1,n+2}`: trace coordinate zero has already been consumed.
Consequently, `twoArmSuccessProbability eta n` and
`twoArmFailureMass eta n` are source `p_{1,n+2}` and
`1-p_{1,n+2}`.  A tail horizon `N` therefore covers source rounds
`t = 2,...,N+1`; the normalized initial bridge adds the exact source-round
`t = 1` failure square `(1-1/2)^2 = 1/4`.

No reward moment, independence, or conditional-MGF hypothesis is introduced.
The one-step and tail recurrences require only the existing finite prior and
bounded fixed-mean environment contract.  Normalizing the initial environment
mixture requires `IsProbabilityMeasure prior`; the paper-exact fixed-IID
specialization uses a Dirac prior and satisfies this automatically.  The final
failure-mass bound uses precisely `0 < eta` and
`eta * sourceC eta < Delta`.

This module does not assemble Equation (7), control the expected terminal
parameter by the logarithmic forward potential, or state Theorem 1.
-/

namespace BanditRLProof
namespace StochasticGradientBandit

open MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory
noncomputable section
universe v

def twoArmTrajectoryParameterZero
    {Env : Type v} [MeasurableSpace Env]
    (eta : Real) (n : Nat)
    (sample : Env × ((k : Nat) -> Fin 2 × Real)) : Real :=
  historyParameter (fun _ : Fin 2 => 0) eta n
    (twoArmEnvironmentPrefix n sample).2 0

def twoArmForwardPotential
    {Env : Type v} [MeasurableSpace Env]
    (eta : Real) (n : Nat)
    (sample : Env × ((k : Nat) -> Fin 2 × Real)) : Real :=
  Real.exp (2 * twoArmTrajectoryParameterZero eta n sample)

def twoArmInversePotential
    {Env : Type v} [MeasurableSpace Env]
    (eta : Real) (n : Nat)
    (sample : Env × ((k : Nat) -> Fin 2 × Real)) : Real :=
  Real.exp (-2 * twoArmTrajectoryParameterZero eta n sample)

def twoArmSuccessProbability
    {Env : Type v} [MeasurableSpace Env]
    (eta : Real) (n : Nat)
    (sample : Env × ((k : Nat) -> Fin 2 × Real)) : Real :=
  softmaxProbability
    (historyParameter (fun _ : Fin 2 => 0) eta n
      (twoArmEnvironmentPrefix n sample).2) 0

def twoArmFailureMass
    {Env : Type v} [MeasurableSpace Env]
    (eta : Real) (n : Nat)
    (sample : Env × ((k : Nat) -> Fin 2 × Real)) : Real :=
  1 - twoArmSuccessProbability eta n sample

theorem measurable_twoArmTrajectoryParameterZero
    {Env : Type v} [MeasurableSpace Env] (eta : Real) (n : Nat) :
    Measurable (twoArmTrajectoryParameterZero (Env := Env) eta n) := by
  exact (measurable_historyParameter (fun _ : Fin 2 => 0) eta n 0).comp
    (measurable_snd.comp (measurable_twoArmEnvironmentPrefix n))

theorem measurable_twoArmForwardPotential
    {Env : Type v} [MeasurableSpace Env] (eta : Real) (n : Nat) :
    Measurable (twoArmForwardPotential (Env := Env) eta n) := by
  exact Real.measurable_exp.comp
    (measurable_const.mul
      (measurable_twoArmTrajectoryParameterZero eta n))

theorem measurable_twoArmInversePotential
    {Env : Type v} [MeasurableSpace Env] (eta : Real) (n : Nat) :
    Measurable (twoArmInversePotential (Env := Env) eta n) := by
  exact Real.measurable_exp.comp
    (measurable_const.mul
      (measurable_twoArmTrajectoryParameterZero eta n))

theorem measurable_twoArmSuccessProbability
    {Env : Type v} [MeasurableSpace Env] (eta : Real) (n : Nat) :
    Measurable (twoArmSuccessProbability (Env := Env) eta n) := by
  let theta := fun sample : Env × ((k : Nat) -> Fin 2 × Real) =>
    historyParameter (fun _ : Fin 2 => 0) eta n
      (twoArmEnvironmentPrefix n sample).2
  have htheta (arm : Fin 2) : Measurable (fun sample => theta sample arm) :=
    (measurable_historyParameter (fun _ : Fin 2 => 0) eta n arm).comp
      (measurable_snd.comp (measurable_twoArmEnvironmentPrefix n))
  simpa [twoArmSuccessProbability, theta] using
    measurable_softmaxProbability theta htheta 0

theorem measurable_twoArmFailureMass
    {Env : Type v} [MeasurableSpace Env] (eta : Real) (n : Nat) :
    Measurable (twoArmFailureMass (Env := Env) eta n) := by
  exact measurable_const.sub (measurable_twoArmSuccessProbability eta n)

theorem integrable_twoArmForwardPotential
    {Env : Type v} [MeasurableSpace Env] [StandardBorelSpace Env]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (eta : Real)
    (environment : Thompson.MeasurableHistoryEnvironment Env (Fin 2) Real)
    (mean : Fin 2 -> Real)
    (contract : TwoArmBoundedFixedMeanEnvironmentContract environment mean)
    (n : Nat) :
    Integrable (twoArmForwardPotential (Env := Env) eta n)
      (twoArmTrajectoryMeasure prior eta environment) := by
  apply Integrable.of_bound
    (measurable_twoArmForwardPotential eta n).aestronglyMeasurable
    (Real.exp (2 * ((n + 1 : Nat) : Real) * |eta|))
  filter_upwards
      [twoArmTrajectoryMeasure_prefix_rewards_abs_le_one_ae
        prior eta environment mean contract n]
    with sample hreward
  rw [twoArmForwardPotential, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  have htheta := abs_historyParameter_zeroInitialization_le eta n
    (twoArmEnvironmentPrefix n sample).2 0 hreward
  calc
    2 * twoArmTrajectoryParameterZero eta n sample <=
        2 * |twoArmTrajectoryParameterZero eta n sample| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) (by norm_num)
    _ <= 2 * (((n + 1 : Nat) : Real) * |eta|) :=
      mul_le_mul_of_nonneg_left htheta (by norm_num)
    _ = 2 * ((n + 1 : Nat) : Real) * |eta| := by ring

theorem integrable_twoArmInversePotential
    {Env : Type v} [MeasurableSpace Env] [StandardBorelSpace Env]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (eta : Real)
    (environment : Thompson.MeasurableHistoryEnvironment Env (Fin 2) Real)
    (mean : Fin 2 -> Real)
    (contract : TwoArmBoundedFixedMeanEnvironmentContract environment mean)
    (n : Nat) :
    Integrable (twoArmInversePotential (Env := Env) eta n)
      (twoArmTrajectoryMeasure prior eta environment) := by
  apply Integrable.of_bound
    (measurable_twoArmInversePotential eta n).aestronglyMeasurable
    (Real.exp (2 * ((n + 1 : Nat) : Real) * |eta|))
  filter_upwards
      [twoArmTrajectoryMeasure_prefix_rewards_abs_le_one_ae
        prior eta environment mean contract n]
    with sample hreward
  rw [twoArmInversePotential, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  have htheta := abs_historyParameter_zeroInitialization_le eta n
    (twoArmEnvironmentPrefix n sample).2 0 hreward
  change -2 * twoArmTrajectoryParameterZero eta n sample <= _
  have hneg := neg_le_abs (twoArmTrajectoryParameterZero eta n sample)
  calc
    -2 * twoArmTrajectoryParameterZero eta n sample <=
        2 * |twoArmTrajectoryParameterZero eta n sample| := by nlinarith
    _ <= 2 * (((n + 1 : Nat) : Real) * |eta|) :=
      mul_le_mul_of_nonneg_left htheta (by norm_num)
    _ = 2 * ((n + 1 : Nat) : Real) * |eta| := by ring

theorem integrable_twoArmSuccessProbability_sq
    {Env : Type v} [MeasurableSpace Env] [StandardBorelSpace Env]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (eta : Real)
    (environment : Thompson.MeasurableHistoryEnvironment Env (Fin 2) Real)
    (n : Nat) :
    Integrable (fun sample =>
      twoArmSuccessProbability (Env := Env) eta n sample ^ 2)
      (twoArmTrajectoryMeasure prior eta environment) := by
  apply Integrable.of_bound
    ((measurable_twoArmSuccessProbability eta n).pow_const 2).aestronglyMeasurable 1
  filter_upwards [] with sample
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hp0 : 0 <= twoArmSuccessProbability (Env := Env) eta n sample :=
    softmaxProbability_nonneg _ 0
  have hp1 : twoArmSuccessProbability (Env := Env) eta n sample <= 1 :=
    softmaxProbability_le_one _ 0
  nlinarith

theorem integrable_twoArmFailureMass_sq
    {Env : Type v} [MeasurableSpace Env] [StandardBorelSpace Env]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (eta : Real)
    (environment : Thompson.MeasurableHistoryEnvironment Env (Fin 2) Real)
    (n : Nat) :
    Integrable (fun sample =>
      twoArmFailureMass (Env := Env) eta n sample ^ 2)
      (twoArmTrajectoryMeasure prior eta environment) := by
  apply Integrable.of_bound
    ((measurable_twoArmFailureMass eta n).pow_const 2).aestronglyMeasurable 1
  filter_upwards [] with sample
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hp0 : 0 <= twoArmSuccessProbability (Env := Env) eta n sample :=
    softmaxProbability_nonneg _ 0
  have hp1 : twoArmSuccessProbability (Env := Env) eta n sample <= 1 :=
    softmaxProbability_le_one _ 0
  change (1 - twoArmSuccessProbability (Env := Env) eta n sample) ^ 2 <= 1
  nlinarith

theorem twoArmForwardSuccessor_eq_nextPotential
    {Env : Type v} [MeasurableSpace Env]
    (eta : Real) (n : Nat) :
    (fun sample : Env × ((k : Nat) -> Fin 2 × Real) =>
      twoArmForwardSuccessorPotential eta
        (twoArmEnvironmentPrefix n sample).2 (twoArmNextPair n sample)) =
      twoArmForwardPotential (Env := Env) eta (n + 1) := by
  funext sample
  rw [twoArmForwardTrajectorySuccessorPotential_eq_exp_historyParameter]
  rfl

theorem twoArmInverseSuccessor_eq_nextPotential
    {Env : Type v} [MeasurableSpace Env]
    (eta : Real) (n : Nat) :
    (fun sample : Env × ((k : Nat) -> Fin 2 × Real) =>
      twoArmInverseSuccessorPotential eta
        (twoArmEnvironmentPrefix n sample).2 (twoArmNextPair n sample)) =
      twoArmInversePotential (Env := Env) eta (n + 1) := by
  funext sample
  rw [twoArmInverseTrajectorySuccessorPotential_eq_exp_historyParameter]
  rfl

theorem integrable_twoArmForwardRecurrenceBound
    {Env : Type v} [MeasurableSpace Env] [StandardBorelSpace Env]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (eta Delta : Real)
    (environment : Thompson.MeasurableHistoryEnvironment Env (Fin 2) Real)
    (mean : Fin 2 -> Real)
    (contract : TwoArmBoundedFixedMeanEnvironmentContract environment mean)
    (n : Nat) :
    Integrable
      (fun sample : Env × ((k : Nat) -> Fin 2 × Real) =>
        twoArmForwardRecurrenceBound eta Delta
          (twoArmEnvironmentPrefix n sample).2)
      (twoArmTrajectoryMeasure prior eta environment) := by
  have hpotential := integrable_twoArmForwardPotential
    prior eta environment mean contract n
  have hprob := integrable_twoArmSuccessProbability_sq
    prior eta environment n
  simpa [twoArmForwardRecurrenceBound, twoArmForwardPotential,
    twoArmTrajectoryParameterZero, twoArmSuccessProbability] using
    hpotential.add
      ((hprob.const_mul 2).mul_const
        (eta * Delta + eta ^ 2 * sourceC eta))

theorem integrable_twoArmInverseRecurrenceBound
    {Env : Type v} [MeasurableSpace Env] [StandardBorelSpace Env]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (eta Delta : Real)
    (environment : Thompson.MeasurableHistoryEnvironment Env (Fin 2) Real)
    (mean : Fin 2 -> Real)
    (contract : TwoArmBoundedFixedMeanEnvironmentContract environment mean)
    (n : Nat) :
    Integrable
      (fun sample : Env × ((k : Nat) -> Fin 2 × Real) =>
        twoArmInverseRecurrenceBound eta Delta
          (twoArmEnvironmentPrefix n sample).2)
      (twoArmTrajectoryMeasure prior eta environment) := by
  have hpotential := integrable_twoArmInversePotential
    prior eta environment mean contract n
  have hpotential' : Integrable
      (fun sample : Env × ((k : Nat) -> Fin 2 × Real) =>
        Real.exp
          (-2 * historyParameter (fun _ : Fin 2 => 0) eta n
            (twoArmEnvironmentPrefix n sample).2 0))
      (twoArmTrajectoryMeasure prior eta environment) := by
    apply hpotential.congr
    filter_upwards [] with sample
    simp only [twoArmInversePotential,
      twoArmTrajectoryParameterZero]
  have hfailure := integrable_twoArmFailureMass_sq
    prior eta environment n
  simpa [twoArmInverseRecurrenceBound, twoArmInversePotential,
    twoArmTrajectoryParameterZero, twoArmFailureMass,
    twoArmSuccessProbability, mul_assoc, neg_mul] using
    hpotential'.sub
      (((hfailure.const_mul (2 * eta)).mul_const
        (Delta - eta * sourceC eta)))

theorem twoArmForwardUnconditionalRecurrence
    {Env : Type v} [MeasurableSpace Env] [StandardBorelSpace Env]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (eta Delta : Real) (heta : 0 <= eta)
    (environment : Thompson.MeasurableHistoryEnvironment Env (Fin 2) Real)
    (mean : Fin 2 -> Real)
    (contract : TwoArmBoundedFixedMeanEnvironmentContract environment mean)
    (hgap : mean 0 - mean 1 = Delta) (n : Nat) :
    integral (twoArmTrajectoryMeasure prior eta environment)
        (twoArmForwardPotential (Env := Env) eta (n + 1)) <=
      integral (twoArmTrajectoryMeasure prior eta environment)
        (twoArmForwardPotential (Env := Env) eta n) +
      2 * integral (twoArmTrajectoryMeasure prior eta environment)
          (fun sample => twoArmSuccessProbability
            (Env := Env) eta n sample ^ 2) *
        (eta * Delta + eta ^ 2 * sourceC eta) := by
  let mu := twoArmTrajectoryMeasure prior eta environment
  have hrec :=
    twoArmForwardTrajectorySuccessor_condExp_le_recurrenceBound
      prior eta Delta heta environment mean contract hgap n
  have hmono := integral_mono_ae
    (integrable_condExp : Integrable
      (mu[fun sample =>
        twoArmForwardSuccessorPotential eta
          (twoArmEnvironmentPrefix n sample).2 (twoArmNextPair n sample) |
        twoArmPrefixSigma (Env := Env) n]) mu)
    (integrable_twoArmForwardRecurrenceBound
      prior eta Delta environment mean contract n) hrec
  have htower := integral_condExp
    (m := twoArmPrefixSigma (Env := Env) n)
    (μ := mu)
    (f := fun sample : Env × ((k : Nat) -> Fin 2 × Real) =>
      twoArmForwardSuccessorPotential eta
        (twoArmEnvironmentPrefix n sample).2 (twoArmNextPair n sample))
    ((twoArmPrefixFiltration (Env := Env)).le n)
  rw [htower] at hmono
  rw [twoArmForwardSuccessor_eq_nextPotential eta n] at hmono
  have hpotential := integrable_twoArmForwardPotential
    prior eta environment mean contract n
  have hprob := integrable_twoArmSuccessProbability_sq
    prior eta environment n
  change _ <= integral mu
    (fun sample => twoArmForwardPotential eta n sample +
      2 * twoArmSuccessProbability eta n sample ^ 2 *
        (eta * Delta + eta ^ 2 * sourceC eta)) at hmono
  rw [integral_add hpotential
      ((hprob.const_mul 2).mul_const
        (eta * Delta + eta ^ 2 * sourceC eta)),
    integral_mul_const, integral_const_mul] at hmono
  exact hmono

theorem twoArmInverseUnconditionalRecurrence
    {Env : Type v} [MeasurableSpace Env] [StandardBorelSpace Env]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (eta Delta : Real) (heta : 0 <= eta)
    (environment : Thompson.MeasurableHistoryEnvironment Env (Fin 2) Real)
    (mean : Fin 2 -> Real)
    (contract : TwoArmBoundedFixedMeanEnvironmentContract environment mean)
    (hgap : mean 0 - mean 1 = Delta) (n : Nat) :
    integral (twoArmTrajectoryMeasure prior eta environment)
        (twoArmInversePotential (Env := Env) eta (n + 1)) <=
      integral (twoArmTrajectoryMeasure prior eta environment)
        (twoArmInversePotential (Env := Env) eta n) -
      2 * eta * integral (twoArmTrajectoryMeasure prior eta environment)
          (fun sample => twoArmFailureMass
            (Env := Env) eta n sample ^ 2) *
        (Delta - eta * sourceC eta) := by
  let mu := twoArmTrajectoryMeasure prior eta environment
  have hrec :=
    twoArmInverseTrajectorySuccessor_condExp_le_recurrenceBound
      prior eta Delta heta environment mean contract hgap n
  have hmono := integral_mono_ae
    (integrable_condExp : Integrable
      (mu[fun sample =>
        twoArmInverseSuccessorPotential eta
          (twoArmEnvironmentPrefix n sample).2 (twoArmNextPair n sample) |
        twoArmPrefixSigma (Env := Env) n]) mu)
    (integrable_twoArmInverseRecurrenceBound
      prior eta Delta environment mean contract n) hrec
  have htower := integral_condExp
    (m := twoArmPrefixSigma (Env := Env) n)
    (μ := mu)
    (f := fun sample : Env × ((k : Nat) -> Fin 2 × Real) =>
      twoArmInverseSuccessorPotential eta
        (twoArmEnvironmentPrefix n sample).2 (twoArmNextPair n sample))
    ((twoArmPrefixFiltration (Env := Env)).le n)
  rw [htower] at hmono
  rw [twoArmInverseSuccessor_eq_nextPotential eta n] at hmono
  have hpotential := integrable_twoArmInversePotential
    prior eta environment mean contract n
  have hfailure := integrable_twoArmFailureMass_sq
    prior eta environment n
  change _ <= integral mu
    (fun sample => twoArmInversePotential eta n sample -
      2 * eta * twoArmFailureMass eta n sample ^ 2 *
        (Delta - eta * sourceC eta)) at hmono
  rw [integral_sub hpotential
      (((hfailure.const_mul (2 * eta)).mul_const
        (Delta - eta * sourceC eta))),
    integral_mul_const, integral_const_mul] at hmono
  exact hmono

/-! Pure scalar iteration leaves.  These add no stochastic assumptions. -/

theorem twoArmScalarForwardIterate
    (value increment : Nat -> Real)
    (hstep : forall n, value (n + 1) <= value n + increment n) :
    forall horizon,
      value horizon <= value 0 + (Finset.range horizon).sum increment := by
  intro horizon
  induction horizon with
  | zero => simp
  | succ n ih =>
      calc
        value (n + 1) <= value n + increment n := hstep n
        _ <= (value 0 + (Finset.range n).sum increment) + increment n :=
          by linarith
        _ = value 0 + (Finset.range (n + 1)).sum increment := by
          rw [Finset.sum_range_succ]
          ring

theorem twoArmScalarInverseTelescope
    (value failure : Nat -> Real) (coefficient : Real)
    (hstep : forall n,
      value (n + 1) <= value n - coefficient * failure n) :
    forall horizon,
      coefficient * (Finset.range horizon).sum failure <=
        value 0 - value horizon := by
  intro horizon
  induction horizon with
  | zero => simp
  | succ n ih =>
      have hlast : coefficient * failure n <= value n - value (n + 1) := by
        linarith [hstep n]
      rw [Finset.sum_range_succ]
      calc
        coefficient * ((Finset.range n).sum failure + failure n) =
            coefficient * (Finset.range n).sum failure +
              coefficient * failure n := by ring
        _ <= (value 0 - value n) + (value n - value (n + 1)) :=
          add_le_add ih hlast
        _ = value 0 - value (n + 1) := by ring

theorem twoArmForwardFiniteIteration
    {Env : Type v} [MeasurableSpace Env] [StandardBorelSpace Env]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (eta Delta : Real) (heta : 0 <= eta)
    (environment : Thompson.MeasurableHistoryEnvironment Env (Fin 2) Real)
    (mean : Fin 2 -> Real)
    (contract : TwoArmBoundedFixedMeanEnvironmentContract environment mean)
    (hgap : mean 0 - mean 1 = Delta) (horizon : Nat) :
    integral (twoArmTrajectoryMeasure prior eta environment)
        (twoArmForwardPotential (Env := Env) eta horizon) <=
      integral (twoArmTrajectoryMeasure prior eta environment)
          (twoArmForwardPotential (Env := Env) eta 0) +
        (Finset.range horizon).sum (fun n =>
          2 * integral (twoArmTrajectoryMeasure prior eta environment)
              (fun sample => twoArmSuccessProbability
                (Env := Env) eta n sample ^ 2) *
            (eta * Delta + eta ^ 2 * sourceC eta)) := by
  let value := fun n =>
    integral (twoArmTrajectoryMeasure prior eta environment)
      (twoArmForwardPotential (Env := Env) eta n)
  let increment := fun n =>
    2 * integral (twoArmTrajectoryMeasure prior eta environment)
        (fun sample => twoArmSuccessProbability
          (Env := Env) eta n sample ^ 2) *
      (eta * Delta + eta ^ 2 * sourceC eta)
  exact twoArmScalarForwardIterate value increment
    (fun n => twoArmForwardUnconditionalRecurrence
      prior eta Delta heta environment mean contract hgap n) horizon

theorem twoArmInverseFailureMassSqTelescope
    {Env : Type v} [MeasurableSpace Env] [StandardBorelSpace Env]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (eta Delta : Real) (heta : 0 <= eta)
    (environment : Thompson.MeasurableHistoryEnvironment Env (Fin 2) Real)
    (mean : Fin 2 -> Real)
    (contract : TwoArmBoundedFixedMeanEnvironmentContract environment mean)
    (hgap : mean 0 - mean 1 = Delta) (horizon : Nat) :
    (2 * eta * (Delta - eta * sourceC eta)) *
        (Finset.range horizon).sum (fun n =>
          integral (twoArmTrajectoryMeasure prior eta environment)
            (fun sample => twoArmFailureMass
              (Env := Env) eta n sample ^ 2)) <=
      integral (twoArmTrajectoryMeasure prior eta environment)
          (twoArmInversePotential (Env := Env) eta 0) -
        integral (twoArmTrajectoryMeasure prior eta environment)
          (twoArmInversePotential (Env := Env) eta horizon) := by
  let value := fun n =>
    integral (twoArmTrajectoryMeasure prior eta environment)
      (twoArmInversePotential (Env := Env) eta n)
  let failure := fun n =>
    integral (twoArmTrajectoryMeasure prior eta environment)
      (fun sample => twoArmFailureMass (Env := Env) eta n sample ^ 2)
  apply twoArmScalarInverseTelescope value failure
    (2 * eta * (Delta - eta * sourceC eta))
  intro n
  have hrec := twoArmInverseUnconditionalRecurrence
    prior eta Delta heta environment mean contract hgap n
  simpa [value, failure, mul_assoc, mul_comm, mul_left_comm] using hrec

theorem twoArmInverseFailureMassSqSum_le_initial_div
    {Env : Type v} [MeasurableSpace Env] [StandardBorelSpace Env]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (eta Delta : Real) (heta : 0 < eta)
    (environment : Thompson.MeasurableHistoryEnvironment Env (Fin 2) Real)
    (mean : Fin 2 -> Real)
    (contract : TwoArmBoundedFixedMeanEnvironmentContract environment mean)
    (hgap : mean 0 - mean 1 = Delta)
    (hmargin : eta * sourceC eta < Delta) (horizon : Nat) :
    (Finset.range horizon).sum (fun n =>
        integral (twoArmTrajectoryMeasure prior eta environment)
          (fun sample => twoArmFailureMass
            (Env := Env) eta n sample ^ 2)) <=
      integral (twoArmTrajectoryMeasure prior eta environment)
          (twoArmInversePotential (Env := Env) eta 0) /
        (2 * eta * (Delta - eta * sourceC eta)) := by
  have hcoefficient : 0 < 2 * eta * (Delta - eta * sourceC eta) := by
    have hmargin' : 0 < Delta - eta * sourceC eta := sub_pos.mpr hmargin
    positivity
  apply (le_div_iff₀ hcoefficient).2
  have htelescope := twoArmInverseFailureMassSqTelescope
    prior eta Delta heta.le environment mean contract hgap horizon
  have hterminal : 0 <=
      integral (twoArmTrajectoryMeasure prior eta environment)
        (twoArmInversePotential (Env := Env) eta horizon) := by
    apply integral_nonneg
    intro sample
    exact Real.exp_nonneg _
  nlinarith

/-! Initial-pair marginal bridge, needed to include source round `t = 1`. -/

def twoArmInitialForwardPotential (eta : Real)
    (pair : Fin 2 × Real) : Real :=
  Real.exp (2 * eta *
    sourceIncrement (fun _ : Fin 2 => (1 : Real) / 2)
      pair.2 pair.1 0)

def twoArmInitialInversePotential (eta : Real)
    (pair : Fin 2 × Real) : Real :=
  Real.exp (-2 * eta *
    sourceIncrement (fun _ : Fin 2 => (1 : Real) / 2)
      pair.2 pair.1 0)

theorem measurable_twoArmInitialForwardPotential (eta : Real) :
    Measurable (twoArmInitialForwardPotential eta) := by
  have hincrement : Measurable
      (fun pair : Fin 2 × Real =>
        sourceIncrement (fun _ : Fin 2 => (1 : Real) / 2)
          pair.2 pair.1 0) :=
    measurable_sourceIncrement
      (fun _ : Fin 2 × Real => fun _ : Fin 2 => (1 : Real) / 2)
      (fun pair : Fin 2 × Real => pair.2)
      (fun pair : Fin 2 × Real => pair.1) 0
      measurable_const measurable_snd measurable_fst
  exact Real.measurable_exp.comp
    ((measurable_const.mul measurable_const).mul hincrement)

theorem measurable_twoArmInitialInversePotential (eta : Real) :
    Measurable (twoArmInitialInversePotential eta) := by
  have hincrement : Measurable
      (fun pair : Fin 2 × Real =>
        sourceIncrement (fun _ : Fin 2 => (1 : Real) / 2)
          pair.2 pair.1 0) :=
    measurable_sourceIncrement
      (fun _ : Fin 2 × Real => fun _ : Fin 2 => (1 : Real) / 2)
      (fun pair : Fin 2 × Real => pair.2)
      (fun pair : Fin 2 × Real => pair.1) 0
      measurable_const measurable_snd measurable_fst
  exact Real.measurable_exp.comp
    ((measurable_const.mul measurable_const).mul hincrement)

theorem twoArmForwardPotential_zero_eq_initial
    {Env : Type v} [MeasurableSpace Env]
    (eta : Real) (sample : Env × ((k : Nat) -> Fin 2 × Real)) :
    twoArmForwardPotential eta 0 sample =
      twoArmInitialForwardPotential eta (sample.2 0) := by
  have hprob : softmaxProbability (fun _ : Fin 2 => 0) =
      fun _ : Fin 2 => (1 : Real) / 2 := by
    funext selected
    exact softmaxProbability_zeroInitialization_finTwo selected
  simp only [twoArmForwardPotential,
    twoArmTrajectoryParameterZero, twoArmInitialForwardPotential,
    twoArmEnvironmentPrefix, historyParameter_zero, zero_add]
  rw [hprob]
  change Real.exp
      (2 * (eta * sourceIncrement (fun _ : Fin 2 => (1 : Real) / 2)
        (sample.2 0).2 (sample.2 0).1 0)) =
    Real.exp
      (2 * eta * sourceIncrement (fun _ : Fin 2 => (1 : Real) / 2)
        (sample.2 0).2 (sample.2 0).1 0)
  congr 1
  ring

theorem twoArmInversePotential_zero_eq_initial
    {Env : Type v} [MeasurableSpace Env]
    (eta : Real) (sample : Env × ((k : Nat) -> Fin 2 × Real)) :
    twoArmInversePotential eta 0 sample =
      twoArmInitialInversePotential eta (sample.2 0) := by
  have hprob : softmaxProbability (fun _ : Fin 2 => 0) =
      fun _ : Fin 2 => (1 : Real) / 2 := by
    funext selected
    exact softmaxProbability_zeroInitialization_finTwo selected
  simp only [twoArmInversePotential,
    twoArmTrajectoryParameterZero, twoArmInitialInversePotential,
    twoArmEnvironmentPrefix, historyParameter_zero, zero_add]
  rw [hprob]
  change Real.exp
      (-2 * (eta * sourceIncrement (fun _ : Fin 2 => (1 : Real) / 2)
        (sample.2 0).2 (sample.2 0).1 0)) =
    Real.exp
      (-2 * eta * sourceIncrement (fun _ : Fin 2 => (1 : Real) / 2)
        (sample.2 0).2 (sample.2 0).1 0)
  congr 1
  ring

theorem integral_twoArmForwardPotential_zero_kernel_eq_initial
    {Env : Type v} [MeasurableSpace Env]
    (eta : Real)
    (environment : Thompson.MeasurableHistoryEnvironment Env (Fin 2) Real)
    (env : Env) :
    integral (trajectoryKernel (fun _ : Fin 2 => 0) eta environment env)
        (fun trajectory =>
          twoArmForwardPotential eta 0 (env, trajectory)) =
      integral
        (Thompson.measurableEnvironmentInitialPairKernel
          (historyAlgorithm (fun _ : Fin 2 => 0) eta) environment env)
        (twoArmInitialForwardPotential eta) := by
  rw [show (fun trajectory =>
      twoArmForwardPotential eta 0 (env, trajectory)) =
        fun trajectory => twoArmInitialForwardPotential eta (trajectory 0) by
    funext trajectory
    exact twoArmForwardPotential_zero_eq_initial eta (env, trajectory)]
  calc
    integral (trajectoryKernel (fun _ : Fin 2 => 0) eta environment env)
        (fun trajectory => twoArmInitialForwardPotential eta (trajectory 0)) =
      integral
        (Measure.map (fun trajectory : (k : Nat) -> Fin 2 × Real => trajectory 0)
          (trajectoryKernel (fun _ : Fin 2 => 0) eta environment env))
        (twoArmInitialForwardPotential eta) := by
          symm
          exact integral_map (measurable_pi_apply 0).aemeasurable
            (measurable_twoArmInitialForwardPotential eta).aestronglyMeasurable
    _ = integral
        ((trajectoryKernel (fun _ : Fin 2 => 0) eta environment).map
          (fun trajectory => trajectory 0) env)
        (twoArmInitialForwardPotential eta) := by
          rw [Kernel.map_apply _ (measurable_pi_apply 0)]
    _ = _ := by
      rw [trajectoryKernel,
        Thompson.canonicalMeasurableEnvironmentTrajectoryKernel_map_eval_zero]

theorem integral_twoArmInversePotential_zero_kernel_eq_initial
    {Env : Type v} [MeasurableSpace Env]
    (eta : Real)
    (environment : Thompson.MeasurableHistoryEnvironment Env (Fin 2) Real)
    (env : Env) :
    integral (trajectoryKernel (fun _ : Fin 2 => 0) eta environment env)
        (fun trajectory =>
          twoArmInversePotential eta 0 (env, trajectory)) =
      integral
        (Thompson.measurableEnvironmentInitialPairKernel
          (historyAlgorithm (fun _ : Fin 2 => 0) eta) environment env)
        (twoArmInitialInversePotential eta) := by
  rw [show (fun trajectory =>
      twoArmInversePotential eta 0 (env, trajectory)) =
        fun trajectory => twoArmInitialInversePotential eta (trajectory 0) by
    funext trajectory
    exact twoArmInversePotential_zero_eq_initial eta (env, trajectory)]
  calc
    integral (trajectoryKernel (fun _ : Fin 2 => 0) eta environment env)
        (fun trajectory => twoArmInitialInversePotential eta (trajectory 0)) =
      integral
        (Measure.map (fun trajectory : (k : Nat) -> Fin 2 × Real => trajectory 0)
          (trajectoryKernel (fun _ : Fin 2 => 0) eta environment env))
        (twoArmInitialInversePotential eta) := by
          symm
          exact integral_map (measurable_pi_apply 0).aemeasurable
            (measurable_twoArmInitialInversePotential eta).aestronglyMeasurable
    _ = integral
        ((trajectoryKernel (fun _ : Fin 2 => 0) eta environment).map
          (fun trajectory => trajectory 0) env)
        (twoArmInitialInversePotential eta) := by
          rw [Kernel.map_apply _ (measurable_pi_apply 0)]
    _ = _ := by
      rw [trajectoryKernel,
        Thompson.canonicalMeasurableEnvironmentTrajectoryKernel_map_eval_zero]

theorem twoArmForwardInitialUnconditionalRecurrence
    {Env : Type v} [MeasurableSpace Env] [StandardBorelSpace Env]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (eta Delta : Real) (heta : 0 <= eta)
    (environment : Thompson.MeasurableHistoryEnvironment Env (Fin 2) Real)
    (mean : Fin 2 -> Real)
    (contract : TwoArmBoundedFixedMeanEnvironmentContract environment mean)
    (hgap : mean 0 - mean 1 = Delta) :
    integral (twoArmTrajectoryMeasure prior eta environment)
        (twoArmForwardPotential (Env := Env) eta 0) <=
      1 + (eta * Delta + eta ^ 2 * sourceC eta) / 2 := by
  let kernel := trajectoryKernel (fun _ : Fin 2 => 0) eta environment
  let potential := twoArmForwardPotential (Env := Env) eta 0
  have hpotential := integrable_twoArmForwardPotential
    prior eta environment mean contract 0
  change Integrable (fun sample => potential sample) (prior ⊗ₘ kernel) at hpotential
  have hinnerStrong : StronglyMeasurable
      (fun env => integral (kernel env)
        (fun trajectory => potential (env, trajectory))) := by
    exact (measurable_twoArmForwardPotential (Env := Env) eta 0).stronglyMeasurable
      |>.integral_kernel_prod_right'
  have hnorm :=
    (Measure.integrable_compProd_iff hpotential.1).mp hpotential |>.2
  have hinner : Integrable
      (fun env => integral (kernel env)
        (fun trajectory => potential (env, trajectory))) prior := by
    apply hnorm.mono' hinnerStrong.aestronglyMeasurable
    filter_upwards [] with env
    exact norm_integral_le_integral_norm _
  have hpoint (env : Env) :
      integral (kernel env)
          (fun trajectory => potential (env, trajectory)) <=
        1 + (eta * Delta + eta ^ 2 * sourceC eta) / 2 := by
    change integral
        (trajectoryKernel (fun _ : Fin 2 => 0) eta environment env)
          (fun trajectory =>
            twoArmForwardPotential eta 0 (env, trajectory)) <= _
    rw [integral_twoArmForwardPotential_zero_kernel_eq_initial]
    exact integral_twoArmInitialPairKernel_exp_forwardIncrement_le_of_contract
      eta Delta heta environment mean contract hgap env
  calc
    integral (twoArmTrajectoryMeasure prior eta environment)
        (twoArmForwardPotential (Env := Env) eta 0) =
      integral prior (fun env => integral (kernel env)
        (fun trajectory => potential (env, trajectory))) := by
          change integral (prior ⊗ₘ kernel)
              (fun sample => potential sample) = _
          exact Measure.integral_compProd hpotential
    _ <= integral prior
        (fun _ : Env => 1 + (eta * Delta + eta ^ 2 * sourceC eta) / 2) :=
      integral_mono hinner (integrable_const _) hpoint
    _ = 1 + (eta * Delta + eta ^ 2 * sourceC eta) / 2 := by
      rw [integral_const, probReal_univ]
      simp

theorem twoArmInverseInitialUnconditionalRecurrence
    {Env : Type v} [MeasurableSpace Env] [StandardBorelSpace Env]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (eta Delta : Real) (heta : 0 <= eta)
    (environment : Thompson.MeasurableHistoryEnvironment Env (Fin 2) Real)
    (mean : Fin 2 -> Real)
    (contract : TwoArmBoundedFixedMeanEnvironmentContract environment mean)
    (hgap : mean 0 - mean 1 = Delta) :
    integral (twoArmTrajectoryMeasure prior eta environment)
        (twoArmInversePotential (Env := Env) eta 0) <=
      1 - eta / 2 * (Delta - eta * sourceC eta) := by
  let kernel := trajectoryKernel (fun _ : Fin 2 => 0) eta environment
  let potential := twoArmInversePotential (Env := Env) eta 0
  have hpotential := integrable_twoArmInversePotential
    prior eta environment mean contract 0
  change Integrable (fun sample => potential sample) (prior ⊗ₘ kernel) at hpotential
  have hinnerStrong : StronglyMeasurable
      (fun env => integral (kernel env)
        (fun trajectory => potential (env, trajectory))) := by
    exact (measurable_twoArmInversePotential (Env := Env) eta 0).stronglyMeasurable
      |>.integral_kernel_prod_right'
  have hnorm :=
    (Measure.integrable_compProd_iff hpotential.1).mp hpotential |>.2
  have hinner : Integrable
      (fun env => integral (kernel env)
        (fun trajectory => potential (env, trajectory))) prior := by
    apply hnorm.mono' hinnerStrong.aestronglyMeasurable
    filter_upwards [] with env
    exact norm_integral_le_integral_norm _
  have hpoint (env : Env) :
      integral (kernel env)
          (fun trajectory => potential (env, trajectory)) <=
        1 - eta / 2 * (Delta - eta * sourceC eta) := by
    change integral
        (trajectoryKernel (fun _ : Fin 2 => 0) eta environment env)
          (fun trajectory =>
            twoArmInversePotential eta 0 (env, trajectory)) <= _
    rw [integral_twoArmInversePotential_zero_kernel_eq_initial]
    exact integral_twoArmInitialPairKernel_exp_inverseIncrement_le_of_contract
      eta Delta heta environment mean contract hgap env
  calc
    integral (twoArmTrajectoryMeasure prior eta environment)
        (twoArmInversePotential (Env := Env) eta 0) =
      integral prior (fun env => integral (kernel env)
        (fun trajectory => potential (env, trajectory))) := by
          change integral (prior ⊗ₘ kernel)
              (fun sample => potential sample) = _
          exact Measure.integral_compProd hpotential
    _ <= integral prior
        (fun _ : Env => 1 - eta / 2 * (Delta - eta * sourceC eta)) :=
      integral_mono hinner (integrable_const _) hpoint
    _ = 1 - eta / 2 * (Delta - eta * sourceC eta) := by
      rw [integral_const, probReal_univ]
      simp

theorem twoArmForwardFiniteIteration_from_source_initial
    {Env : Type v} [MeasurableSpace Env] [StandardBorelSpace Env]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (eta Delta : Real) (heta : 0 <= eta)
    (environment : Thompson.MeasurableHistoryEnvironment Env (Fin 2) Real)
    (mean : Fin 2 -> Real)
    (contract : TwoArmBoundedFixedMeanEnvironmentContract environment mean)
    (hgap : mean 0 - mean 1 = Delta) (tailHorizon : Nat) :
    integral (twoArmTrajectoryMeasure prior eta environment)
        (twoArmForwardPotential (Env := Env) eta tailHorizon) <=
      1 + (eta * Delta + eta ^ 2 * sourceC eta) / 2 +
        (Finset.range tailHorizon).sum (fun n =>
          2 * integral (twoArmTrajectoryMeasure prior eta environment)
              (fun sample => twoArmSuccessProbability
                (Env := Env) eta n sample ^ 2) *
            (eta * Delta + eta ^ 2 * sourceC eta)) := by
  have hiterate := twoArmForwardFiniteIteration
    prior eta Delta heta environment mean contract hgap tailHorizon
  have hinitial := twoArmForwardInitialUnconditionalRecurrence
    prior eta Delta heta environment mean contract hgap
  linarith

/-- The source round `t = 1` contributes exactly `(1 - 1/2)^2 = 1/4`;
the `tailHorizon` summands are source rounds `t = 2, ..., tailHorizon + 1`. -/
theorem twoArmFullFailureMassSqSum_le
    {Env : Type v} [MeasurableSpace Env] [StandardBorelSpace Env]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (eta Delta : Real) (heta : 0 < eta)
    (environment : Thompson.MeasurableHistoryEnvironment Env (Fin 2) Real)
    (mean : Fin 2 -> Real)
    (contract : TwoArmBoundedFixedMeanEnvironmentContract environment mean)
    (hgap : mean 0 - mean 1 = Delta)
    (hmargin : eta * sourceC eta < Delta) (tailHorizon : Nat) :
    (1 : Real) / 4 +
        (Finset.range tailHorizon).sum (fun n =>
          integral (twoArmTrajectoryMeasure prior eta environment)
            (fun sample => twoArmFailureMass
              (Env := Env) eta n sample ^ 2)) <=
      1 / (2 * eta * (Delta - eta * sourceC eta)) := by
  have hcoefficient : 0 < 2 * eta * (Delta - eta * sourceC eta) := by
    have hmargin' : 0 < Delta - eta * sourceC eta := sub_pos.mpr hmargin
    positivity
  apply (le_div_iff₀ hcoefficient).2
  have htelescope := twoArmInverseFailureMassSqTelescope
    prior eta Delta heta.le environment mean contract hgap tailHorizon
  have hinitial := twoArmInverseInitialUnconditionalRecurrence
    prior eta Delta heta.le environment mean contract hgap
  have hterminal : 0 <=
      integral (twoArmTrajectoryMeasure prior eta environment)
        (twoArmInversePotential (Env := Env) eta tailHorizon) := by
    apply integral_nonneg
    intro sample
    exact Real.exp_nonneg _
  nlinarith


end
end StochasticGradientBandit
end BanditRLProof
