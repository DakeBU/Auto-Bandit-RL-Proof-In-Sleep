import BanditRLProof.Algorithms.StochasticGradientBanditTwoArmUnconditionalRecurrence
import BanditRLProof.Algorithms.StochasticGradientBanditTwoArmFixedIID
import Mathlib.Analysis.Convex.Integral

/-!
# Two-arm stochastic-gradient bandit: source Theorem 1

This module closes Theorem 1 of Baudry, Johnson, Vary, Pike-Burke, and
Rebeschini, *Does Stochastic Gradient really succeed for Bandits?*
(NeurIPS 2025), for the paper's fixed two-arm IID reward model.

The route stays on the generated Algorithm-1 trajectory.  It proves the
Equation-(5) conditional-expectation tower, the exact expected-parameter
telescope, the forward-potential Jensen/log bound, the Equation-(7)
success/failure decomposition, and the bridge from generated probabilities to
the regret of the actually sampled actions.  The terminal
`twoArmFixedIIDDirac_theoremOne` uses a Dirac environment prior and maps Lean
`tailHorizon + 1` to the source horizon `T`, including the uniform first
action.  Its right-hand side and hypotheses retain the source constants,
`0 < Delta < 1`, and `eta * sourceC eta < Delta` exactly.

This module does not claim the paper's Theorems 2--4, a general-`K` endpoint,
or verification of the paper beyond this named theorem.
-/

namespace BanditRLProof
namespace StochasticGradientBandit

open MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory
noncomputable section
universe v

def twoArmTrajectorySourceIncrement
    {Env : Type v} [MeasurableSpace Env]
    (eta : Real) (n : Nat)
    (sample : Env × ((k : Nat) -> Fin 2 × Real)) : Real :=
  sourceIncrement
    (softmaxProbability
      (historyParameter (fun _ : Fin 2 => 0) eta n
        (twoArmEnvironmentPrefix n sample).2))
    (twoArmNextPair n sample).2 (twoArmNextPair n sample).1 0

theorem measurable_twoArmTrajectorySourceIncrement
    {Env : Type v} [MeasurableSpace Env]
    (eta : Real) (n : Nat) :
    Measurable (twoArmTrajectorySourceIncrement (Env := Env) eta n) := by
  let theta := fun sample : Env × ((k : Nat) -> Fin 2 × Real) =>
    historyParameter (fun _ : Fin 2 => 0) eta n
      (twoArmEnvironmentPrefix n sample).2
  have htheta (arm : Fin 2) : Measurable (fun sample => theta sample arm) :=
    (measurable_historyParameter (fun _ : Fin 2 => 0) eta n arm).comp
      (measurable_snd.comp (measurable_twoArmEnvironmentPrefix n))
  have hprob : Measurable
      (fun sample => softmaxProbability (theta sample) 0) :=
    measurable_softmaxProbability theta htheta 0
  simpa [twoArmTrajectorySourceIncrement, theta] using
    measurable_sourceIncrement
      (fun sample => softmaxProbability (theta sample))
      (fun sample => (twoArmNextPair n sample).2)
      (fun sample => (twoArmNextPair n sample).1) 0
      hprob (measurable_snd.comp (measurable_twoArmNextPair n))
      (measurable_fst.comp (measurable_twoArmNextPair n))

theorem integrable_twoArmTrajectorySourceIncrement
    {Env : Type v} [MeasurableSpace Env] [StandardBorelSpace Env]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (eta : Real)
    (environment : Thompson.MeasurableHistoryEnvironment Env (Fin 2) Real)
    (mean : Fin 2 -> Real)
    (contract : TwoArmBoundedFixedMeanEnvironmentContract environment mean)
    (n : Nat) :
    Integrable (twoArmTrajectorySourceIncrement (Env := Env) eta n)
      (twoArmTrajectoryMeasure prior eta environment) := by
  apply Integrable.of_bound
    (measurable_twoArmTrajectorySourceIncrement eta n).aestronglyMeasurable 1
  filter_upwards
      [twoArmTrajectoryMeasure_reward_succ_abs_le_one_ae
        prior eta environment mean contract n]
    with sample hreward
  rw [twoArmTrajectorySourceIncrement, Real.norm_eq_abs]
  exact (abs_sourceIncrement_softmax_le_abs_reward
    (historyParameter (fun _ : Fin 2 => 0) eta n
      (twoArmEnvironmentPrefix n sample).2)
    (twoArmNextPair n sample).2 (twoArmNextPair n sample).1 0).trans hreward

theorem twoArmTrajectorySourceIncrement_condExp_ae_eq_integral_condDistrib
    {Env : Type v} [MeasurableSpace Env] [StandardBorelSpace Env]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (eta : Real)
    (environment : Thompson.MeasurableHistoryEnvironment Env (Fin 2) Real)
    (mean : Fin 2 -> Real)
    (contract : TwoArmBoundedFixedMeanEnvironmentContract environment mean)
    (n : Nat) :
    (twoArmTrajectoryMeasure prior eta environment)[
      twoArmTrajectorySourceIncrement (Env := Env) eta n |
      twoArmPrefixSigma (Env := Env) n] =ᵐ[
        twoArmTrajectoryMeasure prior eta environment]
      fun sample : Env × ((k : Nat) -> Fin 2 × Real) =>
        integral
          (condDistrib (twoArmNextPair n) (twoArmEnvironmentPrefix n)
            (twoArmTrajectoryMeasure prior eta environment)
            (twoArmEnvironmentPrefix n sample))
          (fun pair : Fin 2 × Real =>
            sourceIncrement
              (softmaxProbability
                (historyParameter (fun _ : Fin 2 => 0) eta n
                  (twoArmEnvironmentPrefix n sample).2))
              pair.2 pair.1 0) := by
  let pairIncrement :=
    fun input :
        (Env × History.FinitePairHistory (Fin 2) Real n) ×
          (Fin 2 × Real) =>
      sourceIncrement
        (softmaxProbability
          (historyParameter (fun _ : Fin 2 => 0) eta n input.1.2))
        input.2.2 input.2.1 0
  have hpairIncrement : Measurable pairIncrement := by
    have htheta (arm : Fin 2) : Measurable
        (fun input :
            (Env × History.FinitePairHistory (Fin 2) Real n) ×
              (Fin 2 × Real) =>
          historyParameter (fun _ : Fin 2 => 0) eta n input.1.2 arm) :=
      (measurable_historyParameter (fun _ : Fin 2 => 0) eta n arm).comp
        (measurable_snd.comp measurable_fst)
    have hprob : Measurable (fun input :
        (Env × History.FinitePairHistory (Fin 2) Real n) ×
          (Fin 2 × Real) =>
      softmaxProbability
        (historyParameter (fun _ : Fin 2 => 0) eta n input.1.2) 0) :=
      measurable_softmaxProbability
        (fun input :
            (Env × History.FinitePairHistory (Fin 2) Real n) ×
              (Fin 2 × Real) =>
          historyParameter (fun _ : Fin 2 => 0) eta n input.1.2)
        htheta 0
    exact measurable_sourceIncrement
      (fun input :
          (Env × History.FinitePairHistory (Fin 2) Real n) ×
            (Fin 2 × Real) =>
        softmaxProbability
        (historyParameter (fun _ : Fin 2 => 0) eta n input.1.2))
      (fun input :
          (Env × History.FinitePairHistory (Fin 2) Real n) ×
            (Fin 2 × Real) => input.2.2)
      (fun input :
          (Env × History.FinitePairHistory (Fin 2) Real n) ×
            (Fin 2 × Real) => input.2.1) 0 hprob
      (measurable_snd.comp measurable_snd)
      (measurable_fst.comp measurable_snd)
  simpa [pairIncrement, twoArmTrajectorySourceIncrement,
      twoArmPrefixSigma] using
    (condExp_prod_ae_eq_integral_condDistrib
      (μ := twoArmTrajectoryMeasure prior eta environment)
      (f := pairIncrement)
      (measurable_twoArmEnvironmentPrefix (Env := Env) n)
      (measurable_twoArmNextPair (Env := Env) n).aemeasurable
      hpairIncrement.stronglyMeasurable
      (integrable_twoArmTrajectorySourceIncrement
        prior eta environment mean contract n))

theorem twoArmTrajectorySourceIncrement_condExp_ae_eq_successFailure
    {Env : Type v} [MeasurableSpace Env] [StandardBorelSpace Env]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (eta Delta : Real)
    (environment : Thompson.MeasurableHistoryEnvironment Env (Fin 2) Real)
    (mean : Fin 2 -> Real)
    (contract : TwoArmBoundedFixedMeanEnvironmentContract environment mean)
    (hgap : mean 0 - mean 1 = Delta)
    (n : Nat) :
    (twoArmTrajectoryMeasure prior eta environment)[
      twoArmTrajectorySourceIncrement (Env := Env) eta n |
      twoArmPrefixSigma (Env := Env) n] =ᵐ[
        twoArmTrajectoryMeasure prior eta environment]
      fun sample => Delta * twoArmSuccessProbability eta n sample *
        twoArmFailureMass eta n sample := by
  have hcond :=
    twoArmTrajectorySourceIncrement_condExp_ae_eq_integral_condDistrib
      prior eta environment mean contract n
  have hkernel := trajectoryMeasure_condDistrib_nextPair_given_environment_prefix
    prior (fun _ : Fin 2 => 0) eta environment n
  have hkernel' := MeasureTheory.ae_of_ae_map
    (measurable_twoArmEnvironmentPrefix (Env := Env) n).aemeasurable hkernel
  filter_upwards [hcond, hkernel'] with sample hcond hkernel
  have hkernelExact :
      condDistrib (twoArmNextPair n) (twoArmEnvironmentPrefix n)
          (twoArmTrajectoryMeasure prior eta environment)
          (twoArmEnvironmentPrefix n sample) =
        Thompson.measurableEnvironmentHistoryStepKernel
          (historyAlgorithm (fun _ : Fin 2 => 0) eta) environment n
          (twoArmEnvironmentPrefix n sample) := by
    simpa [twoArmNextPair, twoArmEnvironmentPrefix,
      twoArmTrajectoryMeasure] using hkernel
  rw [hcond, hkernelExact]
  have hEqFive :=
    integral_measurableEnvironmentHistoryStepKernel_sourceIncrement_eq_gapCoordinate
      (fun _ : Fin 2 => 0) eta environment n sample.1
      (twoArmEnvironmentPrefix n sample).2 mean
      (fun action => mean 0 - mean action) (mean 0) 0
      (integrable_measurableTwoArmHistoryStepKernel_sourceIncrement_of_contract
        (fun _ : Fin 2 => 0) eta environment mean contract n sample.1
        (twoArmEnvironmentPrefix n sample).2 0)
      (contract.successor_mean n sample.1
        (twoArmEnvironmentPrefix n sample).2)
      (fun _ => rfl)
  have hEqFiveExact :
      integral
          (Thompson.measurableEnvironmentHistoryStepKernel
            (historyAlgorithm (fun _ : Fin 2 => 0) eta) environment n
            (twoArmEnvironmentPrefix n sample))
          (fun pair : Fin 2 × Real =>
            sourceIncrement
              (softmaxProbability
                (historyParameter (fun _ : Fin 2 => 0) eta n
                  (twoArmEnvironmentPrefix n sample).2))
              pair.2 pair.1 0) =
        softmaxProbability
            (historyParameter (fun _ : Fin 2 => 0) eta n
              (twoArmEnvironmentPrefix n sample).2) 0 *
          (instantaneousGap
              (softmaxProbability
                (historyParameter (fun _ : Fin 2 => 0) eta n
                  (twoArmEnvironmentPrefix n sample).2))
              (fun action => mean 0 - mean action) -
            (mean 0 - mean 0)) := by
    simpa [twoArmEnvironmentPrefix] using hEqFive
  rw [hEqFiveExact]
  simp only [instantaneousGap, Fin.sum_univ_two]
  rw [softmaxProbability_one_eq_one_sub_zero]
  simp only [sub_self, mul_zero, zero_add, twoArmSuccessProbability,
    twoArmFailureMass]
  rw [← hgap]
  ring

theorem twoArmTrajectoryParameterZero_succ
    {Env : Type v} [MeasurableSpace Env]
    (eta : Real) (n : Nat)
    (sample : Env × ((k : Nat) -> Fin 2 × Real)) :
    twoArmTrajectoryParameterZero eta (n + 1) sample =
      twoArmTrajectoryParameterZero eta n sample +
        eta * twoArmTrajectorySourceIncrement eta n sample := by
  rw [twoArmTrajectoryParameterZero, historyParameter_succ]
  have hprevious :
      Exp3.previousPairHistory (Preorder.frestrictLe (n + 1) sample.2) =
        Preorder.frestrictLe n sample.2 := by
    funext i
    rfl
  simp only [twoArmEnvironmentPrefix]
  rw [hprevious]
  rfl

theorem integrable_twoArmTrajectoryParameterZero
    {Env : Type v} [MeasurableSpace Env] [StandardBorelSpace Env]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (eta : Real)
    (environment : Thompson.MeasurableHistoryEnvironment Env (Fin 2) Real)
    (mean : Fin 2 -> Real)
    (contract : TwoArmBoundedFixedMeanEnvironmentContract environment mean)
    (n : Nat) :
    Integrable (twoArmTrajectoryParameterZero (Env := Env) eta n)
      (twoArmTrajectoryMeasure prior eta environment) := by
  apply Integrable.of_bound
    (measurable_twoArmTrajectoryParameterZero eta n).aestronglyMeasurable
    (((n + 1 : Nat) : Real) * |eta|)
  filter_upwards
      [twoArmTrajectoryMeasure_prefix_rewards_abs_le_one_ae
        prior eta environment mean contract n]
    with sample hreward
  rw [twoArmTrajectoryParameterZero, Real.norm_eq_abs]
  exact abs_historyParameter_zeroInitialization_le eta n
    (twoArmEnvironmentPrefix n sample).2 0 hreward

theorem integral_twoArmTrajectorySourceIncrement_eq_successFailure
    {Env : Type v} [MeasurableSpace Env] [StandardBorelSpace Env]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (eta Delta : Real)
    (environment : Thompson.MeasurableHistoryEnvironment Env (Fin 2) Real)
    (mean : Fin 2 -> Real)
    (contract : TwoArmBoundedFixedMeanEnvironmentContract environment mean)
    (hgap : mean 0 - mean 1 = Delta)
    (n : Nat) :
    integral (twoArmTrajectoryMeasure prior eta environment)
        (twoArmTrajectorySourceIncrement (Env := Env) eta n) =
      integral (twoArmTrajectoryMeasure prior eta environment)
        (fun sample => Delta * twoArmSuccessProbability eta n sample *
          twoArmFailureMass eta n sample) := by
  let mu := twoArmTrajectoryMeasure prior eta environment
  have htower := integral_condExp
    (m := twoArmPrefixSigma (Env := Env) n)
    (μ := mu)
    (f := twoArmTrajectorySourceIncrement (Env := Env) eta n)
    ((twoArmPrefixFiltration (Env := Env)).le n)
  have hcond :=
    twoArmTrajectorySourceIncrement_condExp_ae_eq_successFailure
      prior eta Delta environment mean contract hgap n
  calc
    integral mu (twoArmTrajectorySourceIncrement eta n) =
        integral mu
          (mu[twoArmTrajectorySourceIncrement eta n |
            twoArmPrefixSigma (Env := Env) n]) := htower.symm
    _ = integral mu (fun sample =>
          Delta * twoArmSuccessProbability eta n sample *
            twoArmFailureMass eta n sample) := integral_congr_ae hcond

theorem integral_twoArmTrajectoryParameterZero_succ
    {Env : Type v} [MeasurableSpace Env] [StandardBorelSpace Env]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (eta Delta : Real)
    (environment : Thompson.MeasurableHistoryEnvironment Env (Fin 2) Real)
    (mean : Fin 2 -> Real)
    (contract : TwoArmBoundedFixedMeanEnvironmentContract environment mean)
    (hgap : mean 0 - mean 1 = Delta)
    (n : Nat) :
    integral (twoArmTrajectoryMeasure prior eta environment)
        (twoArmTrajectoryParameterZero (Env := Env) eta (n + 1)) =
      integral (twoArmTrajectoryMeasure prior eta environment)
          (twoArmTrajectoryParameterZero (Env := Env) eta n) +
        eta * integral (twoArmTrajectoryMeasure prior eta environment)
          (fun sample => Delta * twoArmSuccessProbability eta n sample *
            twoArmFailureMass eta n sample) := by
  let mu := twoArmTrajectoryMeasure prior eta environment
  have htheta := integrable_twoArmTrajectoryParameterZero
    prior eta environment mean contract n
  have hincrement := integrable_twoArmTrajectorySourceIncrement
    prior eta environment mean contract n
  calc
    integral mu (twoArmTrajectoryParameterZero eta (n + 1)) =
        integral mu (fun sample =>
          twoArmTrajectoryParameterZero eta n sample +
            eta * twoArmTrajectorySourceIncrement eta n sample) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun sample =>
        twoArmTrajectoryParameterZero_succ eta n sample
    _ = integral mu (twoArmTrajectoryParameterZero eta n) +
        eta * integral mu (twoArmTrajectorySourceIncrement eta n) := by
      rw [integral_add htheta (hincrement.const_mul eta),
        integral_const_mul]
    _ = integral mu (twoArmTrajectoryParameterZero eta n) +
        eta * integral mu (fun sample =>
          Delta * twoArmSuccessProbability eta n sample *
            twoArmFailureMass eta n sample) := by
      rw [integral_twoArmTrajectorySourceIncrement_eq_successFailure
        prior eta Delta environment mean contract hgap n]

def twoArmInitialSourceIncrement
    (pair : Fin 2 × Real) : Real :=
  sourceIncrement (fun _ : Fin 2 => (1 : Real) / 2)
    pair.2 pair.1 0

theorem measurable_twoArmInitialSourceIncrement :
    Measurable twoArmInitialSourceIncrement := by
  exact measurable_sourceIncrement
    (fun _ : Fin 2 × Real => fun _ : Fin 2 => (1 : Real) / 2)
    Prod.snd Prod.fst 0 measurable_const measurable_snd measurable_fst

theorem integral_twoArmInitialSourceIncrement_eq_quarter_gap
    {Env : Type v} [MeasurableSpace Env]
    (eta Delta : Real)
    (environment : Thompson.MeasurableHistoryEnvironment Env (Fin 2) Real)
    (env : Env) (mean : Fin 2 -> Real)
    (contract : TwoArmBoundedFixedMeanEnvironmentContract environment mean)
    (hgap : mean 0 - mean 1 = Delta) :
    integral
        (Thompson.measurableEnvironmentInitialPairKernel
          (historyAlgorithm (fun _ : Fin 2 => 0) eta) environment env)
        twoArmInitialSourceIncrement = Delta / 4 := by
  have hprob : softmaxProbability (fun _ : Fin 2 => 0) =
      fun _ : Fin 2 => (1 : Real) / 2 := by
    funext selected
    exact softmaxProbability_zeroInitialization_finTwo selected
  have hEqFive :=
    integral_measurableEnvironmentInitialPairKernel_sourceIncrement_eq_expectedSourceIncrement
      (fun _ : Fin 2 => 0) eta environment env mean 0
      (integrable_measurableTwoArmInitialPairKernel_sourceIncrement_of_contract
        (fun _ : Fin 2 => 0) eta environment mean contract env 0)
      (contract.initial_mean env)
  rw [hprob] at hEqFive
  have hEqFiveExact : integral
        (Thompson.measurableEnvironmentInitialPairKernel
          (historyAlgorithm (fun _ : Fin 2 => 0) eta) environment env)
        twoArmInitialSourceIncrement =
      expectedSourceIncrement (fun _ : Fin 2 => (1 : Real) / 2) mean 0 := by
    change integral
        (Thompson.measurableEnvironmentInitialPairKernel
          (historyAlgorithm (fun _ : Fin 2 => 0) eta) environment env)
        (fun pair : Fin 2 × Real =>
          sourceIncrement (fun _ : Fin 2 => (1 : Real) / 2)
            pair.2 pair.1 0) = _
    exact hEqFive
  rw [hEqFiveExact]
  rw [expectedSourceIncrement_eq_gradientCoordinate]
  simp only [policyValue, Fin.sum_univ_two]
  rw [← hgap]
  ring

theorem integral_twoArmTrajectoryParameterZero_zero
    {Env : Type v} [MeasurableSpace Env] [StandardBorelSpace Env]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (eta Delta : Real)
    (environment : Thompson.MeasurableHistoryEnvironment Env (Fin 2) Real)
    (mean : Fin 2 -> Real)
    (contract : TwoArmBoundedFixedMeanEnvironmentContract environment mean)
    (hgap : mean 0 - mean 1 = Delta) :
    integral (twoArmTrajectoryMeasure prior eta environment)
        (twoArmTrajectoryParameterZero (Env := Env) eta 0) =
      eta * Delta / 4 := by
  let kernel := trajectoryKernel (fun _ : Fin 2 => 0) eta environment
  let parameter := twoArmTrajectoryParameterZero (Env := Env) eta 0
  have hparameter := integrable_twoArmTrajectoryParameterZero
    prior eta environment mean contract 0
  change Integrable (fun sample => parameter sample) (prior ⊗ₘ kernel) at hparameter
  have hinnerStrong : StronglyMeasurable
      (fun env => integral (kernel env)
        (fun trajectory => parameter (env, trajectory))) := by
    exact (measurable_twoArmTrajectoryParameterZero (Env := Env) eta 0).stronglyMeasurable
      |>.integral_kernel_prod_right'
  have hnorm :=
    (Measure.integrable_compProd_iff hparameter.1).mp hparameter |>.2
  have hinner : Integrable
      (fun env => integral (kernel env)
        (fun trajectory => parameter (env, trajectory))) prior := by
    apply hnorm.mono' hinnerStrong.aestronglyMeasurable
    filter_upwards [] with env
    exact norm_integral_le_integral_norm _
  have hpoint (env : Env) :
      integral (kernel env)
          (fun trajectory => parameter (env, trajectory)) =
        eta * Delta / 4 := by
    have hparameterPoint :
        (fun trajectory => parameter (env, trajectory)) =
          fun trajectory => eta * twoArmInitialSourceIncrement (trajectory 0) := by
      funext trajectory
      have hprob : softmaxProbability (fun _ : Fin 2 => 0) =
          fun _ : Fin 2 => (1 : Real) / 2 := by
        funext selected
        exact softmaxProbability_zeroInitialization_finTwo selected
      simp only [parameter, twoArmTrajectoryParameterZero,
        twoArmEnvironmentPrefix, historyParameter_zero, zero_add]
      rw [hprob]
      rfl
    rw [hparameterPoint, integral_const_mul]
    have hintegral :
        integral (kernel env)
            (fun trajectory => twoArmInitialSourceIncrement (trajectory 0)) =
          integral
            (Thompson.measurableEnvironmentInitialPairKernel
              (historyAlgorithm (fun _ : Fin 2 => 0) eta) environment env)
            twoArmInitialSourceIncrement := by
      calc
        integral (trajectoryKernel (fun _ : Fin 2 => 0) eta environment env)
            (fun trajectory => twoArmInitialSourceIncrement (trajectory 0)) =
          integral
            (Measure.map
              (fun trajectory : (k : Nat) -> Fin 2 × Real => trajectory 0)
              (trajectoryKernel (fun _ : Fin 2 => 0) eta environment env))
            twoArmInitialSourceIncrement := by
                symm
                exact integral_map (measurable_pi_apply 0).aemeasurable
                  measurable_twoArmInitialSourceIncrement.aestronglyMeasurable
        _ = integral
            ((trajectoryKernel (fun _ : Fin 2 => 0) eta environment).map
              (fun trajectory => trajectory 0) env)
            twoArmInitialSourceIncrement := by
              rw [Kernel.map_apply _ (measurable_pi_apply 0)]
        _ = _ := by
          rw [trajectoryKernel,
            Thompson.canonicalMeasurableEnvironmentTrajectoryKernel_map_eval_zero]
    rw [hintegral,
      integral_twoArmInitialSourceIncrement_eq_quarter_gap
        eta Delta environment env mean contract hgap]
    ring
  change integral (prior ⊗ₘ kernel)
      (fun sample => parameter sample) = eta * Delta / 4
  calc
    integral (prior ⊗ₘ kernel) (fun sample => parameter sample) =
      integral prior (fun env => integral (kernel env)
        (fun trajectory => parameter (env, trajectory))) := by
          exact Measure.integral_compProd hparameter
    _ = integral prior (fun _ : Env => eta * Delta / 4) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hpoint
    _ = eta * Delta / 4 := by
      rw [integral_const, probReal_univ]
      simp

theorem integral_twoArmTrajectoryParameterZero_eq_successFailureSum
    {Env : Type v} [MeasurableSpace Env] [StandardBorelSpace Env]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (eta Delta : Real)
    (environment : Thompson.MeasurableHistoryEnvironment Env (Fin 2) Real)
    (mean : Fin 2 -> Real)
    (contract : TwoArmBoundedFixedMeanEnvironmentContract environment mean)
    (hgap : mean 0 - mean 1 = Delta)
    (tailHorizon : Nat) :
    integral (twoArmTrajectoryMeasure prior eta environment)
        (twoArmTrajectoryParameterZero (Env := Env) eta tailHorizon) =
      eta * Delta *
        ((1 : Real) / 4 +
          (Finset.range tailHorizon).sum (fun n =>
            integral (twoArmTrajectoryMeasure prior eta environment)
              (fun sample => twoArmSuccessProbability eta n sample *
                twoArmFailureMass eta n sample))) := by
  induction tailHorizon with
  | zero =>
      rw [integral_twoArmTrajectoryParameterZero_zero
        prior eta Delta environment mean contract hgap]
      simp
      ring
  | succ n ih =>
      rw [integral_twoArmTrajectoryParameterZero_succ
        prior eta Delta environment mean contract hgap n, ih,
        Finset.sum_range_succ]
      have hfactor :
          integral (twoArmTrajectoryMeasure prior eta environment)
              (fun sample => Delta * twoArmSuccessProbability eta n sample *
                twoArmFailureMass eta n sample) =
            Delta * integral (twoArmTrajectoryMeasure prior eta environment)
              (fun sample => twoArmSuccessProbability eta n sample *
                twoArmFailureMass eta n sample) := by
        rw [show (fun sample =>
            Delta * twoArmSuccessProbability eta n sample *
              twoArmFailureMass eta n sample) =
          fun sample => Delta *
            (twoArmSuccessProbability eta n sample *
              twoArmFailureMass eta n sample) by
            funext sample
            ring]
        rw [integral_const_mul]
      rw [hfactor]
      ring

theorem measurable_twoArmSuccessFailureMass
    {Env : Type v} [MeasurableSpace Env]
    (eta : Real) (n : Nat) :
    Measurable (fun sample : Env × ((k : Nat) -> Fin 2 × Real) =>
      twoArmSuccessProbability eta n sample *
        twoArmFailureMass eta n sample) :=
  (measurable_twoArmSuccessProbability eta n).mul
    (measurable_twoArmFailureMass eta n)

theorem integrable_twoArmSuccessFailureMass
    {Env : Type v} [MeasurableSpace Env] [StandardBorelSpace Env]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (eta : Real)
    (environment : Thompson.MeasurableHistoryEnvironment Env (Fin 2) Real)
    (n : Nat) :
    Integrable (fun sample =>
      twoArmSuccessProbability (Env := Env) eta n sample *
        twoArmFailureMass eta n sample)
      (twoArmTrajectoryMeasure prior eta environment) := by
  apply Integrable.of_bound
    (measurable_twoArmSuccessFailureMass (Env := Env) eta n).aestronglyMeasurable 1
  filter_upwards [] with sample
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · have hp0 : 0 <= twoArmSuccessProbability (Env := Env) eta n sample :=
      softmaxProbability_nonneg _ 0
    have hp1 : twoArmSuccessProbability (Env := Env) eta n sample <= 1 :=
      softmaxProbability_le_one _ 0
    change twoArmSuccessProbability (Env := Env) eta n sample *
        (1 - twoArmSuccessProbability eta n sample) <= 1
    nlinarith
  · exact mul_nonneg (softmaxProbability_nonneg _ 0)
      (sub_nonneg.mpr (softmaxProbability_le_one _ 0))

theorem integral_twoArmFailureMass_eq_successFailure_add_sq
    {Env : Type v} [MeasurableSpace Env] [StandardBorelSpace Env]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (eta : Real)
    (environment : Thompson.MeasurableHistoryEnvironment Env (Fin 2) Real)
    (n : Nat) :
    integral (twoArmTrajectoryMeasure prior eta environment)
        (fun sample => twoArmFailureMass (Env := Env) eta n sample) =
      integral (twoArmTrajectoryMeasure prior eta environment)
          (fun sample => twoArmSuccessProbability eta n sample *
            twoArmFailureMass eta n sample) +
        integral (twoArmTrajectoryMeasure prior eta environment)
          (fun sample => twoArmFailureMass eta n sample ^ 2) := by
  let mu := twoArmTrajectoryMeasure prior eta environment
  have hsuccessFailure := integrable_twoArmSuccessFailureMass
    prior eta environment n
  have hfailureSq := integrable_twoArmFailureMass_sq
    prior eta environment n
  calc
    integral mu (fun sample => twoArmFailureMass eta n sample) =
        integral mu (fun sample =>
          twoArmSuccessProbability eta n sample *
              twoArmFailureMass eta n sample +
            twoArmFailureMass eta n sample ^ 2) := by
      apply integral_congr_ae
      filter_upwards [] with sample
      exact failureMass_eq_successFailure_add_sq
        (twoArmSuccessProbability eta n sample)
    _ = _ := integral_add hsuccessFailure hfailureSq

/-- Expected pseudo-regret for source rounds `1, ..., tailHorizon + 1`.
The first round is uniform, and Lean tail index `n` is source round `n + 2`. -/
def twoArmGeneratedExpectedPseudoRegret
    {Env : Type v} [MeasurableSpace Env]
    (prior : Measure Env) (eta Delta : Real)
    (environment : Thompson.MeasurableHistoryEnvironment Env (Fin 2) Real)
    (tailHorizon : Nat) : Real :=
  Delta * ((1 : Real) / 2 +
    (Finset.range tailHorizon).sum (fun n =>
      integral (twoArmTrajectoryMeasure prior eta environment)
        (fun sample => twoArmFailureMass eta n sample)))

theorem twoArmGeneratedExpectedPseudoRegret_eq_parameter_add_failureSq
    {Env : Type v} [MeasurableSpace Env] [StandardBorelSpace Env]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (eta Delta : Real) (heta : 0 < eta)
    (environment : Thompson.MeasurableHistoryEnvironment Env (Fin 2) Real)
    (mean : Fin 2 -> Real)
    (contract : TwoArmBoundedFixedMeanEnvironmentContract environment mean)
    (hgap : mean 0 - mean 1 = Delta)
    (tailHorizon : Nat) :
    twoArmGeneratedExpectedPseudoRegret prior eta Delta environment tailHorizon =
      integral (twoArmTrajectoryMeasure prior eta environment)
          (twoArmTrajectoryParameterZero (Env := Env) eta tailHorizon) / eta +
        Delta * ((1 : Real) / 4 +
          (Finset.range tailHorizon).sum (fun n =>
            integral (twoArmTrajectoryMeasure prior eta environment)
              (fun sample => twoArmFailureMass eta n sample ^ 2))) := by
  have hsplit :
      (Finset.range tailHorizon).sum (fun n =>
          integral (twoArmTrajectoryMeasure prior eta environment)
            (fun sample => twoArmFailureMass eta n sample)) =
        (Finset.range tailHorizon).sum (fun n =>
          integral (twoArmTrajectoryMeasure prior eta environment)
            (fun sample => twoArmSuccessProbability eta n sample *
              twoArmFailureMass eta n sample)) +
        (Finset.range tailHorizon).sum (fun n =>
          integral (twoArmTrajectoryMeasure prior eta environment)
            (fun sample => twoArmFailureMass eta n sample ^ 2)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _hn
    exact integral_twoArmFailureMass_eq_successFailure_add_sq
      prior eta environment n
  rw [twoArmGeneratedExpectedPseudoRegret,
    integral_twoArmTrajectoryParameterZero_eq_successFailureSum
      prior eta Delta environment mean contract hgap tailHorizon,
    hsplit]
  field_simp
  ring

theorem integral_twoArmTrajectoryParameterZero_le_half_log_forwardPotential
    {Env : Type v} [MeasurableSpace Env] [StandardBorelSpace Env]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (eta : Real)
    (environment : Thompson.MeasurableHistoryEnvironment Env (Fin 2) Real)
    (mean : Fin 2 -> Real)
    (contract : TwoArmBoundedFixedMeanEnvironmentContract environment mean)
    (tailHorizon : Nat) :
    integral (twoArmTrajectoryMeasure prior eta environment)
        (twoArmTrajectoryParameterZero (Env := Env) eta tailHorizon) <=
      Real.log
        (integral (twoArmTrajectoryMeasure prior eta environment)
          (twoArmForwardPotential (Env := Env) eta tailHorizon)) / 2 := by
  letI : IsProbabilityMeasure
      (twoArmTrajectoryMeasure prior eta environment) := by
    unfold twoArmTrajectoryMeasure
    infer_instance
  let mu := twoArmTrajectoryMeasure prior eta environment
  let parameter := twoArmTrajectoryParameterZero (Env := Env) eta tailHorizon
  let doubled := fun sample : Env × ((k : Nat) -> Fin 2 × Real) =>
    2 * parameter sample
  have hparameter := integrable_twoArmTrajectoryParameterZero
    prior eta environment mean contract tailHorizon
  have hdoubled : Integrable doubled mu := by
    simpa [doubled] using hparameter.const_mul 2
  have hexp : Integrable (Real.exp ∘ doubled) mu := by
    simpa [Function.comp_def, doubled, parameter, mu,
      twoArmForwardPotential] using
      (integrable_twoArmForwardPotential
        prior eta environment mean contract tailHorizon)
  have hjensen := convexOn_exp.map_integral_le
    Real.continuous_exp.continuousOn isClosed_univ
    (Filter.Eventually.of_forall fun _ => Set.mem_univ _)
    hdoubled hexp
  have hjensenExact :
      Real.exp (2 * integral mu parameter) <=
        integral mu (twoArmForwardPotential eta tailHorizon) := by
    simpa [doubled, Function.comp_def, parameter,
      twoArmForwardPotential, integral_const_mul] using hjensen
  have hpositive : 0 < integral mu
      (twoArmForwardPotential eta tailHorizon) :=
    (Real.exp_pos (2 * integral mu parameter)).trans_le hjensenExact
  have hlog : 2 * integral mu parameter <=
      Real.log (integral mu (twoArmForwardPotential eta tailHorizon)) :=
    (Real.le_log_iff_exp_le hpositive).2 hjensenExact
  change integral mu parameter <= _
  linarith

theorem integral_twoArmSuccessProbability_sq_le_one
    {Env : Type v} [MeasurableSpace Env] [StandardBorelSpace Env]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (eta : Real)
    (environment : Thompson.MeasurableHistoryEnvironment Env (Fin 2) Real)
    (n : Nat) :
    integral (twoArmTrajectoryMeasure prior eta environment)
        (fun sample => twoArmSuccessProbability (Env := Env) eta n sample ^ 2) <=
      1 := by
  letI : IsProbabilityMeasure
      (twoArmTrajectoryMeasure prior eta environment) := by
    unfold twoArmTrajectoryMeasure
    infer_instance
  have hintegrable := integrable_twoArmSuccessProbability_sq
    prior eta environment n
  calc
    integral (twoArmTrajectoryMeasure prior eta environment)
        (fun sample => twoArmSuccessProbability (Env := Env) eta n sample ^ 2) <=
      integral (twoArmTrajectoryMeasure prior eta environment)
        (fun _ => (1 : Real)) := by
      apply integral_mono hintegrable (integrable_const 1)
      intro sample
      have hp0 : 0 <= twoArmSuccessProbability (Env := Env) eta n sample :=
        softmaxProbability_nonneg _ 0
      have hp1 : twoArmSuccessProbability (Env := Env) eta n sample <= 1 :=
        softmaxProbability_le_one _ 0
      nlinarith
    _ = 1 := by
      rw [integral_const, probReal_univ]
      simp

theorem integral_twoArmForwardPotential_le_source_bound
    {Env : Type v} [MeasurableSpace Env] [StandardBorelSpace Env]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (eta Delta : Real) (heta : 0 < eta) (hDelta : 0 < Delta)
    (environment : Thompson.MeasurableHistoryEnvironment Env (Fin 2) Real)
    (mean : Fin 2 -> Real)
    (contract : TwoArmBoundedFixedMeanEnvironmentContract environment mean)
    (hgap : mean 0 - mean 1 = Delta)
    (hmargin : eta * sourceC eta < Delta)
    (tailHorizon : Nat) :
    integral (twoArmTrajectoryMeasure prior eta environment)
        (twoArmForwardPotential (Env := Env) eta tailHorizon) <=
      1 + 4 * eta * Delta * ((tailHorizon + 1 : Nat) : Real) := by
  let mu := twoArmTrajectoryMeasure prior eta environment
  let coefficient := eta * Delta + eta ^ 2 * sourceC eta
  have hcoefficient_nonneg : 0 <= coefficient := by
    have hC : 0 <= sourceC eta := sourceC_nonneg eta heta.le
    dsimp [coefficient]
    positivity
  have hcoefficient_le : coefficient <= 2 * eta * Delta := by
    have hscaled : eta ^ 2 * sourceC eta < eta * Delta := by
      have := mul_lt_mul_of_pos_left hmargin heta
      nlinarith
    dsimp [coefficient]
    linarith
  have hiterate := twoArmForwardFiniteIteration_from_source_initial
    prior eta Delta heta.le environment mean contract hgap tailHorizon
  have hterm :
      (Finset.range tailHorizon).sum (fun n =>
          2 * integral mu (fun sample =>
            twoArmSuccessProbability (Env := Env) eta n sample ^ 2) *
              coefficient) <=
        (Finset.range tailHorizon).sum (fun _ => 2 * coefficient) := by
    apply Finset.sum_le_sum
    intro n _hn
    have hp := integral_twoArmSuccessProbability_sq_le_one
      prior eta environment n
    have hproduct := mul_nonneg (sub_nonneg.mpr hp) hcoefficient_nonneg
    nlinarith
  have hfirst :
      integral mu (twoArmForwardPotential eta tailHorizon) <=
        1 + coefficient / 2 +
          (Finset.range tailHorizon).sum (fun n =>
            2 * integral mu (fun sample =>
              twoArmSuccessProbability (Env := Env) eta n sample ^ 2) *
                coefficient) := by
    simpa [mu, coefficient] using hiterate
  calc
    integral mu (twoArmForwardPotential eta tailHorizon) <=
        1 + coefficient / 2 +
          (Finset.range tailHorizon).sum (fun n =>
            2 * integral mu (fun sample =>
              twoArmSuccessProbability (Env := Env) eta n sample ^ 2) *
                coefficient) := hfirst
    _ <= 1 + coefficient / 2 +
        (Finset.range tailHorizon).sum (fun _ => 2 * coefficient) := by
      linarith
    _ = 1 + coefficient / 2 +
        (tailHorizon : Real) * (2 * coefficient) := by
      simp
    _ <= 1 + 4 * eta * Delta * ((tailHorizon + 1 : Nat) : Real) := by
      push_cast
      have htail : 0 <= (tailHorizon : Real) := Nat.cast_nonneg _
      nlinarith

theorem integral_twoArmTrajectoryParameterZero_le_source_log_bound
    {Env : Type v} [MeasurableSpace Env] [StandardBorelSpace Env]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (eta Delta : Real) (heta : 0 < eta) (hDelta : 0 < Delta)
    (environment : Thompson.MeasurableHistoryEnvironment Env (Fin 2) Real)
    (mean : Fin 2 -> Real)
    (contract : TwoArmBoundedFixedMeanEnvironmentContract environment mean)
    (hgap : mean 0 - mean 1 = Delta)
    (hmargin : eta * sourceC eta < Delta)
    (tailHorizon : Nat) :
    integral (twoArmTrajectoryMeasure prior eta environment)
        (twoArmTrajectoryParameterZero (Env := Env) eta tailHorizon) <=
      Real.log
        (1 + 4 * eta * Delta * ((tailHorizon + 1 : Nat) : Real)) / 2 := by
  have hjensen :=
    integral_twoArmTrajectoryParameterZero_le_half_log_forwardPotential
      prior eta environment mean contract tailHorizon
  have hmoment := integral_twoArmForwardPotential_le_source_bound
    prior eta Delta heta hDelta environment mean contract hgap hmargin tailHorizon
  have hmoment_pos : 0 < integral (twoArmTrajectoryMeasure prior eta environment)
      (twoArmForwardPotential (Env := Env) eta tailHorizon) := by
    have hpositive := Real.exp_pos
      (2 * integral (twoArmTrajectoryMeasure prior eta environment)
        (twoArmTrajectoryParameterZero (Env := Env) eta tailHorizon))
    letI : IsProbabilityMeasure
        (twoArmTrajectoryMeasure prior eta environment) := by
      unfold twoArmTrajectoryMeasure
      infer_instance
    have hjensenRaw := convexOn_exp.map_integral_le
      Real.continuous_exp.continuousOn isClosed_univ
      (Filter.Eventually.of_forall fun _ => Set.mem_univ _)
      ((integrable_twoArmTrajectoryParameterZero
        prior eta environment mean contract tailHorizon).const_mul 2)
      (by simpa [Function.comp_def, twoArmForwardPotential] using
        (integrable_twoArmForwardPotential
          prior eta environment mean contract tailHorizon))
    have : Real.exp
        (integral (twoArmTrajectoryMeasure prior eta environment)
          (fun sample => 2 * twoArmTrajectoryParameterZero eta tailHorizon sample)) <=
        integral (twoArmTrajectoryMeasure prior eta environment)
          (twoArmForwardPotential eta tailHorizon) := by
      simpa [Function.comp_def, twoArmForwardPotential] using hjensenRaw
    rw [integral_const_mul] at this
    exact hpositive.trans_le this
  have hsource_pos : 0 <
      1 + 4 * eta * Delta * ((tailHorizon + 1 : Nat) : Real) := by
    positivity
  have hlogmono : Real.log
      (integral (twoArmTrajectoryMeasure prior eta environment)
        (twoArmForwardPotential eta tailHorizon)) <=
      Real.log (1 + 4 * eta * Delta * ((tailHorizon + 1 : Nat) : Real)) :=
    Real.log_le_log hmoment_pos hmoment
  linarith

def twoArmActionGap (Delta : Real) (action : Fin 2) : Real :=
  if action = 0 then 0 else Delta

theorem measurable_twoArmActionGap (Delta : Real) :
    Measurable (twoArmActionGap Delta) := by
  fun_prop

theorem integral_twoArmInitialActionGap_eq_half
    {Env : Type v} [MeasurableSpace Env] [StandardBorelSpace Env]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (eta Delta : Real)
    (environment : Thompson.MeasurableHistoryEnvironment Env (Fin 2) Real) :
    integral (twoArmTrajectoryMeasure prior eta environment)
        (fun sample => twoArmActionGap Delta (sample.2 0).1) =
      Delta / 2 := by
  let mu := twoArmTrajectoryMeasure prior eta environment
  let history := fun sample : Env × ((k : Nat) -> Fin 2 × Real) => sample.1
  let action := fun sample : Env × ((k : Nat) -> Fin 2 × Real) =>
    (sample.2 0).1
  let prob := fun _ : Env => softmaxProbability (fun _ : Fin 2 => 0)
  let policy := Kernel.const Env
    (Exp3.finiteActionMeasure (Finset.univ : Finset (Fin 2))
      (softmaxProbability (fun _ : Fin 2 => 0)))
  let score := fun input : Env × Fin 2 => twoArmActionGap Delta input.2
  letI : IsProbabilityMeasure mu := by
    dsimp [mu, twoArmTrajectoryMeasure]
    infer_instance
  letI : IsProbabilityMeasure
      (Exp3.finiteActionMeasure (Finset.univ : Finset (Fin 2))
        (softmaxProbability (fun _ : Fin 2 => 0))) :=
    Exp3.finiteActionMeasure_isProbabilityMeasure _ _
      (softmaxFiniteActionDistribution (fun _ : Fin 2 => 0))
  letI : IsMarkovKernel policy := by
    dsimp [policy]
    infer_instance
  have hcond : condDistrib action history mu =ᵐ[mu.map history] policy := by
    simpa [mu, history, action, policy, twoArmTrajectoryMeasure] using
      (trajectoryMeasure_condDistrib_action_zero_given_environment
        prior (fun _ : Fin 2 => 0) eta environment)
  have hscore : Measurable score :=
    (measurable_twoArmActionGap Delta).comp measurable_snd
  have hscoreIntegrable : Integrable score (mu.map history ⊗ₘ policy) := by
    apply Integrable.of_bound hscore.aestronglyMeasurable |Delta|
    filter_upwards [] with input
    by_cases h : input.2 = 0 <;> simp [score, twoArmActionGap, h]
  have hformula :=
    Exp3.integral_historyAction_eq_integral_sum_of_condDistrib_ae_eq_finiteActionMeasure
      mu history measurable_fst action
      (measurable_fst.comp ((measurable_pi_apply 0).comp measurable_snd))
      (Finset.univ : Finset (Fin 2)) prob
      (fun _ => softmaxFiniteActionDistribution (fun _ : Fin 2 => 0))
      policy (Filter.Eventually.of_forall fun _ => rfl) hcond
      score hscore hscoreIntegrable
  have hsum : (fun env : Env =>
      (Finset.univ : Finset (Fin 2)).sum (fun candidate =>
        prob env candidate * score (env, candidate))) =
      fun _ => Delta / 2 := by
    funext env
    simp only [Fin.sum_univ_two, prob, score, twoArmActionGap,
      if_pos, Fin.isValue]
    norm_num [softmaxProbability, softmaxDenominator]
    ring
  rw [show (fun sample => twoArmActionGap Delta (sample.2 0).1) =
      fun sample => score (history sample, action sample) by rfl]
  rw [hformula]
  rw [hsum]
  letI : IsProbabilityMeasure (mu.map history) :=
    Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  rw [integral_const, probReal_univ]
  simp

theorem integral_twoArmSuccessorActionGap_eq_failureMass
    {Env : Type v} [MeasurableSpace Env] [StandardBorelSpace Env]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (eta Delta : Real)
    (environment : Thompson.MeasurableHistoryEnvironment Env (Fin 2) Real)
    (n : Nat) :
    integral (twoArmTrajectoryMeasure prior eta environment)
        (fun sample => twoArmActionGap Delta (sample.2 (n + 1)).1) =
      Delta * integral (twoArmTrajectoryMeasure prior eta environment)
        (fun sample => twoArmFailureMass (Env := Env) eta n sample) := by
  let mu := twoArmTrajectoryMeasure prior eta environment
  let history := fun sample : Env × ((k : Nat) -> Fin 2 × Real) =>
    Preorder.frestrictLe n sample.2
  let action := fun sample : Env × ((k : Nat) -> Fin 2 × Real) =>
    (sample.2 (n + 1)).1
  let prob := fun h : History.FinitePairHistory (Fin 2) Real n =>
    softmaxProbability (historyParameter (fun _ : Fin 2 => 0) eta n h)
  let policy := Exp3.finiteActionKernel (Finset.univ : Finset (Fin 2)) prob
    (historySoftmaxDistributionSource (fun _ : Fin 2 => 0) eta n)
  let score := fun input :
      History.FinitePairHistory (Fin 2) Real n × Fin 2 =>
    twoArmActionGap Delta input.2
  letI : IsProbabilityMeasure mu := by
    dsimp [mu, twoArmTrajectoryMeasure]
    infer_instance
  letI : IsMarkovKernel policy := by
    dsimp [policy]
    infer_instance
  have hpolicy : policy =ᵐ[mu.map history]
      fun h => Exp3.finiteActionMeasure (Finset.univ : Finset (Fin 2))
        (prob h) := by
    filter_upwards [] with h
    exact Exp3.finiteActionKernel_apply _ _ _ h
  have hcond : condDistrib action history mu =ᵐ[mu.map history] policy := by
    simpa [mu, history, action, policy, prob, twoArmTrajectoryMeasure] using
      (trajectoryMeasure_condDistrib_action
        prior (fun _ : Fin 2 => 0) eta environment n)
  have hscore : Measurable score :=
    (measurable_twoArmActionGap Delta).comp measurable_snd
  have hscoreIntegrable : Integrable score (mu.map history ⊗ₘ policy) := by
    apply Integrable.of_bound hscore.aestronglyMeasurable |Delta|
    filter_upwards [] with input
    by_cases h : input.2 = 0 <;> simp [score, twoArmActionGap, h]
  have hformula :=
    Exp3.integral_historyAction_eq_integral_sum_of_condDistrib_ae_eq_finiteActionMeasure
      mu history ((Preorder.measurable_frestrictLe n).comp measurable_snd)
      action (measurable_fst.comp
        ((measurable_pi_apply (n + 1)).comp measurable_snd))
      (Finset.univ : Finset (Fin 2)) prob
      (fun h => (historySoftmaxDistributionSource
        (fun _ : Fin 2 => 0) eta n).distribution h)
      policy hpolicy hcond score hscore hscoreIntegrable
  have hsum (h : History.FinitePairHistory (Fin 2) Real n) :
      (Finset.univ : Finset (Fin 2)).sum (fun candidate =>
        prob h candidate * score (h, candidate)) =
      Delta * (1 - prob h 0) := by
    simp only [Fin.sum_univ_two, prob, score, twoArmActionGap,
      if_pos, Fin.isValue]
    rw [if_neg (by decide : (1 : Fin 2) ≠ 0),
      softmaxProbability_one_eq_one_sub_zero]
    ring
  rw [show (fun sample => twoArmActionGap Delta (sample.2 (n + 1)).1) =
      fun sample => score (history sample, action sample) by rfl]
  rw [hformula]
  have hright :
      integral (mu.map history) (fun h => Delta * (1 - prob h 0)) =
        integral mu (fun sample =>
          Delta * twoArmFailureMass (Env := Env) eta n sample) := by
    have hfunc : AEStronglyMeasurable
        (fun h : History.FinitePairHistory (Fin 2) Real n =>
          Delta * (1 - prob h 0)) (mu.map history) :=
      (measurable_const.mul
        (measurable_const.sub
          (measurable_softmaxProbability
            (fun h => historyParameter (fun _ : Fin 2 => 0) eta n h)
            (measurable_historyParameter (fun _ : Fin 2 => 0) eta n) 0))).aestronglyMeasurable
    have hmap := integral_map
      (μ := mu) (φ := history)
      (f := fun h : History.FinitePairHistory (Fin 2) Real n =>
        Delta * (1 - prob h 0))
      ((Preorder.measurable_frestrictLe n).comp measurable_snd).aemeasurable
      hfunc
    simpa [history, prob, twoArmFailureMass,
      twoArmSuccessProbability] using hmap
  rw [show (fun h =>
      (Finset.univ : Finset (Fin 2)).sum (fun candidate =>
        prob h candidate * score (h, candidate))) =
      fun h => Delta * (1 - prob h 0) by
        funext h
        exact hsum h]
  rw [hright, integral_const_mul]

def twoArmSampledPseudoRegret
    {Env : Type v} (Delta : Real) (horizon : Nat)
    (sample : Env × ((k : Nat) -> Fin 2 × Real)) : Real :=
  (Finset.range horizon).sum (fun t =>
    twoArmActionGap Delta (sample.2 t).1)

theorem integral_twoArmSampledPseudoRegret_eq_generated
    {Env : Type v} [MeasurableSpace Env] [StandardBorelSpace Env]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (eta Delta : Real)
    (environment : Thompson.MeasurableHistoryEnvironment Env (Fin 2) Real)
    (tailHorizon : Nat) :
    integral (twoArmTrajectoryMeasure prior eta environment)
        (twoArmSampledPseudoRegret (Env := Env) Delta (tailHorizon + 1)) =
      twoArmGeneratedExpectedPseudoRegret
        prior eta Delta environment tailHorizon := by
  let mu := twoArmTrajectoryMeasure prior eta environment
  have hroundIntegrable (t : Nat) : Integrable
      (fun sample : Env × ((k : Nat) -> Fin 2 × Real) =>
        twoArmActionGap Delta (sample.2 t).1) mu := by
    have hmeas : Measurable (fun sample :
        Env × ((k : Nat) -> Fin 2 × Real) =>
      twoArmActionGap Delta (sample.2 t).1) :=
      (measurable_twoArmActionGap Delta).comp
        (measurable_fst.comp ((measurable_pi_apply t).comp measurable_snd))
    apply Integrable.of_bound hmeas.aestronglyMeasurable |Delta|
    filter_upwards [] with sample
    by_cases h : (sample.2 t).1 = 0 <;> simp [twoArmActionGap, h]
  change integral mu (fun sample =>
      (Finset.range (tailHorizon + 1)).sum (fun t =>
        twoArmActionGap Delta (sample.2 t).1)) = _
  rw [integral_finset_sum (Finset.range (tailHorizon + 1))
    (fun t _ht => hroundIntegrable t)]
  rw [Finset.sum_range_succ', integral_twoArmInitialActionGap_eq_half
    prior eta Delta environment]
  have htail :
      (Finset.range tailHorizon).sum (fun n =>
        integral mu (fun sample =>
          twoArmActionGap Delta (sample.2 (n + 1)).1)) =
        Delta * (Finset.range tailHorizon).sum (fun n =>
          integral mu (fun sample => twoArmFailureMass eta n sample)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _hn
    exact integral_twoArmSuccessorActionGap_eq_failureMass
      prior eta Delta environment n
  rw [htail]
  simp [twoArmGeneratedExpectedPseudoRegret]
  ring

theorem twoArmGeneratedExpectedPseudoRegret_le_sourceTheoremOne
    {Env : Type v} [MeasurableSpace Env] [StandardBorelSpace Env]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (eta Delta : Real) (heta : 0 < eta) (hDelta : 0 < Delta)
    (environment : Thompson.MeasurableHistoryEnvironment Env (Fin 2) Real)
    (mean : Fin 2 -> Real)
    (contract : TwoArmBoundedFixedMeanEnvironmentContract environment mean)
    (hgap : mean 0 - mean 1 = Delta)
    (hmargin : eta * sourceC eta < Delta)
    (tailHorizon : Nat) :
    twoArmGeneratedExpectedPseudoRegret
        prior eta Delta environment tailHorizon <=
      Real.log
          (1 + 4 * eta * Delta * ((tailHorizon + 1 : Nat) : Real)) /
          (2 * eta) +
        Delta / (2 * eta * (Delta - eta * sourceC eta)) := by
  have hdecomposition :=
    twoArmGeneratedExpectedPseudoRegret_eq_parameter_add_failureSq
      prior eta Delta heta environment mean contract hgap tailHorizon
  have hparameter :=
    integral_twoArmTrajectoryParameterZero_le_source_log_bound
      prior eta Delta heta hDelta environment mean contract hgap hmargin
        tailHorizon
  have hfailure := twoArmFullFailureMassSqSum_le
    prior eta Delta heta environment mean contract hgap hmargin tailHorizon
  rw [hdecomposition]
  calc
    integral (twoArmTrajectoryMeasure prior eta environment)
          (twoArmTrajectoryParameterZero (Env := Env) eta tailHorizon) / eta +
        Delta * ((1 : Real) / 4 +
          (Finset.range tailHorizon).sum (fun n =>
            integral (twoArmTrajectoryMeasure prior eta environment)
              (fun sample => twoArmFailureMass eta n sample ^ 2))) <=
      (Real.log
          (1 + 4 * eta * Delta * ((tailHorizon + 1 : Nat) : Real)) / 2) /
          eta +
        Delta * (1 / (2 * eta * (Delta - eta * sourceC eta))) := by
      apply add_le_add
      · exact (div_le_div_iff_of_pos_right heta).2 hparameter
      · exact mul_le_mul_of_nonneg_left hfailure hDelta.le
    _ = Real.log
          (1 + 4 * eta * Delta * ((tailHorizon + 1 : Nat) : Real)) /
          (2 * eta) +
        Delta / (2 * eta * (Delta - eta * sourceC eta)) := by
      have heta0 : eta ≠ 0 := ne_of_gt heta
      have hmargin0 : Delta - eta * sourceC eta ≠ 0 :=
        ne_of_gt (sub_pos.mpr hmargin)
      field_simp

theorem integral_twoArmSampledPseudoRegret_le_sourceTheoremOne
    {Env : Type v} [MeasurableSpace Env] [StandardBorelSpace Env]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (eta Delta : Real) (heta : 0 < eta) (hDelta : 0 < Delta)
    (environment : Thompson.MeasurableHistoryEnvironment Env (Fin 2) Real)
    (mean : Fin 2 -> Real)
    (contract : TwoArmBoundedFixedMeanEnvironmentContract environment mean)
    (hgap : mean 0 - mean 1 = Delta)
    (hmargin : eta * sourceC eta < Delta)
    (tailHorizon : Nat) :
    integral (twoArmTrajectoryMeasure prior eta environment)
        (twoArmSampledPseudoRegret (Env := Env) Delta (tailHorizon + 1)) <=
      Real.log
          (1 + 4 * eta * Delta * ((tailHorizon + 1 : Nat) : Real)) /
          (2 * eta) +
        Delta / (2 * eta * (Delta - eta * sourceC eta)) := by
  rw [integral_twoArmSampledPseudoRegret_eq_generated
    prior eta Delta environment tailHorizon]
  exact twoArmGeneratedExpectedPseudoRegret_le_sourceTheoremOne
    prior eta Delta heta hDelta environment mean contract hgap hmargin
      tailHorizon

/-- Source-faithful Theorem 1 of Baudry--Johnson--Vary--Pike-Burke--
Rebeschini (NeurIPS 2025), for a fixed pair of IID arm laws.  Lean horizon
`tailHorizon + 1` is source `T`, including the uniform first action. -/
theorem twoArmFixedIIDDirac_theoremOne
    (armLaw : Fin 2 -> Measure Real)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (mean : Fin 2 -> Real)
    (hbound : forall arm, ∀ᵐ reward ∂armLaw arm, |reward| <= 1)
    (hmean : forall arm, integral (armLaw arm) id = mean arm)
    (eta Delta : Real) (heta : 0 < eta)
    (hDelta : 0 < Delta) (_hDelta_lt_one : Delta < 1)
    (hgap : mean 0 - mean 1 = Delta)
    (hmargin : eta * sourceC eta < Delta)
    (tailHorizon : Nat) :
    integral
        (twoArmTrajectoryMeasure (Measure.dirac ()) eta
          (twoArmFixedIIDEnvironment armLaw hprob))
        (twoArmSampledPseudoRegret (Env := Unit) Delta
          (tailHorizon + 1)) <=
      Real.log
          (1 + 4 * eta * Delta * ((tailHorizon + 1 : Nat) : Real)) /
          (2 * eta) +
        Delta / (2 * eta * (Delta - eta * sourceC eta)) := by
  let environment := twoArmFixedIIDEnvironment armLaw hprob
  let contract := twoArmFixedIIDEnvironment_contract
    armLaw hprob mean hbound hmean
  exact integral_twoArmSampledPseudoRegret_le_sourceTheoremOne
    (Measure.dirac ()) eta Delta heta hDelta environment mean contract hgap
      hmargin tailHorizon

end
end StochasticGradientBandit
end BanditRLProof
