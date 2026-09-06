import BanditRLProof.Algorithms.StochasticGradientBanditTwoArmRecurrence

/-!
# Measurable-environment and trajectory interfaces for the two-arm recurrences

This module lifts the fixed-history recurrences to the jointly measurable
environment kernel used by the canonical SGB trajectory.  It also records one
uniform, source-faithful environment contract: every initial and successor
reward fiber is supported in `[-1,1]` almost everywhere and has the same fixed
arm mean, uniformly over environment values, times, and finite histories.

Process / filtration ledger:

* the ambient finite measure is the canonical measure
  `prior ⊗ₘ trajectoryKernel 0 eta environment` on an environment and an
  infinite action/reward trace; it is a probability measure only when the
  supplied `prior` is one;
* at successor index `n`, the conditioning statistic retains the environment
  and trace pairs `0,...,n`; its generated next pair is trace pair `n+1`;
* the retained history parameter is source `theta_{.,n+2}` and adding the
  next source update produces `theta_{.,n+3}`;
* the prefix statistic retains the latent environment as well as the observed
  pairs.  Thus the filtration below is an environment-revealed filtration for
  a general prior; it agrees with the fixed-instance source reading after
  specializing to a deterministic/Dirac environment;
* `trajectoryMeasure_condDistrib_nextPair_given_environment_prefix` identifies
  the regular conditional distribution of that next pair with the actual
  measurable history-step kernel;
* no independence or `Delta > eta * sourceC eta` premise is used.

The final trajectory declarations are conditional-distribution integral
bounds.  Mathlib's `condExp_prod_ae_eq_integral_condDistrib` would turn these
into function-valued conditional-expectation bounds after proving global
integrability of the successor exponential potential.  The current local
fiber bounds do not yet establish that path-level integrability over every
generated prefix.  This module does construct the nested prefix filtration
needed by `condExp_condExp_of_le`; global integrability of the two exponential
processes is the remaining conditional-expectation/tower blocker and is left
as a named downstream obligation rather than a hidden assumption.
-/

namespace BanditRLProof
namespace StochasticGradientBandit

open MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory

noncomputable section

universe v

/-- The forward successor exponential at a retained finite two-arm history. -/
def twoArmForwardSuccessorPotential (eta : Real) {n : Nat}
    (history : History.FinitePairHistory (Fin 2) Real n)
    (pair : Fin 2 × Real) : Real :=
  Real.exp
    (2 *
      (historyParameter (fun _ : Fin 2 => 0) eta n history 0 +
        eta * sourceIncrement
          (softmaxProbability
            (historyParameter (fun _ : Fin 2 => 0) eta n history))
          pair.2 pair.1 0))

/-- The inverse-odds successor exponential at the same time fence. -/
def twoArmInverseSuccessorPotential (eta : Real) {n : Nat}
    (history : History.FinitePairHistory (Fin 2) Real n)
    (pair : Fin 2 × Real) : Real :=
  Real.exp
    (-2 *
      (historyParameter (fun _ : Fin 2 => 0) eta n history 0 +
        eta * sourceIncrement
          (softmaxProbability
            (historyParameter (fun _ : Fin 2 => 0) eta n history))
          pair.2 pair.1 0))

/-- The additive right side of the forward conditional recurrence. -/
def twoArmForwardRecurrenceBound (eta Delta : Real) {n : Nat}
    (history : History.FinitePairHistory (Fin 2) Real n) : Real :=
  Real.exp
      (2 * historyParameter (fun _ : Fin 2 => 0) eta n history 0) +
    2 *
      softmaxProbability
          (historyParameter (fun _ : Fin 2 => 0) eta n history) 0 ^ 2 *
      (eta * Delta + eta ^ 2 * sourceC eta)

/-- The additive right side of the inverse conditional recurrence. -/
def twoArmInverseRecurrenceBound (eta Delta : Real) {n : Nat}
    (history : History.FinitePairHistory (Fin 2) Real n) : Real :=
  Real.exp
      (-2 * historyParameter (fun _ : Fin 2 => 0) eta n history 0) -
    2 * eta *
      (1 - softmaxProbability
          (historyParameter (fun _ : Fin 2 => 0) eta n history) 0) ^ 2 *
      (Delta - eta * sourceC eta)

theorem measurable_twoArmForwardSuccessorPotential (eta : Real) (n : Nat) :
    Measurable
      (fun input : History.FinitePairHistory (Fin 2) Real n ×
          (Fin 2 × Real) =>
        twoArmForwardSuccessorPotential eta input.1 input.2) := by
  let theta := fun input : History.FinitePairHistory (Fin 2) Real n ×
      (Fin 2 × Real) =>
    historyParameter (fun _ : Fin 2 => 0) eta n input.1
  have htheta (arm : Fin 2) : Measurable (fun input => theta input arm) :=
    (measurable_historyParameter (fun _ : Fin 2 => 0) eta n arm).comp
      measurable_fst
  have hprob : Measurable
      (fun input => softmaxProbability (theta input) 0) :=
    measurable_softmaxProbability theta htheta 0
  have hincrement : Measurable
      (fun input => sourceIncrement (softmaxProbability (theta input))
        input.2.2 input.2.1 0) :=
    measurable_sourceIncrement
      (fun input => softmaxProbability (theta input))
      (fun input => input.2.2) (fun input => input.2.1) 0 hprob
      (measurable_snd.comp measurable_snd)
      (measurable_fst.comp measurable_snd)
  have hexponent : Measurable
      (fun input => 2 * (theta input 0 + eta *
        sourceIncrement (softmaxProbability (theta input))
          input.2.2 input.2.1 0)) :=
    measurable_const.mul ((htheta 0).add (measurable_const.mul hincrement))
  simpa [twoArmForwardSuccessorPotential, theta] using
    Real.measurable_exp.comp hexponent

theorem measurable_twoArmInverseSuccessorPotential (eta : Real) (n : Nat) :
    Measurable
      (fun input : History.FinitePairHistory (Fin 2) Real n ×
          (Fin 2 × Real) =>
        twoArmInverseSuccessorPotential eta input.1 input.2) := by
  let theta := fun input : History.FinitePairHistory (Fin 2) Real n ×
      (Fin 2 × Real) =>
    historyParameter (fun _ : Fin 2 => 0) eta n input.1
  have htheta (arm : Fin 2) : Measurable (fun input => theta input arm) :=
    (measurable_historyParameter (fun _ : Fin 2 => 0) eta n arm).comp
      measurable_fst
  have hprob : Measurable
      (fun input => softmaxProbability (theta input) 0) :=
    measurable_softmaxProbability theta htheta 0
  have hincrement : Measurable
      (fun input => sourceIncrement (softmaxProbability (theta input))
        input.2.2 input.2.1 0) :=
    measurable_sourceIncrement
      (fun input => softmaxProbability (theta input))
      (fun input => input.2.2) (fun input => input.2.1) 0 hprob
      (measurable_snd.comp measurable_snd)
      (measurable_fst.comp measurable_snd)
  have hexponent : Measurable
      (fun input => -2 * (theta input 0 + eta *
        sourceIncrement (softmaxProbability (theta input))
          input.2.2 input.2.1 0)) :=
    measurable_const.mul ((htheta 0).add (measurable_const.mul hincrement))
  simpa [twoArmInverseSuccessorPotential, theta] using
    Real.measurable_exp.comp hexponent

theorem measurable_twoArmForwardRecurrenceBound
    (eta Delta : Real) (n : Nat) :
    Measurable
      (twoArmForwardRecurrenceBound eta Delta :
        History.FinitePairHistory (Fin 2) Real n -> Real) := by
  let theta := fun history : History.FinitePairHistory (Fin 2) Real n =>
    historyParameter (fun _ : Fin 2 => 0) eta n history
  have htheta (arm : Fin 2) : Measurable (fun history => theta history arm) :=
    measurable_historyParameter (fun _ : Fin 2 => 0) eta n arm
  have hprob : Measurable
      (fun history => softmaxProbability (theta history) 0) :=
    measurable_softmaxProbability theta htheta 0
  unfold twoArmForwardRecurrenceBound
  exact (Real.measurable_exp.comp (measurable_const.mul (htheta 0))).add
    ((measurable_const.mul (hprob.pow_const 2)).mul measurable_const)

theorem measurable_twoArmInverseRecurrenceBound
    (eta Delta : Real) (n : Nat) :
    Measurable
      (twoArmInverseRecurrenceBound eta Delta :
        History.FinitePairHistory (Fin 2) Real n -> Real) := by
  let theta := fun history : History.FinitePairHistory (Fin 2) Real n =>
    historyParameter (fun _ : Fin 2 => 0) eta n history
  have htheta (arm : Fin 2) : Measurable (fun history => theta history arm) :=
    measurable_historyParameter (fun _ : Fin 2 => 0) eta n arm
  have hprob : Measurable
      (fun history => softmaxProbability (theta history) 0) :=
    measurable_softmaxProbability theta htheta 0
  unfold twoArmInverseRecurrenceBound
  exact (Real.measurable_exp.comp (measurable_const.mul (htheta 0))).sub
    (((measurable_const.mul
      ((measurable_const.sub hprob).pow_const 2)).mul measurable_const))

/--
Uniform source model for the two-arm Theorem-1 route.  The same `mean` is used
at the initial pair and at every history-dependent successor reward law.  This
is a conditional fixed-mean contract, not an independence assertion.
-/
structure TwoArmBoundedFixedMeanEnvironmentContract
    {Env : Type v} [MeasurableSpace Env]
    (environment : Thompson.MeasurableHistoryEnvironment Env (Fin 2) Real)
    (mean : Fin 2 -> Real) : Prop where
  initial_reward_bound : forall env selected,
    ∀ᵐ reward ∂environment.initialFeedback (env, selected), |reward| <= 1
  initial_mean : forall env selected,
    integral (environment.initialFeedback (env, selected)) id = mean selected
  successor_reward_bound : forall n env
      (history : History.FinitePairHistory (Fin 2) Real n) selected,
    ∀ᵐ reward ∂environment.feedback n (env, (history, selected)),
      |reward| <= 1
  successor_mean : forall n env
      (history : History.FinitePairHistory (Fin 2) Real n) selected,
    integral (environment.feedback n (env, (history, selected))) id =
      mean selected

/-- Forward recurrence on the jointly measurable environment/history kernel. -/
theorem integral_measurableTwoArmHistoryStepKernel_forwardSuccessor_le
    {Env : Type v} [MeasurableSpace Env]
    (eta Delta : Real) (heta : 0 <= eta)
    (environment : Thompson.MeasurableHistoryEnvironment Env (Fin 2) Real)
    (n : Nat) (env : Env)
    (history : History.FinitePairHistory (Fin 2) Real n)
    (mean : Fin 2 -> Real)
    (hreward : forall selected,
      ∀ᵐ reward ∂environment.feedback n (env, (history, selected)),
        |reward| <= 1)
    (hmean : forall selected,
      integral (environment.feedback n (env, (history, selected))) id =
        mean selected)
    (hgap : mean 0 - mean 1 = Delta) :
    integral
        (Thompson.measurableEnvironmentHistoryStepKernel
          (historyAlgorithm (fun _ : Fin 2 => 0) eta) environment n
          (env, history))
        (twoArmForwardSuccessorPotential eta history) <=
      twoArmForwardRecurrenceBound eta Delta history := by
  rw [Thompson.measurableEnvironmentHistoryStepKernel_apply]
  apply integral_twoArmHistoryStepKernel_exp_forwardSuccessor_le_add_success_sq
    eta Delta heta (environment.at env) n history mean
  · intro selected
    simpa [Thompson.MeasurableHistoryEnvironment.at,
      ProbabilityTheory.Kernel.comap_apply] using hreward selected
  · intro selected
    simpa [Thompson.MeasurableHistoryEnvironment.at,
      ProbabilityTheory.Kernel.comap_apply] using hmean selected
  · exact hgap

/-- Inverse recurrence on the jointly measurable environment/history kernel. -/
theorem integral_measurableTwoArmHistoryStepKernel_inverseSuccessor_le
    {Env : Type v} [MeasurableSpace Env]
    (eta Delta : Real) (heta : 0 <= eta)
    (environment : Thompson.MeasurableHistoryEnvironment Env (Fin 2) Real)
    (n : Nat) (env : Env)
    (history : History.FinitePairHistory (Fin 2) Real n)
    (mean : Fin 2 -> Real)
    (hreward : forall selected,
      ∀ᵐ reward ∂environment.feedback n (env, (history, selected)),
        |reward| <= 1)
    (hmean : forall selected,
      integral (environment.feedback n (env, (history, selected))) id =
        mean selected)
    (hgap : mean 0 - mean 1 = Delta) :
    integral
        (Thompson.measurableEnvironmentHistoryStepKernel
          (historyAlgorithm (fun _ : Fin 2 => 0) eta) environment n
          (env, history))
        (twoArmInverseSuccessorPotential eta history) <=
      twoArmInverseRecurrenceBound eta Delta history := by
  rw [Thompson.measurableEnvironmentHistoryStepKernel_apply]
  apply integral_twoArmHistoryStepKernel_exp_inverseSuccessor_le_sub_failure_sq
    eta Delta heta (environment.at env) n history mean
  · intro selected
    simpa [Thompson.MeasurableHistoryEnvironment.at,
      ProbabilityTheory.Kernel.comap_apply] using hreward selected
  · intro selected
    simpa [Thompson.MeasurableHistoryEnvironment.at,
      ProbabilityTheory.Kernel.comap_apply] using hmean selected
  · exact hgap

/-- The uniform environment contract supplies the forward recurrence at every
environment value and retained history. -/
theorem integral_measurableTwoArmHistoryStepKernel_forwardSuccessor_le_of_contract
    {Env : Type v} [MeasurableSpace Env]
    (eta Delta : Real) (heta : 0 <= eta)
    (environment : Thompson.MeasurableHistoryEnvironment Env (Fin 2) Real)
    (mean : Fin 2 -> Real)
    (contract : TwoArmBoundedFixedMeanEnvironmentContract environment mean)
    (hgap : mean 0 - mean 1 = Delta)
    (n : Nat) (env : Env)
    (history : History.FinitePairHistory (Fin 2) Real n) :
    integral
        (Thompson.measurableEnvironmentHistoryStepKernel
          (historyAlgorithm (fun _ : Fin 2 => 0) eta) environment n
          (env, history))
        (twoArmForwardSuccessorPotential eta history) <=
      twoArmForwardRecurrenceBound eta Delta history := by
  exact integral_measurableTwoArmHistoryStepKernel_forwardSuccessor_le
    eta Delta heta environment n env history mean
      (contract.successor_reward_bound n env history)
      (contract.successor_mean n env history) hgap

/-- The same contract supplies the inverse recurrence at every successor. -/
theorem integral_measurableTwoArmHistoryStepKernel_inverseSuccessor_le_of_contract
    {Env : Type v} [MeasurableSpace Env]
    (eta Delta : Real) (heta : 0 <= eta)
    (environment : Thompson.MeasurableHistoryEnvironment Env (Fin 2) Real)
    (mean : Fin 2 -> Real)
    (contract : TwoArmBoundedFixedMeanEnvironmentContract environment mean)
    (hgap : mean 0 - mean 1 = Delta)
    (n : Nat) (env : Env)
    (history : History.FinitePairHistory (Fin 2) Real n) :
    integral
        (Thompson.measurableEnvironmentHistoryStepKernel
          (historyAlgorithm (fun _ : Fin 2 => 0) eta) environment n
          (env, history))
        (twoArmInverseSuccessorPotential eta history) <=
      twoArmInverseRecurrenceBound eta Delta history := by
  exact integral_measurableTwoArmHistoryStepKernel_inverseSuccessor_le
    eta Delta heta environment n env history mean
      (contract.successor_reward_bound n env history)
      (contract.successor_mean n env history) hgap

/-- Canonical two-arm trajectory measure under zero initialization. -/
def twoArmTrajectoryMeasure
    {Env : Type v} [MeasurableSpace Env]
    (prior : Measure Env) (eta : Real)
    (environment : Thompson.MeasurableHistoryEnvironment Env (Fin 2) Real) :
    Measure (Env × ((k : Nat) -> Fin 2 × Real)) :=
  prior ⊗ₘ trajectoryKernel (fun _ : Fin 2 => 0) eta environment

instance instTwoArmTrajectoryMeasureIsFinite
    {Env : Type v} [MeasurableSpace Env]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (eta : Real)
    (environment : Thompson.MeasurableHistoryEnvironment Env (Fin 2) Real) :
    IsFiniteMeasure (twoArmTrajectoryMeasure prior eta environment) := by
  unfold twoArmTrajectoryMeasure
  infer_instance

/-- The environment together with the visible inclusive prefix through `n`. -/
def twoArmEnvironmentPrefix
    {Env : Type v} (n : Nat)
    (sample : Env × ((k : Nat) -> Fin 2 × Real)) :
    Env × History.FinitePairHistory (Fin 2) Real n :=
  (sample.1, Preorder.frestrictLe n sample.2)

/-- The next generated action/reward pair after the inclusive prefix. -/
def twoArmNextPair
    {Env : Type v} (n : Nat)
    (sample : Env × ((k : Nat) -> Fin 2 × Real)) : Fin 2 × Real :=
  sample.2 (n + 1)

theorem measurable_twoArmEnvironmentPrefix
    {Env : Type v} [MeasurableSpace Env] (n : Nat) :
    Measurable (twoArmEnvironmentPrefix (Env := Env) n) :=
  measurable_fst.prodMk
    ((Preorder.measurable_frestrictLe n).comp measurable_snd)

theorem measurable_twoArmNextPair
    {Env : Type v} [MeasurableSpace Env] (n : Nat) :
    Measurable (twoArmNextPair (Env := Env) n) :=
  (measurable_pi_apply (n + 1)).comp measurable_snd

/-- The sigma-algebra generated by retaining the environment and the inclusive
trace prefix through `n`. -/
@[reducible] def twoArmPrefixSigma
    {Env : Type v} [MeasurableSpace Env] (n : Nat) :
    MeasurableSpace (Env × ((k : Nat) -> Fin 2 × Real)) :=
  (inferInstance : MeasurableSpace
    (Env × History.FinitePairHistory (Fin 2) Real n)).comap
      (twoArmEnvironmentPrefix n)

theorem twoArmPrefixSigma_mono
    {Env : Type v} [MeasurableSpace Env] {n m : Nat} (hnm : n <= m) :
    twoArmPrefixSigma (Env := Env) n <= twoArmPrefixSigma (Env := Env) m := by
  let reduce :
      Env × History.FinitePairHistory (Fin 2) Real m ->
        Env × History.FinitePairHistory (Fin 2) Real n :=
    fun context =>
      (context.1,
        Preorder.frestrictLe₂ (π := fun _ : Nat => Fin 2 × Real)
          hnm context.2)
  have hreduce : Measurable reduce :=
    measurable_fst.prodMk
      ((Preorder.measurable_frestrictLe₂ hnm).comp measurable_snd)
  have hfactor :
      twoArmEnvironmentPrefix (Env := Env) n =
        reduce ∘ twoArmEnvironmentPrefix m := by
    funext sample
    apply Prod.ext
    · rfl
    · exact (congrFun
        (Preorder.frestrictLe₂_comp_frestrictLe
          (π := fun _ : Nat => Fin 2 × Real) hnm) sample.2).symm
  unfold twoArmPrefixSigma
  rw [hfactor, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono hreduce.comap_le

/-- The retained environment/prefix sigma-algebras form the canonical
discrete-time filtration needed by the later tower argument. -/
def twoArmPrefixFiltration
    {Env : Type v} [MeasurableSpace Env] :
    Filtration Nat
      (inferInstance : MeasurableSpace
        (Env × ((k : Nat) -> Fin 2 × Real))) where
  seq := twoArmPrefixSigma
  mono' := fun _ _ hnm => twoArmPrefixSigma_mono hnm
  le' := fun n => (measurable_twoArmEnvironmentPrefix n).comap_le

theorem measurable_twoArmForwardTrajectorySuccessorPotential
    {Env : Type v} [MeasurableSpace Env] (eta : Real) (n : Nat) :
    Measurable
      (fun sample : Env × ((k : Nat) -> Fin 2 × Real) =>
        twoArmForwardSuccessorPotential eta
          (twoArmEnvironmentPrefix n sample).2
          (twoArmNextPair n sample)) :=
  (measurable_twoArmForwardSuccessorPotential eta n).comp
    ((measurable_snd.comp (measurable_twoArmEnvironmentPrefix n)).prodMk
      (measurable_twoArmNextPair n))

theorem measurable_twoArmInverseTrajectorySuccessorPotential
    {Env : Type v} [MeasurableSpace Env] (eta : Real) (n : Nat) :
    Measurable
      (fun sample : Env × ((k : Nat) -> Fin 2 × Real) =>
        twoArmInverseSuccessorPotential eta
          (twoArmEnvironmentPrefix n sample).2
          (twoArmNextPair n sample)) :=
  (measurable_twoArmInverseSuccessorPotential eta n).comp
    ((measurable_snd.comp (measurable_twoArmEnvironmentPrefix n)).prodMk
      (measurable_twoArmNextPair n))

/-- On the actual canonical trajectory, the conditional-distribution integral
of the forward successor potential obeys the source recurrence for almost
every retained environment/prefix. -/
theorem trajectoryPrefix_condDistrib_integral_forwardSuccessor_le
    {Env : Type v} [MeasurableSpace Env] [StandardBorelSpace Env]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (eta Delta : Real) (heta : 0 <= eta)
    (environment : Thompson.MeasurableHistoryEnvironment Env (Fin 2) Real)
    (mean : Fin 2 -> Real)
    (contract : TwoArmBoundedFixedMeanEnvironmentContract environment mean)
    (hgap : mean 0 - mean 1 = Delta)
    (n : Nat) :
    ∀ᵐ context
        ∂(twoArmTrajectoryMeasure prior eta environment).map
          (twoArmEnvironmentPrefix n),
      integral
          (condDistrib (twoArmNextPair n) (twoArmEnvironmentPrefix n)
            (twoArmTrajectoryMeasure prior eta environment) context)
          (twoArmForwardSuccessorPotential eta context.2) <=
        twoArmForwardRecurrenceBound eta Delta context.2 := by
  have hcond :
      condDistrib (twoArmNextPair n) (twoArmEnvironmentPrefix n)
          (twoArmTrajectoryMeasure prior eta environment) =ᵐ[
        (twoArmTrajectoryMeasure prior eta environment).map
          (twoArmEnvironmentPrefix n)]
        Thompson.measurableEnvironmentHistoryStepKernel
          (historyAlgorithm (fun _ : Fin 2 => 0) eta) environment n := by
    simpa [twoArmTrajectoryMeasure, twoArmEnvironmentPrefix,
      twoArmNextPair] using
      (trajectoryMeasure_condDistrib_nextPair_given_environment_prefix
        prior (fun _ : Fin 2 => 0) eta environment n)
  filter_upwards [hcond] with context hkernel
  rw [hkernel]
  exact
    integral_measurableTwoArmHistoryStepKernel_forwardSuccessor_le_of_contract
      eta Delta heta environment mean contract hgap n context.1 context.2

/-- The inverse-potential recurrence transported to the same canonical
trajectory conditional distribution. -/
theorem trajectoryPrefix_condDistrib_integral_inverseSuccessor_le
    {Env : Type v} [MeasurableSpace Env] [StandardBorelSpace Env]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (eta Delta : Real) (heta : 0 <= eta)
    (environment : Thompson.MeasurableHistoryEnvironment Env (Fin 2) Real)
    (mean : Fin 2 -> Real)
    (contract : TwoArmBoundedFixedMeanEnvironmentContract environment mean)
    (hgap : mean 0 - mean 1 = Delta)
    (n : Nat) :
    ∀ᵐ context
        ∂(twoArmTrajectoryMeasure prior eta environment).map
          (twoArmEnvironmentPrefix n),
      integral
          (condDistrib (twoArmNextPair n) (twoArmEnvironmentPrefix n)
            (twoArmTrajectoryMeasure prior eta environment) context)
          (twoArmInverseSuccessorPotential eta context.2) <=
        twoArmInverseRecurrenceBound eta Delta context.2 := by
  have hcond :
      condDistrib (twoArmNextPair n) (twoArmEnvironmentPrefix n)
          (twoArmTrajectoryMeasure prior eta environment) =ᵐ[
        (twoArmTrajectoryMeasure prior eta environment).map
          (twoArmEnvironmentPrefix n)]
        Thompson.measurableEnvironmentHistoryStepKernel
          (historyAlgorithm (fun _ : Fin 2 => 0) eta) environment n := by
    simpa [twoArmTrajectoryMeasure, twoArmEnvironmentPrefix,
      twoArmNextPair] using
      (trajectoryMeasure_condDistrib_nextPair_given_environment_prefix
        prior (fun _ : Fin 2 => 0) eta environment n)
  filter_upwards [hcond] with context hkernel
  rw [hkernel]
  exact
    integral_measurableTwoArmHistoryStepKernel_inverseSuccessor_le_of_contract
      eta Delta heta environment mean contract hgap n context.1 context.2

end

end StochasticGradientBandit
end BanditRLProof
