import BanditRLProof.Algorithms.StochasticGradientBanditTwoArmInitialRecurrence
import BanditRLProof.Algorithms.StochasticGradientBanditTwoArmMeasurableRecurrence

/-!
# Path-level integrability for the two-arm SGB exponential recurrences

This module closes the finite-time regularity boundary needed before the
conditional-distribution recurrences can be used in a tower argument.

Probability / process / filtration ledger:

* the ambient measure is `twoArmTrajectoryMeasure prior eta environment`, a
  finite (not necessarily probability) measure unless the caller separately
  assumes `IsProbabilityMeasure prior`;
* the random process is the forward and inverse exponential potential after
  consuming trace coordinates `0,...,n+1`;
* `twoArmPrefixFiltration` retains the latent environment and the inclusive
  action/reward prefix; no independence assertion is introduced;
* `TwoArmBoundedFixedMeanEnvironmentContract` supplies `|reward| <= 1` on each
  initial/successor reward fiber.  The mixed initial-pair and prefix/next-pair
  laws transport those fiber statements to the canonical full trajectory;
* the finite-history parameter is then bounded pathwise by the number of
  consumed rewards times `|eta|`, which gives an integrable deterministic
  exponential envelope on every fixed finite horizon;
* no gap positivity, conditional MGF, summability, or all-time uniform bound
  is used here.  These declarations establish fixed-`n` successor
  integrability and one-step conditional recurrences only; they do not supply
  the initial unconditional trajectory step, recurrence-bound integrability,
  tower iteration, telescoping, or a regret endpoint.

The support transport is explicit: a reward-fiber a.e. statement is never
treated as a full-trajectory a.e. statement without first using the exact
canonical mixed law and `ae_map_iff`.
-/

namespace BanditRLProof
namespace StochasticGradientBandit

open MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory

noncomputable section

universe v

/-! ## Initial recurrence wrappers from the uniform environment contract -/

/-- The uniform contract supplies the source-round forward base recurrence. -/
theorem integral_twoArmInitialPairKernel_exp_forwardIncrement_le_of_contract
    {Env : Type v} [MeasurableSpace Env]
    (eta Delta : Real) (heta : 0 <= eta)
    (environment : Thompson.MeasurableHistoryEnvironment Env (Fin 2) Real)
    (mean : Fin 2 -> Real)
    (contract : TwoArmBoundedFixedMeanEnvironmentContract environment mean)
    (hgap : mean 0 - mean 1 = Delta) (env : Env) :
    integral
        (Thompson.measurableEnvironmentInitialPairKernel
          (historyAlgorithm (fun _ : Fin 2 => 0) eta) environment env)
        (fun pair : Fin 2 × Real =>
          Real.exp
            (2 * eta *
              sourceIncrement (fun _ : Fin 2 => (1 : Real) / 2)
                pair.2 pair.1 0)) <=
      1 + (eta * Delta + eta ^ 2 * sourceC eta) / 2 := by
  exact integral_twoArmInitialPairKernel_exp_forwardIncrement_le
    eta Delta heta environment env mean
      (contract.initial_reward_bound env)
      (contract.initial_mean env) hgap

/-- The same contract supplies the source-round inverse base recurrence. -/
theorem integral_twoArmInitialPairKernel_exp_inverseIncrement_le_of_contract
    {Env : Type v} [MeasurableSpace Env]
    (eta Delta : Real) (heta : 0 <= eta)
    (environment : Thompson.MeasurableHistoryEnvironment Env (Fin 2) Real)
    (mean : Fin 2 -> Real)
    (contract : TwoArmBoundedFixedMeanEnvironmentContract environment mean)
    (hgap : mean 0 - mean 1 = Delta) (env : Env) :
    integral
        (Thompson.measurableEnvironmentInitialPairKernel
          (historyAlgorithm (fun _ : Fin 2 => 0) eta) environment env)
        (fun pair : Fin 2 × Real =>
          Real.exp
            (-2 * eta *
              sourceIncrement (fun _ : Fin 2 => (1 : Real) / 2)
                pair.2 pair.1 0)) <=
      1 - eta / 2 * (Delta - eta * sourceC eta) := by
  exact integral_twoArmInitialPairKernel_exp_inverseIncrement_le
    eta Delta heta environment env mean
      (contract.initial_reward_bound env)
      (contract.initial_mean env) hgap

/-! ## Exact support transport to the canonical trajectory -/

/-- The initial reward bound holds on the full prior-mixed canonical path. -/
theorem twoArmTrajectoryMeasure_reward_zero_abs_le_one_ae
    {Env : Type v} [MeasurableSpace Env]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (eta : Real)
    (environment : Thompson.MeasurableHistoryEnvironment Env (Fin 2) Real)
    (mean : Fin 2 -> Real)
    (contract : TwoArmBoundedFixedMeanEnvironmentContract environment mean) :
    ∀ᵐ sample ∂twoArmTrajectoryMeasure prior eta environment,
      |(sample.2 0).2| <= 1 := by
  let mu := twoArmTrajectoryMeasure prior eta environment
  let joinEnvironmentInitial :=
    fun sample : Env × ((k : Nat) -> Fin 2 × Real) =>
      (sample.1, sample.2 0)
  have hjoin : Measurable joinEnvironmentInitial :=
    measurable_fst.prodMk ((measurable_pi_apply 0).comp measurable_snd)
  have hp : MeasurableSet
      {sample : Env × (Fin 2 × Real) | |sample.2.2| <= 1} := by
    exact measurableSet_le
      ((measurable_snd.comp measurable_snd).abs) measurable_const
  have hkernel :
      mu.map joinEnvironmentInitial =
        prior ⊗ₘ
          Thompson.measurableEnvironmentInitialPairKernel
            (historyAlgorithm (fun _ : Fin 2 => 0) eta) environment := by
    simpa [mu, twoArmTrajectoryMeasure, joinEnvironmentInitial] using
      (Exp3.canonicalMeasurableEnvironmentTrajectoryMeasure_map_environment_eval_zero
        prior (historyAlgorithm (fun _ : Fin 2 => 0) eta) environment)
  have hjoint : ∀ᵐ sample ∂
      prior ⊗ₘ
        Thompson.measurableEnvironmentInitialPairKernel
          (historyAlgorithm (fun _ : Fin 2 => 0) eta) environment,
      |sample.2.2| <= 1 := by
    apply Measure.ae_compProd_of_ae_ae hp
    filter_upwards [] with env
    have hpPair : MeasurableSet
        {pair : Fin 2 × Real | |pair.2| <= 1} := by
      exact measurableSet_le measurable_snd.abs measurable_const
    rw [Thompson.measurableEnvironmentInitialPairKernel_apply]
    apply Measure.ae_compProd_of_ae_ae hpPair
    filter_upwards [] with selected
    simpa [Thompson.MeasurableHistoryEnvironment.at,
      Kernel.comap_apply] using
      contract.initial_reward_bound env selected
  rw [← hkernel] at hjoint
  exact (ae_map_iff hjoin.aemeasurable hp).mp hjoint

/-- Every fixed successor reward bound also holds on the full canonical path. -/
theorem twoArmTrajectoryMeasure_reward_succ_abs_le_one_ae
    {Env : Type v} [MeasurableSpace Env] [StandardBorelSpace Env]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (eta : Real)
    (environment : Thompson.MeasurableHistoryEnvironment Env (Fin 2) Real)
    (mean : Fin 2 -> Real)
    (contract : TwoArmBoundedFixedMeanEnvironmentContract environment mean)
    (n : Nat) :
    ∀ᵐ sample ∂twoArmTrajectoryMeasure prior eta environment,
      |(sample.2 (n + 1)).2| <= 1 := by
  let mu := twoArmTrajectoryMeasure prior eta environment
  let joinEnvironmentPrefixNext :=
    fun sample : Env × ((k : Nat) -> Fin 2 × Real) =>
      ((sample.1, Preorder.frestrictLe n sample.2), sample.2 (n + 1))
  have hjoin : Measurable joinEnvironmentPrefixNext :=
    (measurable_fst.prodMk
      ((Preorder.measurable_frestrictLe n).comp measurable_snd)).prodMk
        ((measurable_pi_apply (n + 1)).comp measurable_snd)
  have hp : MeasurableSet
      {sample : (Env × History.FinitePairHistory (Fin 2) Real n) ×
          (Fin 2 × Real) | |sample.2.2| <= 1} := by
    exact measurableSet_le
      ((measurable_snd.comp measurable_snd).abs) measurable_const
  have hkernel :
      mu.map joinEnvironmentPrefixNext =
        mu.map (fun sample =>
            (sample.1, Preorder.frestrictLe n sample.2)) ⊗ₘ
          Thompson.measurableEnvironmentHistoryStepKernel
            (historyAlgorithm (fun _ : Fin 2 => 0) eta) environment n := by
    simpa [mu, twoArmTrajectoryMeasure, joinEnvironmentPrefixNext] using
      (Exp3.canonicalMeasurableEnvironmentTrajectoryMeasure_map_environment_prefix_next_eq_compProd
        prior (historyAlgorithm (fun _ : Fin 2 => 0) eta) environment n)
  have hjoint : ∀ᵐ sample ∂
      mu.map (fun sample =>
          (sample.1, Preorder.frestrictLe n sample.2)) ⊗ₘ
        Thompson.measurableEnvironmentHistoryStepKernel
          (historyAlgorithm (fun _ : Fin 2 => 0) eta) environment n,
      |sample.2.2| <= 1 := by
    apply Measure.ae_compProd_of_ae_ae hp
    filter_upwards [] with environmentHistory
    have hpPair : MeasurableSet
        {pair : Fin 2 × Real | |pair.2| <= 1} := by
      exact measurableSet_le measurable_snd.abs measurable_const
    rw [Thompson.measurableEnvironmentHistoryStepKernel,
      Kernel.compProd_apply_eq_compProd_sectR]
    apply Measure.ae_compProd_of_ae_ae hpPair
    filter_upwards [] with selected
    rw [Kernel.sectR_apply, Kernel.comap_apply]
    exact contract.successor_reward_bound n environmentHistory.1
      environmentHistory.2 selected
  rw [← hkernel] at hjoint
  exact (ae_map_iff hjoin.aemeasurable hp).mp hjoint

/-- Uniform fixed-coordinate wrapper, separating coordinate zero from shifted
successor coordinates. -/
theorem twoArmTrajectoryMeasure_reward_abs_le_one_ae
    {Env : Type v} [MeasurableSpace Env] [StandardBorelSpace Env]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (eta : Real)
    (environment : Thompson.MeasurableHistoryEnvironment Env (Fin 2) Real)
    (mean : Fin 2 -> Real)
    (contract : TwoArmBoundedFixedMeanEnvironmentContract environment mean)
    (t : Nat) :
    ∀ᵐ sample ∂twoArmTrajectoryMeasure prior eta environment,
      |(sample.2 t).2| <= 1 := by
  cases t with
  | zero =>
      exact twoArmTrajectoryMeasure_reward_zero_abs_le_one_ae
        prior eta environment mean contract
  | succ n =>
      exact twoArmTrajectoryMeasure_reward_succ_abs_le_one_ae
        prior eta environment mean contract n

/-- For a fixed finite prefix, all reward coordinates are simultaneously in
the source support almost everywhere. -/
theorem twoArmTrajectoryMeasure_prefix_rewards_abs_le_one_ae
    {Env : Type v} [MeasurableSpace Env] [StandardBorelSpace Env]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (eta : Real)
    (environment : Thompson.MeasurableHistoryEnvironment Env (Fin 2) Real)
    (mean : Fin 2 -> Real)
    (contract : TwoArmBoundedFixedMeanEnvironmentContract environment mean)
    (n : Nat) :
    ∀ᵐ sample ∂twoArmTrajectoryMeasure prior eta environment,
      ∀ i : Finset.Iic n, |(sample.2 i.1).2| <= 1 := by
  rw [ae_all_iff]
  intro i
  exact twoArmTrajectoryMeasure_reward_abs_le_one_ae
    prior eta environment mean contract i.1

/-! ## Deterministic finite-prefix envelopes -/

/-- One Algorithm-1 coordinate update is no larger than the observed reward
when the coordinate probability lies in `[0,1]`. -/
theorem abs_sourceIncrement_le_abs_reward_of_mem_Icc
    {Action : Type*} [DecidableEq Action]
    (p : Action -> Real) (reward : Real)
    (selected coordinate : Action)
    (hp_nonneg : 0 <= p coordinate) (hp_le_one : p coordinate <= 1) :
    |sourceIncrement p reward selected coordinate| <= |reward| := by
  by_cases hselected : selected = coordinate
  · rw [sourceIncrement, if_pos hselected, abs_mul,
      abs_of_nonneg (sub_nonneg.mpr hp_le_one)]
    exact mul_le_of_le_one_left (abs_nonneg reward) (by linarith)
  · rw [sourceIncrement, if_neg hselected, abs_neg, abs_mul,
      abs_of_nonneg hp_nonneg]
    exact mul_le_of_le_one_left (abs_nonneg reward) hp_le_one

/-- Softmax coordinates satisfy the probability premises of the preceding
generic update bound. -/
theorem abs_sourceIncrement_softmax_le_abs_reward
    {Action : Type*} [Fintype Action] [DecidableEq Action] [Nonempty Action]
    (theta : Action -> Real) (reward : Real) (selected coordinate : Action) :
    |sourceIncrement (softmaxProbability theta) reward selected coordinate| <=
      |reward| :=
  abs_sourceIncrement_le_abs_reward_of_mem_Icc
    (softmaxProbability theta) reward selected coordinate
      (softmaxProbability_nonneg theta coordinate)
      (softmaxProbability_le_one theta coordinate)

/-! ## Equation-(5) update integrability from the source support contract -/

/-- The bounded fixed-mean contract discharges the initial-pair
`Integrable sourceIncrement` premise used by Equation (5).  Only the support
field of the contract is needed: softmax updates are measurable and have
absolute value at most the observed reward. -/
theorem integrable_measurableTwoArmInitialPairKernel_sourceIncrement_of_contract
    {Env : Type v} [MeasurableSpace Env]
    (initialTheta : Fin 2 -> Real) (eta : Real)
    (environment : Thompson.MeasurableHistoryEnvironment Env (Fin 2) Real)
    (mean : Fin 2 -> Real)
    (contract : TwoArmBoundedFixedMeanEnvironmentContract environment mean)
    (env : Env) (coordinate : Fin 2) :
    Integrable
      (fun pair : Fin 2 × Real =>
        sourceIncrement (softmaxProbability initialTheta)
          pair.2 pair.1 coordinate)
      (Thompson.measurableEnvironmentInitialPairKernel
        (historyAlgorithm initialTheta eta) environment env) := by
  have hmeas : Measurable
      (fun pair : Fin 2 × Real =>
        sourceIncrement (softmaxProbability initialTheta)
          pair.2 pair.1 coordinate) :=
    measurable_sourceIncrement
      (fun _pair : Fin 2 × Real => softmaxProbability initialTheta)
      Prod.snd Prod.fst coordinate measurable_const measurable_snd
        measurable_fst
  apply Integrable.of_bound hmeas.aestronglyMeasurable 1
  have hpPair : MeasurableSet
      {pair : Fin 2 × Real | |pair.2| <= 1} := by
    exact measurableSet_le measurable_snd.abs measurable_const
  have hbound :
      ∀ᵐ pair
          ∂Thompson.measurableEnvironmentInitialPairKernel
            (historyAlgorithm initialTheta eta) environment env,
        |pair.2| <= 1 := by
    rw [Thompson.measurableEnvironmentInitialPairKernel_apply]
    apply Measure.ae_compProd_of_ae_ae hpPair
    filter_upwards [] with selected
    simpa [Thompson.MeasurableHistoryEnvironment.at,
      Kernel.comap_apply] using
      contract.initial_reward_bound env selected
  filter_upwards [hbound] with pair hreward
  rw [Real.norm_eq_abs]
  exact (abs_sourceIncrement_softmax_le_abs_reward
    initialTheta pair.2 pair.1 coordinate).trans hreward

/-- The same contract discharges Equation-(5)'s source-increment
integrability premise at every generated successor history.  No independence,
gap, or learning-rate assumption is introduced. -/
theorem integrable_measurableTwoArmHistoryStepKernel_sourceIncrement_of_contract
    {Env : Type v} [MeasurableSpace Env]
    (initialTheta : Fin 2 -> Real) (eta : Real)
    (environment : Thompson.MeasurableHistoryEnvironment Env (Fin 2) Real)
    (mean : Fin 2 -> Real)
    (contract : TwoArmBoundedFixedMeanEnvironmentContract environment mean)
    (n : Nat) (env : Env)
    (history : History.FinitePairHistory (Fin 2) Real n)
    (coordinate : Fin 2) :
    Integrable
      (fun pair : Fin 2 × Real =>
        sourceIncrement
          (softmaxProbability
            (historyParameter initialTheta eta n history))
          pair.2 pair.1 coordinate)
      (Thompson.measurableEnvironmentHistoryStepKernel
        (historyAlgorithm initialTheta eta)
        environment n (env, history)) := by
  have hmeas : Measurable
      (fun pair : Fin 2 × Real =>
        sourceIncrement
          (softmaxProbability
            (historyParameter initialTheta eta n history))
          pair.2 pair.1 coordinate) :=
    measurable_sourceIncrement
      (fun _pair : Fin 2 × Real =>
        softmaxProbability
          (historyParameter initialTheta eta n history))
      Prod.snd Prod.fst coordinate measurable_const measurable_snd
        measurable_fst
  apply Integrable.of_bound hmeas.aestronglyMeasurable 1
  have hpPair : MeasurableSet
      {pair : Fin 2 × Real | |pair.2| <= 1} := by
    exact measurableSet_le measurable_snd.abs measurable_const
  have hbound :
      ∀ᵐ pair
          ∂Thompson.measurableEnvironmentHistoryStepKernel
            (historyAlgorithm initialTheta eta)
            environment n (env, history),
        |pair.2| <= 1 := by
    rw [Thompson.measurableEnvironmentHistoryStepKernel_apply,
      Thompson.historyStepKernel,
      ProbabilityTheory.Kernel.compProd_apply_eq_compProd_sectR]
    apply Measure.ae_compProd_of_ae_ae hpPair
    filter_upwards [] with selected
    rw [Kernel.sectR_apply]
    simpa [Thompson.MeasurableHistoryEnvironment.at,
      Kernel.comap_apply] using
      contract.successor_reward_bound n env history selected
  filter_upwards [hbound] with pair hreward
  rw [Real.norm_eq_abs]
  exact (abs_sourceIncrement_softmax_le_abs_reward
    (historyParameter initialTheta eta n history)
    pair.2 pair.1 coordinate).trans hreward

/-- On a finite history supported in `[-1,1]`, every zero-initialized
Algorithm-1 parameter coordinate grows by at most `|eta|` per consumed pair. -/
theorem abs_historyParameter_zeroInitialization_le
    (eta : Real) : forall n
      (history : History.FinitePairHistory (Fin 2) Real n)
      (coordinate : Fin 2),
      (forall i, |(history i).2| <= 1) ->
      |historyParameter (fun _ : Fin 2 => 0) eta n history coordinate| <=
        ((n + 1 : Nat) : Real) * |eta| := by
  intro n
  induction n with
  | zero =>
      intro history coordinate hreward
      rw [historyParameter_zero]
      simp only [zero_add]
      calc
        |eta * sourceIncrement (softmaxProbability (fun _ : Fin 2 => 0))
            (history ⟨0, Finset.mem_Iic.mpr le_rfl⟩).2
            (history ⟨0, Finset.mem_Iic.mpr le_rfl⟩).1 coordinate| =
            |eta| *
              |sourceIncrement (softmaxProbability (fun _ : Fin 2 => 0))
                (history ⟨0, Finset.mem_Iic.mpr le_rfl⟩).2
                (history ⟨0, Finset.mem_Iic.mpr le_rfl⟩).1
                coordinate| := abs_mul _ _
        _ <= |eta| * |(history ⟨0, Finset.mem_Iic.mpr le_rfl⟩).2| :=
          mul_le_mul_of_nonneg_left
            (abs_sourceIncrement_softmax_le_abs_reward
              (fun _ : Fin 2 => 0)
              (history ⟨0, Finset.mem_Iic.mpr le_rfl⟩).2
              (history ⟨0, Finset.mem_Iic.mpr le_rfl⟩).1 coordinate)
            (abs_nonneg eta)
        _ <= |eta| * 1 :=
          mul_le_mul_of_nonneg_left
            (hreward ⟨0, Finset.mem_Iic.mpr le_rfl⟩) (abs_nonneg eta)
        _ = (((0 + 1 : Nat) : Real) * |eta|) := by ring
  | succ n ih =>
      intro history coordinate hreward
      rw [historyParameter_succ]
      have hprevious : forall
          i : Finset.Iic n,
          |(Exp3.previousPairHistory history i).2| <= 1 := by
        intro i
        exact hreward
          ⟨i.1, Finset.mem_Iic.mpr
            ((Finset.mem_Iic.mp i.2).trans (Nat.le_succ n))⟩
      have htheta := ih (Exp3.previousPairHistory history) coordinate hprevious
      have hincrement :
          |sourceIncrement
              (softmaxProbability
                (historyParameter (fun _ : Fin 2 => 0) eta n
                  (Exp3.previousPairHistory history)))
              (history ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩).2
              (history ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩).1
              coordinate| <= 1 :=
        (abs_sourceIncrement_softmax_le_abs_reward
          (historyParameter (fun _ : Fin 2 => 0) eta n
            (Exp3.previousPairHistory history))
          (history ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩).2
          (history ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩).1 coordinate).trans
            (hreward ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩)
      calc
        |historyParameter (fun _ : Fin 2 => 0) eta n
              (Exp3.previousPairHistory history) coordinate +
            eta * sourceIncrement
              (softmaxProbability
                (historyParameter (fun _ : Fin 2 => 0) eta n
                  (Exp3.previousPairHistory history)))
              (history ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩).2
              (history ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩).1
              coordinate| <=
            |historyParameter (fun _ : Fin 2 => 0) eta n
              (Exp3.previousPairHistory history) coordinate| +
            |eta * sourceIncrement
              (softmaxProbability
                (historyParameter (fun _ : Fin 2 => 0) eta n
                  (Exp3.previousPairHistory history)))
              (history ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩).2
              (history ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩).1
              coordinate| := abs_add_le _ _
        _ <= ((n + 1 : Nat) : Real) * |eta| + |eta| * 1 := by
          exact add_le_add htheta
            (by rw [abs_mul]; exact
              mul_le_mul_of_nonneg_left hincrement (abs_nonneg eta))
        _ = (((n + 1 + 1 : Nat) : Real) * |eta|) := by
          push_cast
          ring

/-- The forward successor potential is exactly the exponential of the next
finite-history parameter. -/
theorem twoArmForwardTrajectorySuccessorPotential_eq_exp_historyParameter
    {Env : Type v} [MeasurableSpace Env]
    (eta : Real) (n : Nat)
    (sample : Env × ((k : Nat) -> Fin 2 × Real)) :
    twoArmForwardSuccessorPotential eta
        (twoArmEnvironmentPrefix n sample).2 (twoArmNextPair n sample) =
      Real.exp
        (2 * historyParameter (fun _ : Fin 2 => 0) eta (n + 1)
          (Preorder.frestrictLe (n + 1) sample.2) 0) := by
  rw [historyParameter_succ]
  have hprevious :
      Exp3.previousPairHistory (Preorder.frestrictLe (n + 1) sample.2) =
        Preorder.frestrictLe n sample.2 := by
    funext i
    rfl
  rw [hprevious]
  rfl

/-- The inverse successor potential has the analogous next-parameter form. -/
theorem twoArmInverseTrajectorySuccessorPotential_eq_exp_historyParameter
    {Env : Type v} [MeasurableSpace Env]
    (eta : Real) (n : Nat)
    (sample : Env × ((k : Nat) -> Fin 2 × Real)) :
    twoArmInverseSuccessorPotential eta
        (twoArmEnvironmentPrefix n sample).2 (twoArmNextPair n sample) =
      Real.exp
        (-2 * historyParameter (fun _ : Fin 2 => 0) eta (n + 1)
          (Preorder.frestrictLe (n + 1) sample.2) 0) := by
  rw [historyParameter_succ]
  have hprevious :
      Exp3.previousPairHistory (Preorder.frestrictLe (n + 1) sample.2) =
        Preorder.frestrictLe n sample.2 := by
    funext i
    rfl
  rw [hprevious]
  rfl

/-! ## Fixed-time path-level integrability -/

/-- The actual forward successor exponential is integrable on the canonical
trajectory at every fixed successor index.  A finite prior is sufficient; no
normalization of the prior is claimed or used. -/
theorem integrable_twoArmForwardTrajectorySuccessorPotential
    {Env : Type v} [MeasurableSpace Env] [StandardBorelSpace Env]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (eta : Real)
    (environment : Thompson.MeasurableHistoryEnvironment Env (Fin 2) Real)
    (mean : Fin 2 -> Real)
    (contract : TwoArmBoundedFixedMeanEnvironmentContract environment mean)
    (n : Nat) :
    Integrable
      (fun sample : Env × ((k : Nat) -> Fin 2 × Real) =>
        twoArmForwardSuccessorPotential eta
          (twoArmEnvironmentPrefix n sample).2
          (twoArmNextPair n sample))
      (twoArmTrajectoryMeasure prior eta environment) := by
  apply Integrable.of_bound
    (measurable_twoArmForwardTrajectorySuccessorPotential
      (Env := Env) eta n).aestronglyMeasurable
    (Real.exp (2 * ((n + 2 : Nat) : Real) * |eta|))
  filter_upwards
      [twoArmTrajectoryMeasure_prefix_rewards_abs_le_one_ae
        prior eta environment mean contract (n + 1)]
    with sample hreward
  rw [twoArmForwardTrajectorySuccessorPotential_eq_exp_historyParameter]
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  have htheta :=
    abs_historyParameter_zeroInitialization_le eta (n + 1)
      (Preorder.frestrictLe (n + 1) sample.2) 0 (by
        intro i
        exact hreward i)
  calc
    2 * historyParameter (fun _ : Fin 2 => 0) eta (n + 1)
          (Preorder.frestrictLe (n + 1) sample.2) 0 <=
        2 *
          |historyParameter (fun _ : Fin 2 => 0) eta (n + 1)
            (Preorder.frestrictLe (n + 1) sample.2) 0| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) (by norm_num)
    _ <= 2 * (((n + 1 + 1 : Nat) : Real) * |eta|) :=
      mul_le_mul_of_nonneg_left htheta (by norm_num)
    _ = 2 * ((n + 2 : Nat) : Real) * |eta| := by
      push_cast
      ring

/-- The inverse-odds successor exponential has the same deterministic
fixed-time envelope and is integrable on the same canonical trajectory. -/
theorem integrable_twoArmInverseTrajectorySuccessorPotential
    {Env : Type v} [MeasurableSpace Env] [StandardBorelSpace Env]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (eta : Real)
    (environment : Thompson.MeasurableHistoryEnvironment Env (Fin 2) Real)
    (mean : Fin 2 -> Real)
    (contract : TwoArmBoundedFixedMeanEnvironmentContract environment mean)
    (n : Nat) :
    Integrable
      (fun sample : Env × ((k : Nat) -> Fin 2 × Real) =>
        twoArmInverseSuccessorPotential eta
          (twoArmEnvironmentPrefix n sample).2
          (twoArmNextPair n sample))
      (twoArmTrajectoryMeasure prior eta environment) := by
  apply Integrable.of_bound
    (measurable_twoArmInverseTrajectorySuccessorPotential
      (Env := Env) eta n).aestronglyMeasurable
    (Real.exp (2 * ((n + 2 : Nat) : Real) * |eta|))
  filter_upwards
      [twoArmTrajectoryMeasure_prefix_rewards_abs_le_one_ae
        prior eta environment mean contract (n + 1)]
    with sample hreward
  rw [twoArmInverseTrajectorySuccessorPotential_eq_exp_historyParameter]
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  have htheta :=
    abs_historyParameter_zeroInitialization_le eta (n + 1)
      (Preorder.frestrictLe (n + 1) sample.2) 0 (by
        intro i
        exact hreward i)
  calc
    -2 * historyParameter (fun _ : Fin 2 => 0) eta (n + 1)
          (Preorder.frestrictLe (n + 1) sample.2) 0 <=
        2 *
          |historyParameter (fun _ : Fin 2 => 0) eta (n + 1)
            (Preorder.frestrictLe (n + 1) sample.2) 0| := by
      have hneg := neg_le_abs
        (historyParameter (fun _ : Fin 2 => 0) eta (n + 1)
          (Preorder.frestrictLe (n + 1) sample.2) 0)
      nlinarith
    _ <= 2 * (((n + 1 + 1 : Nat) : Real) * |eta|) :=
      mul_le_mul_of_nonneg_left htheta (by norm_num)
    _ = 2 * ((n + 2 : Nat) : Real) * |eta| := by
      push_cast
      ring

/-! ## Conditional-expectation wrappers -/

/-- The fixed-time forward potential has the regular-conditional-distribution
representation with respect to the environment/prefix sigma-algebra. -/
theorem twoArmForwardTrajectorySuccessor_condExp_ae_eq_integral_condDistrib
    {Env : Type v} [MeasurableSpace Env] [StandardBorelSpace Env]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (eta : Real)
    (environment : Thompson.MeasurableHistoryEnvironment Env (Fin 2) Real)
    (mean : Fin 2 -> Real)
    (contract : TwoArmBoundedFixedMeanEnvironmentContract environment mean)
    (n : Nat) :
    (twoArmTrajectoryMeasure prior eta environment)[
        fun sample : Env × ((k : Nat) -> Fin 2 × Real) =>
          twoArmForwardSuccessorPotential eta
            (twoArmEnvironmentPrefix n sample).2
            (twoArmNextPair n sample) |
        twoArmPrefixSigma (Env := Env) n] =ᵐ[
          twoArmTrajectoryMeasure prior eta environment]
      fun sample : Env × ((k : Nat) -> Fin 2 × Real) =>
        integral
          (condDistrib (twoArmNextPair n) (twoArmEnvironmentPrefix n)
            (twoArmTrajectoryMeasure prior eta environment)
            (twoArmEnvironmentPrefix n sample))
          (twoArmForwardSuccessorPotential eta
            (twoArmEnvironmentPrefix n sample).2) := by
  let pairPotential :=
    fun input :
        (Env × History.FinitePairHistory (Fin 2) Real n) ×
          (Fin 2 × Real) =>
      twoArmForwardSuccessorPotential eta input.1.2 input.2
  have hpairPotential : Measurable pairPotential :=
    (measurable_twoArmForwardSuccessorPotential eta n).comp
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  simpa [pairPotential, twoArmPrefixSigma] using
    (condExp_prod_ae_eq_integral_condDistrib
      (μ := twoArmTrajectoryMeasure prior eta environment)
      (f := pairPotential)
      (measurable_twoArmEnvironmentPrefix (Env := Env) n)
      (measurable_twoArmNextPair (Env := Env) n).aemeasurable
      hpairPotential.stronglyMeasurable
      (integrable_twoArmForwardTrajectorySuccessorPotential
        prior eta environment mean contract n))

/-- The inverse potential has the same conditional-distribution
representation. -/
theorem twoArmInverseTrajectorySuccessor_condExp_ae_eq_integral_condDistrib
    {Env : Type v} [MeasurableSpace Env] [StandardBorelSpace Env]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (eta : Real)
    (environment : Thompson.MeasurableHistoryEnvironment Env (Fin 2) Real)
    (mean : Fin 2 -> Real)
    (contract : TwoArmBoundedFixedMeanEnvironmentContract environment mean)
    (n : Nat) :
    (twoArmTrajectoryMeasure prior eta environment)[
        fun sample : Env × ((k : Nat) -> Fin 2 × Real) =>
          twoArmInverseSuccessorPotential eta
            (twoArmEnvironmentPrefix n sample).2
            (twoArmNextPair n sample) |
        twoArmPrefixSigma (Env := Env) n] =ᵐ[
          twoArmTrajectoryMeasure prior eta environment]
      fun sample : Env × ((k : Nat) -> Fin 2 × Real) =>
        integral
          (condDistrib (twoArmNextPair n) (twoArmEnvironmentPrefix n)
            (twoArmTrajectoryMeasure prior eta environment)
            (twoArmEnvironmentPrefix n sample))
          (twoArmInverseSuccessorPotential eta
            (twoArmEnvironmentPrefix n sample).2) := by
  let pairPotential :=
    fun input :
        (Env × History.FinitePairHistory (Fin 2) Real n) ×
          (Fin 2 × Real) =>
      twoArmInverseSuccessorPotential eta input.1.2 input.2
  have hpairPotential : Measurable pairPotential :=
    (measurable_twoArmInverseSuccessorPotential eta n).comp
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  simpa [pairPotential, twoArmPrefixSigma] using
    (condExp_prod_ae_eq_integral_condDistrib
      (μ := twoArmTrajectoryMeasure prior eta environment)
      (f := pairPotential)
      (measurable_twoArmEnvironmentPrefix (Env := Env) n)
      (measurable_twoArmNextPair (Env := Env) n).aemeasurable
      hpairPotential.stronglyMeasurable
      (integrable_twoArmInverseTrajectorySuccessorPotential
        prior eta environment mean contract n))

/-- Tower-ready forward conditional recurrence on the actual canonical path. -/
theorem twoArmForwardTrajectorySuccessor_condExp_le_recurrenceBound
    {Env : Type v} [MeasurableSpace Env] [StandardBorelSpace Env]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (eta Delta : Real) (heta : 0 <= eta)
    (environment : Thompson.MeasurableHistoryEnvironment Env (Fin 2) Real)
    (mean : Fin 2 -> Real)
    (contract : TwoArmBoundedFixedMeanEnvironmentContract environment mean)
    (hgap : mean 0 - mean 1 = Delta) (n : Nat) :
    (twoArmTrajectoryMeasure prior eta environment)[
        fun sample : Env × ((k : Nat) -> Fin 2 × Real) =>
          twoArmForwardSuccessorPotential eta
            (twoArmEnvironmentPrefix n sample).2
            (twoArmNextPair n sample) |
        twoArmPrefixSigma (Env := Env) n] ≤ᵐ[
          twoArmTrajectoryMeasure prior eta environment]
      fun sample : Env × ((k : Nat) -> Fin 2 × Real) =>
        twoArmForwardRecurrenceBound eta Delta
          (twoArmEnvironmentPrefix n sample).2 := by
  have hcond :=
    twoArmForwardTrajectorySuccessor_condExp_ae_eq_integral_condDistrib
      prior eta environment mean contract n
  have hrecurrence := MeasureTheory.ae_of_ae_map
    (measurable_twoArmEnvironmentPrefix (Env := Env) n).aemeasurable
    (trajectoryPrefix_condDistrib_integral_forwardSuccessor_le
      prior eta Delta heta environment mean contract hgap n)
  filter_upwards [hcond, hrecurrence] with sample hcond hrecurrence
  rw [hcond]
  exact hrecurrence

/-- Tower-ready inverse conditional recurrence on the same path. -/
theorem twoArmInverseTrajectorySuccessor_condExp_le_recurrenceBound
    {Env : Type v} [MeasurableSpace Env] [StandardBorelSpace Env]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (eta Delta : Real) (heta : 0 <= eta)
    (environment : Thompson.MeasurableHistoryEnvironment Env (Fin 2) Real)
    (mean : Fin 2 -> Real)
    (contract : TwoArmBoundedFixedMeanEnvironmentContract environment mean)
    (hgap : mean 0 - mean 1 = Delta) (n : Nat) :
    (twoArmTrajectoryMeasure prior eta environment)[
        fun sample : Env × ((k : Nat) -> Fin 2 × Real) =>
          twoArmInverseSuccessorPotential eta
            (twoArmEnvironmentPrefix n sample).2
            (twoArmNextPair n sample) |
        twoArmPrefixSigma (Env := Env) n] ≤ᵐ[
          twoArmTrajectoryMeasure prior eta environment]
      fun sample : Env × ((k : Nat) -> Fin 2 × Real) =>
        twoArmInverseRecurrenceBound eta Delta
          (twoArmEnvironmentPrefix n sample).2 := by
  have hcond :=
    twoArmInverseTrajectorySuccessor_condExp_ae_eq_integral_condDistrib
      prior eta environment mean contract n
  have hrecurrence := MeasureTheory.ae_of_ae_map
    (measurable_twoArmEnvironmentPrefix (Env := Env) n).aemeasurable
    (trajectoryPrefix_condDistrib_integral_inverseSuccessor_le
      prior eta Delta heta environment mean contract hgap n)
  filter_upwards [hcond, hrecurrence] with sample hcond hrecurrence
  rw [hcond]
  exact hrecurrence

end

end StochasticGradientBandit
end BanditRLProof
