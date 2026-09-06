import BanditRLProof.Algorithms.ThompsonCanonicalTrajectory
import BanditRLProof.Algorithms.ETCFiniteArmRewardLaw

/-!
# Measurable environment-indexed Thompson trajectory kernels

The pointwise `HistoryEnvironment` API does not by itself say that feedback
laws vary measurably with the environment.  This module records that missing
joint regularity and uses Mathlib's kernel-valued Ionescu-Tulcea theorem to
construct the complete environment-indexed pair-trajectory kernel.
-/

open MeasureTheory
open scoped ProbabilityTheory

universe u v w

namespace BanditRLProof
namespace Thompson

/--
Jointly measurable feedback environment.  Freezing the first kernel input
recovers the pointwise `HistoryEnvironment` consumed by the density route.
-/
structure MeasurableHistoryEnvironment
    (Env : Type u) (Action : Type v) (Reward : Type w)
    [MeasurableSpace Env] [MeasurableSpace Action] [MeasurableSpace Reward]
    where
  initialFeedback : ProbabilityTheory.Kernel (Env × Action) Reward
  [initialFeedback_isMarkov :
    ProbabilityTheory.IsMarkovKernel initialFeedback]
  feedback : (n : Nat) -> ProbabilityTheory.Kernel
    (Env × (History.FinitePairHistory Action Reward n × Action)) Reward
  [feedback_isMarkov : forall n,
    ProbabilityTheory.IsMarkovKernel (feedback n)]

instance instMeasurableHistoryEnvironmentInitialFeedbackIsMarkov
    {Env : Type u} {Action : Type v} {Reward : Type w}
    [MeasurableSpace Env] [MeasurableSpace Action] [MeasurableSpace Reward]
    (environment : MeasurableHistoryEnvironment Env Action Reward) :
    ProbabilityTheory.IsMarkovKernel environment.initialFeedback :=
  environment.initialFeedback_isMarkov

instance instMeasurableHistoryEnvironmentFeedbackIsMarkov
    {Env : Type u} {Action : Type v} {Reward : Type w}
    [MeasurableSpace Env] [MeasurableSpace Action] [MeasurableSpace Reward]
    (environment : MeasurableHistoryEnvironment Env Action Reward) (n : Nat) :
    ProbabilityTheory.IsMarkovKernel (environment.feedback n) :=
  environment.feedback_isMarkov n

/-- Freeze the measurable environment input to recover the pointwise API. -/
noncomputable def MeasurableHistoryEnvironment.at
    {Env : Type u} {Action : Type v} {Reward : Type w}
    [MeasurableSpace Env] [MeasurableSpace Action] [MeasurableSpace Reward]
    (environment : MeasurableHistoryEnvironment Env Action Reward)
    (env : Env) : HistoryEnvironment Action Reward where
  initialFeedback := environment.initialFeedback.comap
    (Prod.mk env) (measurable_const.prodMk measurable_id)
  feedback n := (environment.feedback n).comap
    (Prod.mk env) (measurable_const.prodMk measurable_id)

/-- Jointly measurable law of the initial action/reward pair. -/
noncomputable def measurableEnvironmentInitialPairKernel
    {Env : Type u} {Action : Type v} {Reward : Type w}
    [MeasurableSpace Env] [MeasurableSpace Action] [MeasurableSpace Reward]
    (algorithm : HistoryAlgorithm Action Reward)
    (environment : MeasurableHistoryEnvironment Env Action Reward) :
    ProbabilityTheory.Kernel Env (Action × Reward) :=
  ProbabilityTheory.Kernel.const Env algorithm.initialAction ⊗ₖ
    environment.initialFeedback

instance instMeasurableEnvironmentInitialPairKernelIsMarkov
    {Env : Type u} {Action : Type v} {Reward : Type w}
    [MeasurableSpace Env] [MeasurableSpace Action] [MeasurableSpace Reward]
    (algorithm : HistoryAlgorithm Action Reward)
    (environment : MeasurableHistoryEnvironment Env Action Reward) :
    ProbabilityTheory.IsMarkovKernel
      (measurableEnvironmentInitialPairKernel algorithm environment) := by
  unfold measurableEnvironmentInitialPairKernel
  infer_instance

/-- Jointly measurable successor pair kernel over environment and history. -/
noncomputable def measurableEnvironmentHistoryStepKernel
    {Env : Type u} {Action : Type v} {Reward : Type w}
    [MeasurableSpace Env] [MeasurableSpace Action] [MeasurableSpace Reward]
    (algorithm : HistoryAlgorithm Action Reward)
    (environment : MeasurableHistoryEnvironment Env Action Reward) (n : Nat) :
    ProbabilityTheory.Kernel
      (Env × History.FinitePairHistory Action Reward n) (Action × Reward) :=
  (algorithm.policy n).comap Prod.snd measurable_snd ⊗ₖ
    (environment.feedback n).comap
      (fun input => (input.1.1, (input.1.2, input.2))) (by fun_prop)

instance instMeasurableEnvironmentHistoryStepKernelIsMarkov
    {Env : Type u} {Action : Type v} {Reward : Type w}
    [MeasurableSpace Env] [MeasurableSpace Action] [MeasurableSpace Reward]
    (algorithm : HistoryAlgorithm Action Reward)
    (environment : MeasurableHistoryEnvironment Env Action Reward) (n : Nat) :
    ProbabilityTheory.IsMarkovKernel
      (measurableEnvironmentHistoryStepKernel algorithm environment n) := by
  unfold measurableEnvironmentHistoryStepKernel
  infer_instance

theorem measurableEnvironmentInitialPairKernel_apply
    {Env : Type u} {Action : Type v} {Reward : Type w}
    [MeasurableSpace Env] [MeasurableSpace Action] [MeasurableSpace Reward]
    (algorithm : HistoryAlgorithm Action Reward)
    (environment : MeasurableHistoryEnvironment Env Action Reward)
    (env : Env) :
    measurableEnvironmentInitialPairKernel algorithm environment env =
      algorithm.initialAction ⊗ₘ (environment.at env).initialFeedback := by
  rw [measurableEnvironmentInitialPairKernel,
    ProbabilityTheory.Kernel.compProd_apply_eq_compProd_sectR,
    ProbabilityTheory.Kernel.const_apply]
  rfl

theorem measurableEnvironmentHistoryStepKernel_apply
    {Env : Type u} {Action : Type v} {Reward : Type w}
    [MeasurableSpace Env] [MeasurableSpace Action] [MeasurableSpace Reward]
    (algorithm : HistoryAlgorithm Action Reward)
    (environment : MeasurableHistoryEnvironment Env Action Reward)
    (n : Nat) (env : Env)
    (history : History.FinitePairHistory Action Reward n) :
    measurableEnvironmentHistoryStepKernel algorithm environment n
        (env, history) =
      historyStepKernel algorithm (environment.at env) n history := by
  rw [measurableEnvironmentHistoryStepKernel, historyStepKernel,
    ProbabilityTheory.Kernel.compProd_apply_eq_compProd_sectR,
    ProbabilityTheory.Kernel.compProd_apply_eq_compProd_sectR]
  rfl

/-- Environment coordinate stored in a finite internal state prefix. -/
def measurableTrajectoryPrefixEnvironment
    {Env : Type u} {Action : Type v} {Reward : Type w} {n : Nat}
    (statePrefix : (i : Finset.Iic n) -> Env × (Action × Reward)) : Env :=
  (statePrefix ⟨0, Finset.mem_Iic.mpr (Nat.zero_le n)⟩).1

/-- Pair history stored after the dummy zeroth internal state. -/
def measurableTrajectoryPrefixHistory
    {Env : Type u} {Action : Type v} {Reward : Type w} {n : Nat}
    (statePrefix : (i : Finset.Iic (n + 1)) ->
      Env × (Action × Reward)) :
    History.FinitePairHistory Action Reward n :=
  fun i => (statePrefix
    ⟨i.1 + 1, Finset.mem_Iic.mpr
      (Nat.succ_le_succ (Finset.mem_Iic.mp i.2))⟩).2

theorem measurable_measurableTrajectoryPrefixEnvironment
    {Env : Type u} {Action : Type v} {Reward : Type w} {n : Nat}
    [MeasurableSpace Env] [MeasurableSpace Action] [MeasurableSpace Reward] :
    Measurable
      (measurableTrajectoryPrefixEnvironment
        (Env := Env) (Action := Action) (Reward := Reward) (n := n)) :=
  measurable_fst.comp
    (measurable_pi_apply
      (⟨0, Finset.mem_Iic.mpr (Nat.zero_le n)⟩ : Finset.Iic n))

theorem measurable_measurableTrajectoryPrefixHistory
    {Env : Type u} {Action : Type v} {Reward : Type w} {n : Nat}
    [MeasurableSpace Env] [MeasurableSpace Action] [MeasurableSpace Reward] :
    Measurable
      (measurableTrajectoryPrefixHistory
        (Env := Env) (Action := Action) (Reward := Reward) (n := n)) := by
  exact measurable_pi_lambda _ (fun i => measurable_snd.comp
    (measurable_pi_apply
      (⟨i.1 + 1, Finset.mem_Iic.mpr
        (Nat.succ_le_succ (Finset.mem_Iic.mp i.2))⟩ :
          Finset.Iic (n + 1))))

theorem measurable_measurableTrajectoryPrefixEnvironmentHistory
    {Env : Type u} {Action : Type v} {Reward : Type w} {n : Nat}
    [MeasurableSpace Env] [MeasurableSpace Action] [MeasurableSpace Reward] :
    Measurable
      (fun statePrefix : (i : Finset.Iic (n + 1)) ->
          Env × (Action × Reward) =>
        (measurableTrajectoryPrefixEnvironment (n := n + 1) statePrefix,
          measurableTrajectoryPrefixHistory (n := n) statePrefix)) := by
  exact
    (measurable_measurableTrajectoryPrefixEnvironment
      (Env := Env) (Action := Action) (Reward := Reward) (n := n + 1)).prodMk
    (measurable_measurableTrajectoryPrefixHistory
      (Env := Env) (Action := Action) (Reward := Reward) (n := n))

/-- Attach a kernel output to the environment already present in its input. -/
noncomputable def retainEnvironmentKernel
    {Input : Type u} {Env : Type v} {Output : Type w}
    [MeasurableSpace Input] [MeasurableSpace Env] [MeasurableSpace Output]
    (env : Input -> Env) (_henv : Measurable env)
    (kernel : ProbabilityTheory.Kernel Input Output) :
    ProbabilityTheory.Kernel Input (Env × Output) :=
  (ProbabilityTheory.Kernel.id ×ₖ kernel).map
    (fun inputOutput => (env inputOutput.1, inputOutput.2))

instance instRetainEnvironmentKernelIsMarkov
    {Input : Type u} {Env : Type v} {Output : Type w}
    [MeasurableSpace Input] [MeasurableSpace Env] [MeasurableSpace Output]
    (env : Input -> Env) (henv : Measurable env)
    (kernel : ProbabilityTheory.Kernel Input Output)
    [ProbabilityTheory.IsMarkovKernel kernel] :
    ProbabilityTheory.IsMarkovKernel
      (retainEnvironmentKernel env henv kernel) := by
  unfold retainEnvironmentKernel
  exact ProbabilityTheory.Kernel.IsMarkovKernel.map _
    ((henv.comp measurable_fst).prodMk measurable_snd)

theorem retainEnvironmentKernel_apply
    {Input : Type u} {Env : Type v} {Output : Type w}
    [MeasurableSpace Input] [MeasurableSpace Env] [MeasurableSpace Output]
    (env : Input -> Env) (henv : Measurable env)
    (kernel : ProbabilityTheory.Kernel Input Output)
    [ProbabilityTheory.IsMarkovKernel kernel] (input : Input) :
    retainEnvironmentKernel env henv kernel input =
      (kernel input).map (Prod.mk (env input)) := by
  let embed : Output -> Env × Output := fun output => (env input, output)
  have hembed : Measurable embed := measurable_const.prodMk measurable_id
  have hmap : Measurable
      (fun inputOutput : Input × Output =>
        (env inputOutput.1, inputOutput.2)) :=
    (henv.comp measurable_fst).prodMk measurable_snd
  change retainEnvironmentKernel env henv kernel input =
    (kernel input).map embed
  ext event hevent
  rw [retainEnvironmentKernel,
    ProbabilityTheory.Kernel.map_apply' _ hmap _ hevent,
    ProbabilityTheory.Kernel.id_prod_apply' kernel input
      (hevent.preimage hmap),
    Measure.map_apply hembed hevent]
  rfl

theorem retainEnvironmentKernel_map_snd
    {Input : Type u} {Env : Type v} {Output : Type w}
    [MeasurableSpace Input] [MeasurableSpace Env] [MeasurableSpace Output]
    (env : Input -> Env) (henv : Measurable env)
    (kernel : ProbabilityTheory.Kernel Input Output)
    [ProbabilityTheory.IsMarkovKernel kernel] :
    (retainEnvironmentKernel env henv kernel).map Prod.snd = kernel := by
  ext input event hevent
  have hmk : Measurable (Prod.mk (env input) : Output -> Env × Output) :=
    measurable_const.prodMk measurable_id
  have hcomp : Prod.snd ∘ (Prod.mk (env input) : Output -> Env × Output) = id :=
    rfl
  rw [ProbabilityTheory.Kernel.map_apply _ measurable_snd,
    retainEnvironmentKernel_apply,
    Measure.map_map measurable_snd hmk,
    hcomp,
    Measure.map_id]

/-- Stable internal step family used by the measurable trajectory producer. -/
noncomputable def canonicalMeasurableEnvironmentStepKernel
    {Env : Type u} {Action : Type v} {Reward : Type w}
    [MeasurableSpace Env] [MeasurableSpace Action] [MeasurableSpace Reward]
    (algorithm : HistoryAlgorithm Action Reward)
    (environment : MeasurableHistoryEnvironment Env Action Reward) :
    (n : Nat) -> ProbabilityTheory.Kernel
      ((i : Finset.Iic n) -> Env × (Action × Reward))
      (Env × (Action × Reward))
  | 0 => retainEnvironmentKernel measurableTrajectoryPrefixEnvironment
      measurable_measurableTrajectoryPrefixEnvironment
      ((measurableEnvironmentInitialPairKernel algorithm environment).comap
        measurableTrajectoryPrefixEnvironment
        measurable_measurableTrajectoryPrefixEnvironment)
  | n + 1 => retainEnvironmentKernel measurableTrajectoryPrefixEnvironment
      (measurable_measurableTrajectoryPrefixEnvironment (n := n + 1))
      ((measurableEnvironmentHistoryStepKernel algorithm environment n).comap
        (fun statePrefix : (i : Finset.Iic (n + 1)) ->
            Env × (Action × Reward) =>
          (measurableTrajectoryPrefixEnvironment (n := n + 1) statePrefix,
            measurableTrajectoryPrefixHistory (n := n) statePrefix))
        measurable_measurableTrajectoryPrefixEnvironmentHistory)

instance instCanonicalMeasurableEnvironmentStepKernelIsMarkov
    {Env : Type u} {Action : Type v} {Reward : Type w}
    [MeasurableSpace Env] [MeasurableSpace Action] [MeasurableSpace Reward]
    (algorithm : HistoryAlgorithm Action Reward)
    (environment : MeasurableHistoryEnvironment Env Action Reward) (n : Nat) :
    ProbabilityTheory.IsMarkovKernel
      (canonicalMeasurableEnvironmentStepKernel algorithm environment n) := by
  cases n with
  | zero =>
      unfold canonicalMeasurableEnvironmentStepKernel
      infer_instance
  | succ n =>
      unfold canonicalMeasurableEnvironmentStepKernel
      infer_instance

/-- Dropping the retained environment recovers the visible pair step law. -/
theorem canonicalMeasurableEnvironmentStepKernel_succ_apply_map_snd
    {Env : Type u} {Action : Type v} {Reward : Type w}
    [MeasurableSpace Env] [MeasurableSpace Action] [MeasurableSpace Reward]
    (algorithm : HistoryAlgorithm Action Reward)
    (environment : MeasurableHistoryEnvironment Env Action Reward) (n : Nat)
    (statePrefix : (i : Finset.Iic (n + 1)) -> Env × (Action × Reward)) :
    (canonicalMeasurableEnvironmentStepKernel algorithm environment (n + 1)
        statePrefix).map Prod.snd =
      historyStepKernel algorithm
        (environment.at (measurableTrajectoryPrefixEnvironment statePrefix)) n
        (measurableTrajectoryPrefixHistory statePrefix) := by
  rw [← ProbabilityTheory.Kernel.map_apply _ measurable_snd,
    show canonicalMeasurableEnvironmentStepKernel algorithm environment (n + 1) =
        retainEnvironmentKernel measurableTrajectoryPrefixEnvironment
          (measurable_measurableTrajectoryPrefixEnvironment (n := n + 1))
          ((measurableEnvironmentHistoryStepKernel algorithm environment n).comap
            (fun statePrefix =>
              (measurableTrajectoryPrefixEnvironment statePrefix,
                measurableTrajectoryPrefixHistory statePrefix))
            measurable_measurableTrajectoryPrefixEnvironmentHistory) from rfl,
    retainEnvironmentKernel_map_snd,
    ProbabilityTheory.Kernel.comap_apply,
    measurableEnvironmentHistoryStepKernel_apply]

/-- Dummy time-zero prefix used only to seed `Kernel.traj`. -/
noncomputable def measurableEnvironmentInitialStatePrefix
    {Env : Type u} {Action : Type v} {Reward : Type w}
    [Nonempty Action] [Nonempty Reward] (env : Env) :
    (i : Finset.Iic 0) -> Env × (Action × Reward) :=
  fun _ => (env, Classical.ofNonempty)

theorem measurable_measurableEnvironmentInitialStatePrefix
    {Env : Type u} {Action : Type v} {Reward : Type w}
    [MeasurableSpace Env] [MeasurableSpace Action] [MeasurableSpace Reward]
    [Nonempty Action] [Nonempty Reward] :
    Measurable
      (measurableEnvironmentInitialStatePrefix
        (Env := Env) (Action := Action) (Reward := Reward)) := by
  exact measurable_pi_lambda _ (fun _ =>
    measurable_id.prodMk measurable_const)

/-- Pair trace obtained by dropping the dummy internal time-zero state. -/
def measurableEnvironmentPairTrace
    {Env : Type u} {Action : Type v} {Reward : Type w}
    (trajectory : (n : Nat) -> Env × (Action × Reward)) :
    (n : Nat) -> Action × Reward :=
  fun n => (trajectory (n + 1)).2

theorem measurable_measurableEnvironmentPairTrace
    {Env : Type u} {Action : Type v} {Reward : Type w}
    [MeasurableSpace Env] [MeasurableSpace Action] [MeasurableSpace Reward] :
    Measurable
      (measurableEnvironmentPairTrace
        (Env := Env) (Action := Action) (Reward := Reward)) := by
  exact measurable_pi_lambda _ (fun n =>
    measurable_snd.comp (measurable_pi_apply (n + 1)))

/--
Complete measurable pair-trajectory kernel generated from the joint feedback
environment, with no externally supplied trajectory-kernel premise.
-/
noncomputable def canonicalMeasurableEnvironmentTrajectoryKernel
    {Env : Type u} {Action : Type v} {Reward : Type w}
    [MeasurableSpace Env] [MeasurableSpace Action] [MeasurableSpace Reward]
    [Nonempty Action] [Nonempty Reward]
    (algorithm : HistoryAlgorithm Action Reward)
    (environment : MeasurableHistoryEnvironment Env Action Reward) :
    ProbabilityTheory.Kernel Env ((n : Nat) -> Action × Reward) :=
  ((ProbabilityTheory.Kernel.traj
      (canonicalMeasurableEnvironmentStepKernel algorithm environment) 0).comap
      measurableEnvironmentInitialStatePrefix
      measurable_measurableEnvironmentInitialStatePrefix).map
    measurableEnvironmentPairTrace

instance instCanonicalMeasurableEnvironmentTrajectoryKernelIsMarkov
    {Env : Type u} {Action : Type v} {Reward : Type w}
    [MeasurableSpace Env] [MeasurableSpace Action] [MeasurableSpace Reward]
    [Nonempty Action] [Nonempty Reward]
    (algorithm : HistoryAlgorithm Action Reward)
    (environment : MeasurableHistoryEnvironment Env Action Reward) :
    ProbabilityTheory.IsMarkovKernel
      (canonicalMeasurableEnvironmentTrajectoryKernel algorithm environment) := by
  unfold canonicalMeasurableEnvironmentTrajectoryKernel
  exact ProbabilityTheory.Kernel.IsMarkovKernel.map _
    measurable_measurableEnvironmentPairTrace

theorem canonicalMeasurableEnvironmentTrajectoryKernel_apply
    {Env : Type u} {Action : Type v} {Reward : Type w}
    [MeasurableSpace Env] [MeasurableSpace Action] [MeasurableSpace Reward]
    [Nonempty Action] [Nonempty Reward]
    (algorithm : HistoryAlgorithm Action Reward)
    (environment : MeasurableHistoryEnvironment Env Action Reward) (env : Env) :
    canonicalMeasurableEnvironmentTrajectoryKernel algorithm environment env =
      (ProbabilityTheory.Kernel.traj
        (canonicalMeasurableEnvironmentStepKernel algorithm environment) 0
        (measurableEnvironmentInitialStatePrefix
          (Action := Action) (Reward := Reward) env)).map
        measurableEnvironmentPairTrace := by
  rw [canonicalMeasurableEnvironmentTrajectoryKernel,
    ProbabilityTheory.Kernel.map_apply _
      measurable_measurableEnvironmentPairTrace,
    ProbabilityTheory.Kernel.comap_apply]

theorem measurableTrajectoryPrefixEnvironment_initialStatePrefix
    {Env : Type u} {Action : Type v} {Reward : Type w}
    [Nonempty Action] [Nonempty Reward] (env : Env) :
    measurableTrajectoryPrefixEnvironment
        (measurableEnvironmentInitialStatePrefix
          (Action := Action) (Reward := Reward) env) = env := by
  rfl

/-- Under a fixed input environment, every finite internal prefix retains it. -/
theorem measurableTrajectoryPrefixEnvironment_ae_eq_of_traj
    {Env : Type u} {Action : Type v} {Reward : Type w}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSpace Reward]
    [Nonempty Action] [Nonempty Reward]
    (algorithm : HistoryAlgorithm Action Reward)
    (environment : MeasurableHistoryEnvironment Env Action Reward)
    (env : Env) (n : Nat) :
    (measurableTrajectoryPrefixEnvironment
      (Env := Env) (Action := Action) (Reward := Reward) (n := n + 1)) =ᵐ[
        ((ProbabilityTheory.Kernel.traj
          (X := fun _ : Nat => Env × (Action × Reward))
          (canonicalMeasurableEnvironmentStepKernel algorithm environment) 0)
          (measurableEnvironmentInitialStatePrefix
            (Action := Action) (Reward := Reward) env)).map
          (Preorder.frestrictLe (n + 1))]
      fun _ : ((i : Finset.Iic (n + 1)) -> Env × (Action × Reward)) => env := by
  let stepKernel :=
    canonicalMeasurableEnvironmentStepKernel algorithm environment
  let seed := measurableEnvironmentInitialStatePrefix
    (Env := Env) (Action := Action) (Reward := Reward)
  let internalMeasure : Measure ((k : Nat) -> Env × (Action × Reward)) :=
    ProbabilityTheory.Kernel.traj stepKernel 0 (seed env)
  let restrictInternal :
      ((k : Nat) -> Env × (Action × Reward)) ->
        ((i : Finset.Iic (n + 1)) -> Env × (Action × Reward)) :=
    Preorder.frestrictLe (n + 1)
  have hrestrictInternal : Measurable restrictInternal :=
    Preorder.measurable_frestrictLe (n + 1)
  change ∀ᵐ statePrefix ∂internalMeasure.map restrictInternal,
      measurableTrajectoryPrefixEnvironment
        (Env := Env) (Action := Action) (Reward := Reward) statePrefix = env
  apply (ae_map_iff (μ := internalMeasure) hrestrictInternal.aemeasurable
    (by
      change MeasurableSet
        (measurableTrajectoryPrefixEnvironment ⁻¹' {env})
      exact (measurableSet_singleton env).preimage
        measurable_measurableTrajectoryPrefixEnvironment)).2
  let updateInitial := fun trajectory : (k : Nat) -> Env × (Action × Reward) =>
    Function.updateFinset trajectory (Finset.Iic 0) (seed env)
  have hupdate : internalMeasure.map updateInitial = internalMeasure := by
    dsimp [internalMeasure, updateInitial, stepKernel, seed]
    exact ProbabilityTheory.Kernel.traj_map_updateFinset
      (X := fun _ : Nat => Env × (Action × Reward))
      (κ := canonicalMeasurableEnvironmentStepKernel algorithm environment)
      (measurableEnvironmentInitialStatePrefix
        (Action := Action) (Reward := Reward) env)
  rw [← hupdate]
  apply (ae_map_iff (μ := internalMeasure) (f := updateInitial)
    (by fun_prop)
    (by
      change MeasurableSet
        ((measurableTrajectoryPrefixEnvironment ∘
          restrictInternal) ⁻¹' {env})
      exact (measurableSet_singleton env).preimage
        (measurable_measurableTrajectoryPrefixEnvironment.comp
          hrestrictInternal))).2
  filter_upwards [] with trajectory
  rfl

/-- The generated trajectory kernel has the configured initial pair law. -/
theorem canonicalMeasurableEnvironmentTrajectoryKernel_map_eval_zero
    {Env : Type u} {Action : Type v} {Reward : Type w}
    [MeasurableSpace Env] [MeasurableSpace Action] [MeasurableSpace Reward]
    [Nonempty Action] [Nonempty Reward]
    (algorithm : HistoryAlgorithm Action Reward)
    (environment : MeasurableHistoryEnvironment Env Action Reward) :
    (canonicalMeasurableEnvironmentTrajectoryKernel algorithm environment).map
        (fun trajectory => trajectory 0) =
      measurableEnvironmentInitialPairKernel algorithm environment := by
  let stepKernel :=
    canonicalMeasurableEnvironmentStepKernel algorithm environment
  let seed := measurableEnvironmentInitialStatePrefix
    (Env := Env) (Action := Action) (Reward := Reward)
  let pairTrace := measurableEnvironmentPairTrace
    (Env := Env) (Action := Action) (Reward := Reward)
  let evalPairZero := fun trajectory : (n : Nat) -> Action × Reward =>
    trajectory 0
  let evalStateOne := fun trajectory : (n : Nat) ->
      Env × (Action × Reward) => trajectory 1
  let prefixEnv := measurableTrajectoryPrefixEnvironment
    (Env := Env) (Action := Action) (Reward := Reward) (n := 0)
  have hseed : Measurable seed :=
    measurable_measurableEnvironmentInitialStatePrefix
  have hpairTrace : Measurable pairTrace :=
    measurable_measurableEnvironmentPairTrace
  have hevalPairZero : Measurable evalPairZero := measurable_pi_apply 0
  have hevalStateOne : Measurable evalStateOne := measurable_pi_apply 1
  have hprefixEnv : Measurable prefixEnv :=
    measurable_measurableTrajectoryPrefixEnvironment
  have hcompDrop : evalPairZero ∘ pairTrace = Prod.snd ∘ evalStateOne := by
    rfl
  have hseedPrefix : prefixEnv ∘ seed = id := by
    funext env
    exact measurableTrajectoryPrefixEnvironment_initialStatePrefix env
  calc
    (canonicalMeasurableEnvironmentTrajectoryKernel algorithm environment).map
        evalPairZero =
        (((ProbabilityTheory.Kernel.traj stepKernel 0).comap seed hseed).map
          pairTrace).map evalPairZero := by
            rfl
    _ = ((ProbabilityTheory.Kernel.traj stepKernel 0).comap seed hseed).map
          (evalPairZero ∘ pairTrace) := by
            rw [ProbabilityTheory.Kernel.map_comp_right _ hpairTrace
              hevalPairZero]
    _ = ((ProbabilityTheory.Kernel.traj stepKernel 0).comap seed hseed).map
          (Prod.snd ∘ evalStateOne) := by rw [hcompDrop]
    _ = (((ProbabilityTheory.Kernel.traj stepKernel 0).comap seed hseed).map
          evalStateOne).map Prod.snd := by
            rw [← ProbabilityTheory.Kernel.map_comp_right _ hevalStateOne
              measurable_snd]
    _ = (((ProbabilityTheory.Kernel.traj stepKernel 0).map evalStateOne).comap
          seed hseed).map Prod.snd := by
            rw [ProbabilityTheory.Kernel.comap_map_comm _ hseed hevalStateOne]
    _ = ((stepKernel 0).comap seed hseed).map Prod.snd := by
            rw [ProbabilityTheory.Kernel.map_traj_succ_self]
    _ = (((stepKernel 0).map Prod.snd).comap seed hseed) := by
            rw [ProbabilityTheory.Kernel.comap_map_comm _ hseed measurable_snd]
    _ = ((measurableEnvironmentInitialPairKernel algorithm environment).comap
          prefixEnv hprefixEnv).comap seed hseed := by
            rw [show stepKernel 0 = retainEnvironmentKernel prefixEnv hprefixEnv
                ((measurableEnvironmentInitialPairKernel algorithm environment).comap
                  prefixEnv hprefixEnv) from rfl,
              retainEnvironmentKernel_map_snd]
    _ = (measurableEnvironmentInitialPairKernel algorithm environment).comap
          (prefixEnv ∘ seed) (hprefixEnv.comp hseed) := by
            rw [ProbabilityTheory.Kernel.comap_comp_right]
    _ = (measurableEnvironmentInitialPairKernel algorithm environment).comap
          id measurable_id := by
            congr 1
    _ = measurableEnvironmentInitialPairKernel algorithm environment :=
          ProbabilityTheory.Kernel.comap_id _

/-- Joint finite-prefix/next-pair law of the projected measurable trajectory. -/
theorem canonicalMeasurableEnvironmentTrajectoryKernel_map_prefix_next_eq_compProd
    {Env : Type u} {Action : Type v} {Reward : Type w}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [StandardBorelSpace Action] [Nonempty Action]
    [MeasurableSpace Reward] [StandardBorelSpace Reward] [Nonempty Reward]
    (algorithm : HistoryAlgorithm Action Reward)
    (environment : MeasurableHistoryEnvironment Env Action Reward)
    (env : Env) (n : Nat) :
    (canonicalMeasurableEnvironmentTrajectoryKernel algorithm environment env).map
        (fun trajectory =>
          (Preorder.frestrictLe n trajectory, trajectory (n + 1))) =
      (canonicalMeasurableEnvironmentTrajectoryKernel algorithm environment env).map
          (Preorder.frestrictLe n) ⊗ₘ
        historyStepKernel algorithm (environment.at env) n := by
  let stepKernel :=
    canonicalMeasurableEnvironmentStepKernel algorithm environment
  let seed := measurableEnvironmentInitialStatePrefix
    (Env := Env) (Action := Action) (Reward := Reward)
  let internalMeasure : Measure ((k : Nat) -> Env × (Action × Reward)) :=
    ProbabilityTheory.Kernel.traj stepKernel 0 (seed env)
  let internalPrefix :
      ((k : Nat) -> Env × (Action × Reward)) ->
        ((i : Finset.Iic (n + 1)) -> Env × (Action × Reward)) :=
    Preorder.frestrictLe (n + 1)
  let prefixHistory := measurableTrajectoryPrefixHistory
    (Env := Env) (Action := Action) (Reward := Reward) (n := n)
  let pairTrace := measurableEnvironmentPairTrace
    (Env := Env) (Action := Action) (Reward := Reward)
  let targetKernel := historyStepKernel algorithm (environment.at env) n
  let prefixMeasure :
      Measure ((i : Finset.Iic (n + 1)) -> Env × (Action × Reward)) :=
    ProbabilityTheory.Kernel.partialTraj
      (X := fun _ : Nat => Env × (Action × Reward))
      stepKernel 0 (n + 1) (seed env)
  have hinternalPrefix :
      internalMeasure.map internalPrefix = prefixMeasure := by
    dsimp [internalMeasure, internalPrefix, prefixMeasure]
    exact ProbabilityTheory.Kernel.traj_map_frestrictLe_apply
      (X := fun _ : Nat => Env × (Action × Reward)) (κ := stepKernel)
      0 (n + 1) (seed env)
  have henvPrefix : ∀ᵐ statePrefix ∂prefixMeasure,
      measurableTrajectoryPrefixEnvironment statePrefix = env := by
    have h := measurableTrajectoryPrefixEnvironment_ae_eq_of_traj
      algorithm environment env n
    change ∀ᵐ statePrefix ∂internalMeasure.map internalPrefix,
      measurableTrajectoryPrefixEnvironment statePrefix = env at h
    rwa [hinternalPrefix] at h
  have hprefixHistory : Measurable prefixHistory :=
    measurable_measurableTrajectoryPrefixHistory
  have hstepMap :
      (stepKernel (n + 1)).map Prod.snd =ᵐ[prefixMeasure]
        targetKernel.comap prefixHistory hprefixHistory := by
    filter_upwards [henvPrefix] with statePrefix henv
    rw [ProbabilityTheory.Kernel.map_apply _ measurable_snd,
      ProbabilityTheory.Kernel.comap_apply]
    simpa [stepKernel, targetKernel, prefixHistory, henv] using
      (canonicalMeasurableEnvironmentStepKernel_succ_apply_map_snd
        algorithm environment n statePrefix)
  have hinternalJoint :
      prefixMeasure ⊗ₘ stepKernel (n + 1) =
        internalMeasure.map
          (fun trajectory =>
            (internalPrefix trajectory, trajectory (n + 2))) := by
    dsimp [prefixMeasure, internalMeasure, internalPrefix]
    simpa [Nat.add_assoc] using
      (ProbabilityTheory.Kernel.partialTraj_compProd_eq_map_traj
        (X := fun _ : Nat => Env × (Action × Reward))
        (κ := stepKernel) (a := 0) (b := n + 1) (Nat.zero_le (n + 1))
        (x₀ := seed env))
  let mapHistory := fun sample :
      (((i : Finset.Iic (n + 1)) -> Env × (Action × Reward)) ×
        (Action × Reward)) => (prefixHistory sample.1, sample.2)
  let internalVisibleJoint := fun trajectory :
      (k : Nat) -> Env × (Action × Reward) =>
        (prefixHistory (internalPrefix trajectory), (trajectory (n + 2)).2)
  have hproductVisible :
      prefixMeasure.map prefixHistory ⊗ₘ targetKernel =
        internalMeasure.map internalVisibleJoint := by
    calc
      prefixMeasure.map prefixHistory ⊗ₘ targetKernel =
          (prefixMeasure ⊗ₘ
            targetKernel.comap prefixHistory hprefixHistory).map mapHistory := by
            simpa [mapHistory] using
              (map_compProd_comap_history prefixMeasure prefixHistory
                hprefixHistory targetKernel).symm
      _ = (prefixMeasure ⊗ₘ (stepKernel (n + 1)).map Prod.snd).map
          mapHistory := by
            rw [Measure.compProd_congr hstepMap.symm]
      _ = ((prefixMeasure ⊗ₘ stepKernel (n + 1)).map
          (Prod.map id Prod.snd)).map mapHistory := by
            rw [← Measure.compProd_map measurable_snd]
      _ = (prefixMeasure ⊗ₘ stepKernel (n + 1)).map
          (mapHistory ∘ Prod.map id Prod.snd) := by
            rw [Measure.map_map]
            all_goals fun_prop
      _ = (internalMeasure.map
          (fun trajectory =>
            (internalPrefix trajectory, trajectory (n + 2)))).map
          (mapHistory ∘ Prod.map id Prod.snd) := by rw [hinternalJoint]
      _ = internalMeasure.map internalVisibleJoint := by
            rw [Measure.map_map]
            · congr 1
            · fun_prop
            · fun_prop
  calc
    (canonicalMeasurableEnvironmentTrajectoryKernel algorithm environment env).map
        (fun trajectory =>
          (Preorder.frestrictLe n trajectory, trajectory (n + 1))) =
        internalMeasure.map internalVisibleJoint := by
          rw [canonicalMeasurableEnvironmentTrajectoryKernel_apply,
            Measure.map_map]
          · congr 1
          · fun_prop
          · exact measurable_measurableEnvironmentPairTrace
    _ = prefixMeasure.map prefixHistory ⊗ₘ targetKernel := hproductVisible.symm
    _ = (canonicalMeasurableEnvironmentTrajectoryKernel algorithm environment env).map
          (Preorder.frestrictLe n) ⊗ₘ targetKernel := by
          congr 1
          rw [canonicalMeasurableEnvironmentTrajectoryKernel_apply,
            Measure.map_map, ← hinternalPrefix, Measure.map_map]
          · congr 1
          · exact hprefixHistory
          · fun_prop
          · fun_prop
          · exact measurable_measurableEnvironmentPairTrace

/-- The projected trajectory has the configured shifted successor pair law. -/
theorem canonicalMeasurableEnvironmentTrajectoryKernel_condDistrib_succ
    {Env : Type u} {Action : Type v} {Reward : Type w}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [StandardBorelSpace Action] [Nonempty Action]
    [MeasurableSpace Reward] [StandardBorelSpace Reward] [Nonempty Reward]
    (algorithm : HistoryAlgorithm Action Reward)
    (environment : MeasurableHistoryEnvironment Env Action Reward)
    (env : Env) (n : Nat) :
    ProbabilityTheory.condDistrib
        (fun trajectory : (k : Nat) -> Action × Reward => trajectory (n + 1))
        (Preorder.frestrictLe n)
        (canonicalMeasurableEnvironmentTrajectoryKernel algorithm environment
          env) =ᵐ[
            (canonicalMeasurableEnvironmentTrajectoryKernel algorithm environment
              env).map (Preorder.frestrictLe n)]
      historyStepKernel algorithm (environment.at env) n := by
  apply ProbabilityTheory.condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
    (Preorder.measurable_frestrictLe n) (measurable_pi_apply (n + 1))
  exact
    canonicalMeasurableEnvironmentTrajectoryKernel_map_prefix_next_eq_compProd
      algorithm environment env n

/--
The generated measurable trajectory kernel has the canonical fixed-environment
law once its shifted successor conditional laws are identified.  The initial
law is discharged internally by the preceding theorem.
-/
theorem canonicalMeasurableEnvironmentTrajectoryKernel_apply_eq_canonical_of_step_condDistrib
    {Env : Type u} {Action : Type v} {Reward : Type w}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [StandardBorelSpace Action] [Nonempty Action]
    [MeasurableSpace Reward] [StandardBorelSpace Reward] [Nonempty Reward]
    (algorithm : HistoryAlgorithm Action Reward)
    (environment : MeasurableHistoryEnvironment Env Action Reward)
    (env : Env)
    (hstep : forall n,
      ProbabilityTheory.condDistrib
          (fun trajectory : (k : Nat) -> Action × Reward => trajectory (n + 1))
          (Preorder.frestrictLe n)
          (canonicalMeasurableEnvironmentTrajectoryKernel algorithm environment
            env) =ᵐ[
              (canonicalMeasurableEnvironmentTrajectoryKernel algorithm environment
                env).map (Preorder.frestrictLe n)]
        historyStepKernel algorithm (environment.at env) n) :
    canonicalMeasurableEnvironmentTrajectoryKernel algorithm environment env =
      canonicalHistoryTrajectoryMeasure algorithm (environment.at env) := by
  let trajectoryMeasure :=
    canonicalMeasurableEnvironmentTrajectoryKernel algorithm environment env
  let initialPair :=
    algorithm.initialAction ⊗ₘ (environment.at env).initialFeedback
  have hzero :
      Measure.map
          (fun trajectory : (k : Nat) -> Action × Reward => trajectory 0)
          trajectoryMeasure = initialPair := by
    have hkernel := congrArg
      (fun kernel : ProbabilityTheory.Kernel Env (Action × Reward) => kernel env)
      (canonicalMeasurableEnvironmentTrajectoryKernel_map_eval_zero
        algorithm environment)
    change
      ((canonicalMeasurableEnvironmentTrajectoryKernel algorithm environment).map
          (fun trajectory => trajectory 0)) env =
        measurableEnvironmentInitialPairKernel algorithm environment env at hkernel
    rw [ProbabilityTheory.Kernel.map_apply _ (measurable_pi_apply 0),
      measurableEnvironmentInitialPairKernel_apply] at hkernel
    exact hkernel
  simpa [trajectoryMeasure, initialPair, canonicalHistoryTrajectoryMeasure] using
    (RewardKernel.rewardTrace_map_eq_trajMeasure_of_condDistrib
      (mu := trajectoryMeasure) (mu0 := initialPair)
      (reward := fun trajectory : (k : Nat) -> Action × Reward => trajectory)
      (hreward := fun t => measurable_pi_apply t)
      (kernel := fun n => historyStepKernel algorithm (environment.at env) n)
      hzero hstep)

/-- The generated measurable trajectory kernel is pointwise canonical. -/
theorem canonicalMeasurableEnvironmentTrajectoryKernel_apply_eq_canonical
    {Env : Type u} {Action : Type v} {Reward : Type w}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [StandardBorelSpace Action] [Nonempty Action]
    [MeasurableSpace Reward] [StandardBorelSpace Reward] [Nonempty Reward]
    (algorithm : HistoryAlgorithm Action Reward)
    (environment : MeasurableHistoryEnvironment Env Action Reward) (env : Env) :
    canonicalMeasurableEnvironmentTrajectoryKernel algorithm environment env =
      canonicalHistoryTrajectoryMeasure algorithm (environment.at env) := by
  exact
    canonicalMeasurableEnvironmentTrajectoryKernel_apply_eq_canonical_of_step_condDistrib
      algorithm environment env
      (canonicalMeasurableEnvironmentTrajectoryKernel_condDistrib_succ
        algorithm environment env)

/--
Finite-prefix probability matching from jointly measurable actual/reference
feedback environments.  The only remaining process premise is the shifted
successor conditional law of the two generated `Kernel.traj` kernels.
-/
theorem finitePairReferencePolicySampler_condDistrib_action_ae_eq_bestAction_of_measurableEnvironment_stepCondDistrib
    {Env : Type u} {Action : Type v} {Reward : Type w}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [StandardBorelSpace Action] [Nonempty Action]
    [MeasurableSpace Reward] [StandardBorelSpace Reward] [Nonempty Reward]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (algorithm referenceAlgorithm : HistoryAlgorithm Action Reward)
    (environment : MeasurableHistoryEnvironment Env Action Reward)
    (absolutelyContinuous :
      HistoryAlgorithmAbsolutelyContinuous algorithm referenceAlgorithm)
    (hstep : forall env n,
      ProbabilityTheory.condDistrib
          (fun trajectory : (k : Nat) -> Action × Reward => trajectory (n + 1))
          (Preorder.frestrictLe n)
          (canonicalMeasurableEnvironmentTrajectoryKernel algorithm environment
            env) =ᵐ[
              (canonicalMeasurableEnvironmentTrajectoryKernel algorithm environment
                env).map (Preorder.frestrictLe n)]
        historyStepKernel algorithm (environment.at env) n)
    (hreferenceStep : forall env n,
      ProbabilityTheory.condDistrib
          (fun trajectory : (k : Nat) -> Action × Reward => trajectory (n + 1))
          (Preorder.frestrictLe n)
          (canonicalMeasurableEnvironmentTrajectoryKernel referenceAlgorithm
            environment env) =ᵐ[
              (canonicalMeasurableEnvironmentTrajectoryKernel referenceAlgorithm
                environment env).map (Preorder.frestrictLe n)]
        historyStepKernel referenceAlgorithm (environment.at env) n)
    (n : Nat) (bestAction : Env -> Action)
    (hbestAction : Measurable bestAction) :
    let trajectoryKernel :=
      canonicalMeasurableEnvironmentTrajectoryKernel algorithm environment
    let referenceTrajectoryKernel :=
      canonicalMeasurableEnvironmentTrajectoryKernel referenceAlgorithm environment
    let actualHistory := fun sample => History.finitePairHistoryOfTrace
      (environmentTrajectoryAction sample)
      (environmentTrajectoryReward sample) n
    let referenceHistory := fun sample => History.finitePairHistoryOfTrace
      (environmentTrajectoryAction sample)
      (environmentTrajectoryReward sample) n
    let policy := referenceActionKernel
      (prior ⊗ₘ referenceTrajectoryKernel) Prod.fst referenceHistory
      measurable_fst
      (History.measurable_finitePairHistoryOfTrace
        environmentTrajectoryAction environmentTrajectoryReward
        measurable_environmentTrajectoryAction_apply
        measurable_environmentTrajectoryReward_apply n)
      bestAction hbestAction
    let sampler := policySamplerMeasure
      (prior ⊗ₘ trajectoryKernel) actualHistory
      (History.measurable_finitePairHistoryOfTrace
        environmentTrajectoryAction environmentTrajectoryReward
        measurable_environmentTrajectoryAction_apply
        measurable_environmentTrajectoryReward_apply n) policy
    ProbabilityTheory.condDistrib policySamplerAction
        (policySamplerHistory actualHistory) sampler =ᵐ[
      sampler.map (policySamplerHistory actualHistory)]
      ProbabilityTheory.condDistrib
        (bestAction ∘ policySamplerEnv Prod.fst)
        (policySamplerHistory actualHistory) sampler := by
  exact
    finitePairReferencePolicySampler_condDistrib_action_ae_eq_bestAction_of_canonicalTrajectoryKernels
      prior algorithm referenceAlgorithm environment.at
      (canonicalMeasurableEnvironmentTrajectoryKernel algorithm environment)
      (canonicalMeasurableEnvironmentTrajectoryKernel referenceAlgorithm environment)
      (fun env =>
        canonicalMeasurableEnvironmentTrajectoryKernel_apply_eq_canonical_of_step_condDistrib
          algorithm environment env (hstep env))
      (fun env =>
        canonicalMeasurableEnvironmentTrajectoryKernel_apply_eq_canonical_of_step_condDistrib
          referenceAlgorithm environment env (hreferenceStep env))
      absolutelyContinuous n bestAction hbestAction

/--
Finite-prefix Thompson probability matching directly from a jointly measurable
feedback environment, with both trajectory kernels and their process laws
constructed internally.
-/
theorem finitePairReferencePolicySampler_condDistrib_action_ae_eq_bestAction_of_measurableEnvironment
    {Env : Type u} {Action : Type v} {Reward : Type w}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [StandardBorelSpace Action] [Nonempty Action]
    [MeasurableSpace Reward] [StandardBorelSpace Reward] [Nonempty Reward]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (algorithm referenceAlgorithm : HistoryAlgorithm Action Reward)
    (environment : MeasurableHistoryEnvironment Env Action Reward)
    (absolutelyContinuous :
      HistoryAlgorithmAbsolutelyContinuous algorithm referenceAlgorithm)
    (n : Nat) (bestAction : Env -> Action)
    (hbestAction : Measurable bestAction) :
    let trajectoryKernel :=
      canonicalMeasurableEnvironmentTrajectoryKernel algorithm environment
    let referenceTrajectoryKernel :=
      canonicalMeasurableEnvironmentTrajectoryKernel referenceAlgorithm environment
    let actualHistory := fun sample => History.finitePairHistoryOfTrace
      (environmentTrajectoryAction sample)
      (environmentTrajectoryReward sample) n
    let referenceHistory := fun sample => History.finitePairHistoryOfTrace
      (environmentTrajectoryAction sample)
      (environmentTrajectoryReward sample) n
    let policy := referenceActionKernel
      (prior ⊗ₘ referenceTrajectoryKernel) Prod.fst referenceHistory
      measurable_fst
      (History.measurable_finitePairHistoryOfTrace
        environmentTrajectoryAction environmentTrajectoryReward
        measurable_environmentTrajectoryAction_apply
        measurable_environmentTrajectoryReward_apply n)
      bestAction hbestAction
    let sampler := policySamplerMeasure
      (prior ⊗ₘ trajectoryKernel) actualHistory
      (History.measurable_finitePairHistoryOfTrace
        environmentTrajectoryAction environmentTrajectoryReward
        measurable_environmentTrajectoryAction_apply
        measurable_environmentTrajectoryReward_apply n) policy
    ProbabilityTheory.condDistrib policySamplerAction
        (policySamplerHistory actualHistory) sampler =ᵐ[
      sampler.map (policySamplerHistory actualHistory)]
      ProbabilityTheory.condDistrib
        (bestAction ∘ policySamplerEnv Prod.fst)
        (policySamplerHistory actualHistory) sampler := by
  exact
    finitePairReferencePolicySampler_condDistrib_action_ae_eq_bestAction_of_measurableEnvironment_stepCondDistrib
      prior algorithm referenceAlgorithm environment absolutelyContinuous
      (fun env n =>
        canonicalMeasurableEnvironmentTrajectoryKernel_condDistrib_succ
          algorithm environment env n)
      (fun env n =>
        canonicalMeasurableEnvironmentTrajectoryKernel_condDistrib_succ
          referenceAlgorithm environment env n)
      n bestAction hbestAction

end Thompson
end BanditRLProof
