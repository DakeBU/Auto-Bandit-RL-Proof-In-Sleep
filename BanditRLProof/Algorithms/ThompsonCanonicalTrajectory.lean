import BanditRLProof.Algorithms.ThompsonAlgorithmDensityProcess

/-!
# Canonical trajectory producer for history-based Thompson processes

This module realizes a `HistoryAlgorithm` interacting with one fixed
`HistoryEnvironment` on Mathlib's Ionescu-Tulcea `trajMeasure`.  It proves both
the combined action/reward process contract and the four split conditional-law
fields used by the environment-indexed Thompson density route.
-/

open MeasureTheory
open scoped ProbabilityTheory

universe u v w

namespace BanditRLProof
namespace Thompson

/-- The canonical Ionescu-Tulcea law of the observable action/reward pairs. -/
noncomputable def canonicalHistoryTrajectoryMeasure
    {Action : Type u} {Reward : Type v}
    [MeasurableSpace Action] [MeasurableSpace Reward]
    (algorithm : HistoryAlgorithm Action Reward)
    (environment : HistoryEnvironment Action Reward) :
    Measure ((n : Nat) -> Action × Reward) :=
  ProbabilityTheory.Kernel.trajMeasure
    (algorithm.initialAction ⊗ₘ environment.initialFeedback)
    (fun n => historyStepKernel algorithm environment n)

instance instCanonicalHistoryTrajectoryMeasureIsProbability
    {Action : Type u} {Reward : Type v}
    [MeasurableSpace Action] [MeasurableSpace Reward]
    (algorithm : HistoryAlgorithm Action Reward)
    (environment : HistoryEnvironment Action Reward) :
    IsProbabilityMeasure
      (canonicalHistoryTrajectoryMeasure algorithm environment) := by
  unfold canonicalHistoryTrajectoryMeasure
  infer_instance

/-- Action trace projected from the canonical pair trajectory. -/
def canonicalHistoryTrajectoryAction
    {Action : Type u} {Reward : Type v} :
    ((n : Nat) -> Action × Reward) -> ActionTrace Action :=
  fun trajectory n => (trajectory n).1

/-- Reward trace projected from the canonical pair trajectory. -/
def canonicalHistoryTrajectoryReward
    {Action : Type u} {Reward : Type v} :
    ((n : Nat) -> Action × Reward) -> RewardTrace Reward :=
  fun trajectory n => (trajectory n).2

theorem measurable_canonicalHistoryTrajectoryAction_apply
    {Action : Type u} {Reward : Type v}
    [MeasurableSpace Action] [MeasurableSpace Reward] (n : Nat) :
    Measurable (fun trajectory : (k : Nat) -> Action × Reward =>
      canonicalHistoryTrajectoryAction trajectory n) :=
  measurable_fst.comp (measurable_pi_apply n)

theorem measurable_canonicalHistoryTrajectoryReward_apply
    {Action : Type u} {Reward : Type v}
    [MeasurableSpace Action] [MeasurableSpace Reward] (n : Nat) :
    Measurable (fun trajectory : (k : Nat) -> Action × Reward =>
      canonicalHistoryTrajectoryReward trajectory n) :=
  measurable_snd.comp (measurable_pi_apply n)

theorem canonicalHistoryTrajectory_initialPair_map_eq
    {Action : Type u} {Reward : Type v}
    [MeasurableSpace Action] [MeasurableSpace Reward]
    (algorithm : HistoryAlgorithm Action Reward)
    (environment : HistoryEnvironment Action Reward) :
    Measure.map
        (fun trajectory =>
          (canonicalHistoryTrajectoryAction trajectory 0,
            canonicalHistoryTrajectoryReward trajectory 0))
        (canonicalHistoryTrajectoryMeasure algorithm environment) =
      algorithm.initialAction ⊗ₘ environment.initialFeedback := by
  rw [canonicalHistoryTrajectoryMeasure]
  have hpair :
      (fun trajectory : (n : Nat) -> Action × Reward =>
        (canonicalHistoryTrajectoryAction trajectory 0,
          canonicalHistoryTrajectoryReward trajectory 0)) =
        fun trajectory => trajectory 0 := by
    funext trajectory
    exact Prod.eta _
  rw [hpair]
  exact RewardKernel.trajMeasure_map_eval_zero
    (X := fun _ : Nat => Action × Reward)
    (algorithm.initialAction ⊗ₘ environment.initialFeedback)
    (fun n => historyStepKernel algorithm environment n)

theorem canonicalHistoryTrajectory_step_condDistrib
    {Action : Type u} {Reward : Type v}
    [MeasurableSpace Action] [StandardBorelSpace Action] [Nonempty Action]
    [MeasurableSpace Reward] [StandardBorelSpace Reward] [Nonempty Reward]
    (algorithm : HistoryAlgorithm Action Reward)
    (environment : HistoryEnvironment Action Reward) (n : Nat) :
    ProbabilityTheory.condDistrib
        (fun trajectory =>
          (canonicalHistoryTrajectoryAction trajectory (n + 1),
            canonicalHistoryTrajectoryReward trajectory (n + 1)))
        (fun trajectory => History.finitePairHistoryOfTrace
          (canonicalHistoryTrajectoryAction trajectory)
          (canonicalHistoryTrajectoryReward trajectory) n)
        (canonicalHistoryTrajectoryMeasure algorithm environment) =ᵐ[
      (canonicalHistoryTrajectoryMeasure algorithm environment).map
        (fun trajectory => History.finitePairHistoryOfTrace
          (canonicalHistoryTrajectoryAction trajectory)
          (canonicalHistoryTrajectoryReward trajectory) n)]
      historyStepKernel algorithm environment n := by
  have hnext :
      (fun trajectory : (k : Nat) -> Action × Reward =>
        (canonicalHistoryTrajectoryAction trajectory (n + 1),
          canonicalHistoryTrajectoryReward trajectory (n + 1))) =
        fun trajectory => trajectory (n + 1) := by
    funext trajectory
    exact Prod.eta _
  have hhistory :
      (fun trajectory : (k : Nat) -> Action × Reward =>
        History.finitePairHistoryOfTrace
          (canonicalHistoryTrajectoryAction trajectory)
          (canonicalHistoryTrajectoryReward trajectory) n) =
        Preorder.frestrictLe n := by
    rfl
  rw [hnext, hhistory]
  simpa only [canonicalHistoryTrajectoryMeasure] using
    (ProbabilityTheory.Kernel.condDistrib_trajMeasure
      (X := fun _ : Nat => Action × Reward)
      (μ₀ := algorithm.initialAction ⊗ₘ environment.initialFeedback)
      (κ := fun k => historyStepKernel algorithm environment k) (a := n))

/--
The canonical pair trajectory satisfies the combined history-process contract
without any externally supplied law premise.
-/
noncomputable def canonicalHistoryAlgorithmEnvironmentSequence
    {Action : Type u} {Reward : Type v}
    [MeasurableSpace Action] [StandardBorelSpace Action] [Nonempty Action]
    [MeasurableSpace Reward] [StandardBorelSpace Reward] [Nonempty Reward]
    (algorithm : HistoryAlgorithm Action Reward)
    (environment : HistoryEnvironment Action Reward) :
    IsHistoryAlgorithmEnvironmentSequence
      (canonicalHistoryTrajectoryMeasure algorithm environment)
      canonicalHistoryTrajectoryAction canonicalHistoryTrajectoryReward
      algorithm environment where
  measurable_action := measurable_canonicalHistoryTrajectoryAction_apply
  measurable_reward := measurable_canonicalHistoryTrajectoryReward_apply
  initialPair_map_eq :=
    canonicalHistoryTrajectory_initialPair_map_eq algorithm environment
  step_condDistrib :=
    canonicalHistoryTrajectory_step_condDistrib algorithm environment

/-- The combined initial pair law determines the initial action marginal. -/
theorem initialAction_map_eq_of_historyAlgorithmEnvironmentSequence
    {Omega : Type w} {Action : Type u} {Reward : Type v}
    [MeasurableSpace Omega]
    [MeasurableSpace Action] [StandardBorelSpace Action] [Nonempty Action]
    [MeasurableSpace Reward] [StandardBorelSpace Reward] [Nonempty Reward]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Reward)
    (algorithm : HistoryAlgorithm Action Reward)
    (environment : HistoryEnvironment Action Reward)
    (source : IsHistoryAlgorithmEnvironmentSequence
      mu action reward algorithm environment) :
    mu.map (fun omega => action omega 0) = algorithm.initialAction := by
  calc
    mu.map (fun omega => action omega 0) =
        (mu.map (fun omega => (action omega 0, reward omega 0))).map Prod.fst := by
      rw [Measure.map_map measurable_fst
        ((source.measurable_action 0).prod (source.measurable_reward 0))]
      exact Measure.map_congr <| Filter.Eventually.of_forall <| fun _ => rfl
    _ = (algorithm.initialAction ⊗ₘ environment.initialFeedback).fst := by
      rw [source.initialPair_map_eq]
      rfl
    _ = algorithm.initialAction :=
      Measure.fst_compProd algorithm.initialAction environment.initialFeedback

/-- The combined initial pair law determines the initial feedback conditional law. -/
theorem initialFeedback_condDistrib_of_historyAlgorithmEnvironmentSequence
    {Omega : Type w} {Action : Type u} {Reward : Type v}
    [MeasurableSpace Omega]
    [MeasurableSpace Action] [StandardBorelSpace Action] [Nonempty Action]
    [MeasurableSpace Reward] [StandardBorelSpace Reward] [Nonempty Reward]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Reward)
    (algorithm : HistoryAlgorithm Action Reward)
    (environment : HistoryEnvironment Action Reward)
    (source : IsHistoryAlgorithmEnvironmentSequence
      mu action reward algorithm environment) :
    ProbabilityTheory.condDistrib (fun omega => reward omega 0)
        (fun omega => action omega 0) mu =ᵐ[
      mu.map (fun omega => action omega 0)] environment.initialFeedback :=
  ProbabilityTheory.condDistrib_ae_eq_of_measure_eq_compProd
    (fun omega => action omega 0) (source.measurable_reward 0).aemeasurable <| by
      rw [initialAction_map_eq_of_historyAlgorithmEnvironmentSequence
        mu action reward algorithm environment source]
      exact source.initialPair_map_eq

/-- The action marginal of a history step kernel is its policy kernel. -/
theorem historyStepKernel_map_fst
    {Action : Type u} {Reward : Type v}
    [MeasurableSpace Action] [MeasurableSpace Reward]
    (algorithm : HistoryAlgorithm Action Reward)
    (environment : HistoryEnvironment Action Reward) (n : Nat) :
    (historyStepKernel algorithm environment n).map Prod.fst =
      algorithm.policy n := by
  rw [← ProbabilityTheory.Kernel.fst_eq]
  exact ProbabilityTheory.Kernel.fst_compProd _ _

/-- The combined successor pair law determines the successor action policy. -/
theorem policy_condDistrib_of_historyAlgorithmEnvironmentSequence
    {Omega : Type w} {Action : Type u} {Reward : Type v}
    [MeasurableSpace Omega]
    [MeasurableSpace Action] [StandardBorelSpace Action] [Nonempty Action]
    [MeasurableSpace Reward] [StandardBorelSpace Reward] [Nonempty Reward]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Reward)
    (algorithm : HistoryAlgorithm Action Reward)
    (environment : HistoryEnvironment Action Reward)
    (source : IsHistoryAlgorithmEnvironmentSequence
      mu action reward algorithm environment) (n : Nat) :
    ProbabilityTheory.condDistrib (fun omega => action omega (n + 1))
        (fun omega => History.finitePairHistoryOfTrace
          (action omega) (reward omega) n) mu =ᵐ[
      mu.map (fun omega => History.finitePairHistoryOfTrace
        (action omega) (reward omega) n)] algorithm.policy n := by
  let history := fun omega => History.finitePairHistoryOfTrace
    (action omega) (reward omega) n
  let nextPair := fun omega => (action omega (n + 1), reward omega (n + 1))
  have hcomp :
      ProbabilityTheory.condDistrib (Prod.fst ∘ nextPair) history mu =ᵐ[
        mu.map history]
        (ProbabilityTheory.condDistrib nextPair history mu).map Prod.fst :=
    ProbabilityTheory.condDistrib_comp
      (μ := mu) (mβ := inferInstance) (Y := nextPair) history
      ((source.measurable_action (n + 1)).prod
        (source.measurable_reward (n + 1))).aemeasurable
      (f := Prod.fst) measurable_fst
  have hresult :
      ProbabilityTheory.condDistrib (Prod.fst ∘ nextPair) history mu =ᵐ[
        mu.map history] algorithm.policy n := by
    filter_upwards [hcomp, source.step_condDistrib n] with h hcompAt hpairAt
    calc
      ProbabilityTheory.condDistrib (Prod.fst ∘ nextPair)
          history mu h =
          ((ProbabilityTheory.condDistrib nextPair history mu).map Prod.fst) h :=
        hcompAt
      _ = ((historyStepKernel algorithm environment n).map Prod.fst) h := by
        rw [ProbabilityTheory.Kernel.map_apply _ measurable_fst,
          ProbabilityTheory.Kernel.map_apply _ measurable_fst, hpairAt]
      _ = algorithm.policy n h := by
        rw [historyStepKernel_map_fst]
  simpa [history, nextPair, Function.comp_def] using hresult

/--
The combined successor pair law also determines the feedback conditional law
given the finite history and the newly sampled action.
-/
theorem feedback_condDistrib_of_historyAlgorithmEnvironmentSequence
    {Omega : Type w} {Action : Type u} {Reward : Type v}
    [MeasurableSpace Omega]
    [MeasurableSpace Action] [StandardBorelSpace Action] [Nonempty Action]
    [MeasurableSpace Reward] [StandardBorelSpace Reward] [Nonempty Reward]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Reward)
    (algorithm : HistoryAlgorithm Action Reward)
    (environment : HistoryEnvironment Action Reward)
    (source : IsHistoryAlgorithmEnvironmentSequence
      mu action reward algorithm environment) (n : Nat) :
    ProbabilityTheory.condDistrib (fun omega => reward omega (n + 1))
        (fun omega =>
          (History.finitePairHistoryOfTrace
            (action omega) (reward omega) n, action omega (n + 1))) mu =ᵐ[
      mu.map (fun omega =>
        (History.finitePairHistoryOfTrace
          (action omega) (reward omega) n, action omega (n + 1)))]
      environment.feedback n := by
  let history := fun omega => History.finitePairHistoryOfTrace
    (action omega) (reward omega) n
  let nextAction := fun omega => action omega (n + 1)
  let nextReward := fun omega => reward omega (n + 1)
  let nextPair := fun omega => (nextAction omega, nextReward omega)
  have hhistory : Measurable history :=
    History.measurable_finitePairHistoryOfTrace
      action reward source.measurable_action source.measurable_reward n
  have hnextAction : Measurable nextAction := source.measurable_action (n + 1)
  have hnextReward : Measurable nextReward := source.measurable_reward (n + 1)
  have hpolicy := policy_condDistrib_of_historyAlgorithmEnvironmentSequence
    mu action reward algorithm environment source n
  have hpolicyJoint :
      mu.map (fun omega => (history omega, nextAction omega)) =
        mu.map history ⊗ₘ algorithm.policy n :=
    (ProbabilityTheory.condDistrib_ae_eq_iff_measure_eq_compProd
      history hnextAction.aemeasurable (algorithm.policy n)).mp <| by
        simpa [history, nextAction] using hpolicy
  have hpairJoint :
      mu.map (fun omega => (history omega, nextPair omega)) =
        mu.map history ⊗ₘ historyStepKernel algorithm environment n := by
    simpa [history, nextPair, nextAction, nextReward] using
      nextPairJointLaw_eq_compProd
        mu action reward algorithm environment source n
  have hfeedbackJoint :
      mu.map (fun omega =>
          ((history omega, nextAction omega), nextReward omega)) =
        mu.map (fun omega => (history omega, nextAction omega)) ⊗ₘ
          environment.feedback n := by
    calc
      mu.map (fun omega =>
          ((history omega, nextAction omega), nextReward omega)) =
          (mu.map (fun omega => (history omega, nextPair omega))).map
            MeasurableEquiv.prodAssoc.symm := by
        rw [Measure.map_map MeasurableEquiv.prodAssoc.symm.measurable
          (hhistory.prod (hnextAction.prod hnextReward))]
        exact Measure.map_congr <| Filter.Eventually.of_forall <| fun _ => rfl
      _ = (mu.map history ⊗ₘ
          historyStepKernel algorithm environment n).map
            MeasurableEquiv.prodAssoc.symm := by
        rw [hpairJoint]
      _ = (mu.map history ⊗ₘ
          (algorithm.policy n ⊗ₖ environment.feedback n)).map
            MeasurableEquiv.prodAssoc.symm := by
        rfl
      _ = (mu.map history ⊗ₘ algorithm.policy n) ⊗ₘ
          environment.feedback n := Measure.compProd_assoc
      _ = mu.map (fun omega => (history omega, nextAction omega)) ⊗ₘ
          environment.feedback n := by
        rw [hpolicyJoint]
  have hresult :=
    ProbabilityTheory.condDistrib_ae_eq_of_measure_eq_compProd
      (fun omega => (history omega, nextAction omega))
      hnextReward.aemeasurable hfeedbackJoint
  simpa [history, nextAction, nextReward] using hresult

/-- Split action/feedback laws for one fixed history environment. -/
structure HistoryAlgorithmEnvironmentSplitSource
    {Omega : Type w} {Action : Type u} {Reward : Type v}
    [MeasurableSpace Omega]
    [MeasurableSpace Action] [StandardBorelSpace Action] [Nonempty Action]
    [MeasurableSpace Reward] [StandardBorelSpace Reward] [Nonempty Reward]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Reward)
    (algorithm : HistoryAlgorithm Action Reward)
    (environment : HistoryEnvironment Action Reward) : Prop where
  measurable_action : forall n, Measurable (fun omega => action omega n)
  measurable_reward : forall n, Measurable (fun omega => reward omega n)
  initialAction_map_eq :
    mu.map (fun omega => action omega 0) = algorithm.initialAction
  initialFeedback_condDistrib :
    ProbabilityTheory.condDistrib (fun omega => reward omega 0)
        (fun omega => action omega 0) mu =ᵐ[
      mu.map (fun omega => action omega 0)] environment.initialFeedback
  policy_condDistrib : forall n,
    ProbabilityTheory.condDistrib (fun omega => action omega (n + 1))
        (fun omega => History.finitePairHistoryOfTrace
          (action omega) (reward omega) n) mu =ᵐ[
      mu.map (fun omega => History.finitePairHistoryOfTrace
        (action omega) (reward omega) n)] algorithm.policy n
  feedback_condDistrib : forall n,
    ProbabilityTheory.condDistrib (fun omega => reward omega (n + 1))
        (fun omega =>
          (History.finitePairHistoryOfTrace
            (action omega) (reward omega) n, action omega (n + 1))) mu =ᵐ[
      mu.map (fun omega =>
        (History.finitePairHistoryOfTrace
          (action omega) (reward omega) n, action omega (n + 1)))]
      environment.feedback n

/-- Assemble the combined process contract from a fixed-environment split source. -/
noncomputable def HistoryAlgorithmEnvironmentSplitSource.toSequence
    {Omega : Type w} {Action : Type u} {Reward : Type v}
    [MeasurableSpace Omega]
    [MeasurableSpace Action] [StandardBorelSpace Action] [Nonempty Action]
    [MeasurableSpace Reward] [StandardBorelSpace Reward] [Nonempty Reward]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Reward)
    (algorithm : HistoryAlgorithm Action Reward)
    (environment : HistoryEnvironment Action Reward)
    (source : HistoryAlgorithmEnvironmentSplitSource
      mu action reward algorithm environment) :
    IsHistoryAlgorithmEnvironmentSequence
      mu action reward algorithm environment :=
  isHistoryAlgorithmEnvironmentSequence_of_split
    mu action reward algorithm environment
    source.measurable_action source.measurable_reward
    source.initialAction_map_eq source.initialFeedback_condDistrib
    source.policy_condDistrib source.feedback_condDistrib

/-- The canonical trajectory realizes all four fixed-environment split laws. -/
noncomputable def canonicalHistoryAlgorithmEnvironmentSplitSource
    {Action : Type u} {Reward : Type v}
    [MeasurableSpace Action] [StandardBorelSpace Action] [Nonempty Action]
    [MeasurableSpace Reward] [StandardBorelSpace Reward] [Nonempty Reward]
    (algorithm : HistoryAlgorithm Action Reward)
    (environment : HistoryEnvironment Action Reward) :
    HistoryAlgorithmEnvironmentSplitSource
      (canonicalHistoryTrajectoryMeasure algorithm environment)
      canonicalHistoryTrajectoryAction canonicalHistoryTrajectoryReward
      algorithm environment where
  measurable_action := measurable_canonicalHistoryTrajectoryAction_apply
  measurable_reward := measurable_canonicalHistoryTrajectoryReward_apply
  initialAction_map_eq :=
    initialAction_map_eq_of_historyAlgorithmEnvironmentSequence
      (canonicalHistoryTrajectoryMeasure algorithm environment)
      canonicalHistoryTrajectoryAction canonicalHistoryTrajectoryReward
      algorithm environment
      (canonicalHistoryAlgorithmEnvironmentSequence algorithm environment)
  initialFeedback_condDistrib :=
    initialFeedback_condDistrib_of_historyAlgorithmEnvironmentSequence
      (canonicalHistoryTrajectoryMeasure algorithm environment)
      canonicalHistoryTrajectoryAction canonicalHistoryTrajectoryReward
      algorithm environment
      (canonicalHistoryAlgorithmEnvironmentSequence algorithm environment)
  policy_condDistrib :=
    policy_condDistrib_of_historyAlgorithmEnvironmentSequence
      (canonicalHistoryTrajectoryMeasure algorithm environment)
      canonicalHistoryTrajectoryAction canonicalHistoryTrajectoryReward
      algorithm environment
      (canonicalHistoryAlgorithmEnvironmentSequence algorithm environment)
  feedback_condDistrib :=
    feedback_condDistrib_of_historyAlgorithmEnvironmentSequence
      (canonicalHistoryTrajectoryMeasure algorithm environment)
      canonicalHistoryTrajectoryAction canonicalHistoryTrajectoryReward
      algorithm environment
      (canonicalHistoryAlgorithmEnvironmentSequence algorithm environment)

/-- The canonical combined process reconstructed specifically from its split laws. -/
noncomputable def canonicalHistoryAlgorithmEnvironmentSequence_of_split
    {Action : Type u} {Reward : Type v}
    [MeasurableSpace Action] [StandardBorelSpace Action] [Nonempty Action]
    [MeasurableSpace Reward] [StandardBorelSpace Reward] [Nonempty Reward]
    (algorithm : HistoryAlgorithm Action Reward)
    (environment : HistoryEnvironment Action Reward) :
    IsHistoryAlgorithmEnvironmentSequence
      (canonicalHistoryTrajectoryMeasure algorithm environment)
      canonicalHistoryTrajectoryAction canonicalHistoryTrajectoryReward
      algorithm environment :=
  (canonicalHistoryAlgorithmEnvironmentSplitSource algorithm environment).toSequence
    (canonicalHistoryTrajectoryMeasure algorithm environment)
    canonicalHistoryTrajectoryAction canonicalHistoryTrajectoryReward
    algorithm environment

/-- Lift a kernel to samples that retain the kernel input as their first coordinate. -/
noncomputable def kernelWithInput
    {Input : Type u} {Output : Type v}
    [MeasurableSpace Input] [MeasurableSpace Output]
    (kernel : ProbabilityTheory.Kernel Input Output) :
    ProbabilityTheory.Kernel Input (Input × Output) :=
  ProbabilityTheory.Kernel.id ⊗ₖ
    ProbabilityTheory.Kernel.prodMkLeft Input kernel

instance instKernelWithInputIsMarkov
    {Input : Type u} {Output : Type v}
    [MeasurableSpace Input] [MeasurableSpace Output]
    (kernel : ProbabilityTheory.Kernel Input Output)
    [ProbabilityTheory.IsMarkovKernel kernel] :
    ProbabilityTheory.IsMarkovKernel (kernelWithInput kernel) := by
  unfold kernelWithInput
  infer_instance

theorem kernelWithInput_apply
    {Input : Type u} {Output : Type v}
    [MeasurableSpace Input] [MeasurableSingletonClass Input]
    [MeasurableSpace Output]
    (kernel : ProbabilityTheory.Kernel Input Output)
    [ProbabilityTheory.IsMarkovKernel kernel] (input : Input) :
    kernelWithInput kernel input =
      (kernel input).map (Prod.mk input) := by
  ext event hevent
  rw [kernelWithInput,
    ProbabilityTheory.Kernel.compProd_apply hevent,
    ProbabilityTheory.Kernel.id_apply, lintegral_dirac]
  rw [ProbabilityTheory.Kernel.prodMkLeft_apply]
  rw [Measure.map_apply (f := Prod.mk input)
    (measurable_const.prodMk measurable_id) hevent]

/--
For a composition-product sample, conditioning the complete sample on its
first coordinate keeps that coordinate and uses the supplied second-coordinate
kernel.
-/
theorem condDistrib_id_fst_compProd_ae_eq_kernelWithInput
    {Input : Type u} {Output : Type v}
    [MeasurableSpace Input] [StandardBorelSpace Input] [Nonempty Input]
    [MeasurableSpace Output] [StandardBorelSpace Output] [Nonempty Output]
    (prior : Measure Input) [IsFiniteMeasure prior]
    (kernel : ProbabilityTheory.Kernel Input Output)
    [ProbabilityTheory.IsMarkovKernel kernel] :
    ProbabilityTheory.condDistrib id Prod.fst (prior ⊗ₘ kernel) =ᵐ[prior]
      kernelWithInput kernel := by
  let sampleMeasure := prior ⊗ₘ kernel
  have hfirst : sampleMeasure.map Prod.fst = prior := by
    change (prior ⊗ₘ kernel).fst = prior
    exact Measure.fst_compProd prior kernel
  have hjoint :
      sampleMeasure.map (fun sample => (sample.1, sample)) =
        sampleMeasure.map Prod.fst ⊗ₘ kernelWithInput kernel := by
    rw [hfirst]
    ext event hevent
    rw [Measure.map_apply
      (f := fun sample : Input × Output => (sample.1, sample))
      (measurable_fst.prodMk measurable_id) hevent]
    change (prior ⊗ₘ kernel)
        ((fun sample : Input × Output => (sample.1, sample)) ⁻¹' event) =
      (prior ⊗ₘ kernelWithInput kernel) event
    rw [Measure.compProd_apply
      (μ := prior) (κ := kernel)
      (s := (fun sample : Input × Output => (sample.1, sample)) ⁻¹' event)
      (hevent.preimage (measurable_fst.prodMk measurable_id)),
      Measure.compProd_apply
        (μ := prior) (κ := kernelWithInput kernel) (s := event) hevent]
    congr with input
    rw [kernelWithInput_apply,
      Measure.map_apply (f := Prod.mk input)
        (measurable_const.prodMk measurable_id)]
    · rfl
    · exact hevent.preimage (measurable_const.prodMk measurable_id)
  have hcond :=
    ProbabilityTheory.condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
      (μ := sampleMeasure) (κ := kernelWithInput kernel)
      measurable_fst measurable_id hjoint
  rw [hfirst] at hcond
  exact hcond

/-- Action trace of an environment/trajectory sample. -/
def environmentTrajectoryAction
    {Env : Type u} {Action : Type v} {Reward : Type w} :
    (Env × ((n : Nat) -> Action × Reward)) -> ActionTrace Action :=
  fun sample n => (sample.2 n).1

/-- Reward trace of an environment/trajectory sample. -/
def environmentTrajectoryReward
    {Env : Type u} {Action : Type v} {Reward : Type w} :
    (Env × ((n : Nat) -> Action × Reward)) -> RewardTrace Reward :=
  fun sample n => (sample.2 n).2

theorem measurable_environmentTrajectoryAction_apply
    {Env : Type u} {Action : Type v} {Reward : Type w}
    [MeasurableSpace Env] [MeasurableSpace Action] [MeasurableSpace Reward]
    (n : Nat) :
    Measurable (fun sample : Env × ((k : Nat) -> Action × Reward) =>
      environmentTrajectoryAction sample n) :=
  measurable_fst.comp ((measurable_pi_apply n).comp measurable_snd)

theorem measurable_environmentTrajectoryReward_apply
    {Env : Type u} {Action : Type v} {Reward : Type w}
    [MeasurableSpace Env] [MeasurableSpace Action] [MeasurableSpace Reward]
    (n : Nat) :
    Measurable (fun sample : Env × ((k : Nat) -> Action × Reward) =>
      environmentTrajectoryReward sample n) :=
  measurable_snd.comp ((measurable_pi_apply n).comp measurable_snd)

/-- Transport a history-process contract across an equality of source measures. -/
noncomputable def historyAlgorithmEnvironmentSequence_of_measure_eq
    {Omega : Type w} {Action : Type u} {Reward : Type v}
    [MeasurableSpace Omega]
    [MeasurableSpace Action] [StandardBorelSpace Action] [Nonempty Action]
    [MeasurableSpace Reward] [StandardBorelSpace Reward] [Nonempty Reward]
    (mu nu : Measure Omega) [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Reward)
    (algorithm : HistoryAlgorithm Action Reward)
    (environment : HistoryEnvironment Action Reward)
    (hmeasure : mu = nu)
    (source : IsHistoryAlgorithmEnvironmentSequence
      mu action reward algorithm environment) :
    IsHistoryAlgorithmEnvironmentSequence
      nu action reward algorithm environment := by
  subst nu
  exact source

/-- Retaining a fixed environment coordinate preserves the canonical process. -/
noncomputable def mappedCanonicalHistoryAlgorithmEnvironmentSequence
    {Env : Type u} {Action : Type v} {Reward : Type w}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [StandardBorelSpace Action] [Nonempty Action]
    [MeasurableSpace Reward] [StandardBorelSpace Reward] [Nonempty Reward]
    (algorithm : HistoryAlgorithm Action Reward)
    (feedbackEnvironment : Env -> HistoryEnvironment Action Reward)
    (environment : Env) :
    IsHistoryAlgorithmEnvironmentSequence
      ((canonicalHistoryTrajectoryMeasure algorithm
        (feedbackEnvironment environment)).map (Prod.mk environment))
      environmentTrajectoryAction environmentTrajectoryReward
      algorithm (feedbackEnvironment environment) where
  measurable_action := measurable_environmentTrajectoryAction_apply
  measurable_reward := measurable_environmentTrajectoryReward_apply
  initialPair_map_eq := by
    calc
      Measure.map
          (fun sample =>
            (environmentTrajectoryAction sample 0,
              environmentTrajectoryReward sample 0))
          ((canonicalHistoryTrajectoryMeasure algorithm
            (feedbackEnvironment environment)).map (Prod.mk environment)) =
          Measure.map
            ((fun sample =>
              (environmentTrajectoryAction sample 0,
                environmentTrajectoryReward sample 0)) ∘ Prod.mk environment)
            (canonicalHistoryTrajectoryMeasure algorithm
              (feedbackEnvironment environment)) := by
        exact Measure.map_map
          ((measurable_environmentTrajectoryAction_apply 0).prod
            (measurable_environmentTrajectoryReward_apply 0))
          (measurable_const.prodMk measurable_id)
      _ = Measure.map
          (fun trajectory =>
            (canonicalHistoryTrajectoryAction trajectory 0,
              canonicalHistoryTrajectoryReward trajectory 0))
          (canonicalHistoryTrajectoryMeasure algorithm
            (feedbackEnvironment environment)) := by
        congr 1
      _ = algorithm.initialAction ⊗ₘ
          (feedbackEnvironment environment).initialFeedback :=
        canonicalHistoryTrajectory_initialPair_map_eq
          algorithm (feedbackEnvironment environment)
  step_condDistrib := fun n => by
    let canonicalMeasure := canonicalHistoryTrajectoryMeasure
      algorithm (feedbackEnvironment environment)
    let embed : ((k : Nat) -> Action × Reward) ->
        Env × ((k : Nat) -> Action × Reward) := Prod.mk environment
    let history := fun sample : Env × ((k : Nat) -> Action × Reward) =>
      History.finitePairHistoryOfTrace
        (environmentTrajectoryAction sample)
        (environmentTrajectoryReward sample) n
    let nextPair := fun sample : Env × ((k : Nat) -> Action × Reward) =>
      (environmentTrajectoryAction sample (n + 1),
        environmentTrajectoryReward sample (n + 1))
    have hembed : Measurable embed := measurable_const.prodMk measurable_id
    have hhistory : Measurable history :=
      History.measurable_finitePairHistoryOfTrace
        environmentTrajectoryAction environmentTrajectoryReward
        measurable_environmentTrajectoryAction_apply
        measurable_environmentTrajectoryReward_apply n
    have hnextPair : Measurable nextPair :=
      (measurable_environmentTrajectoryAction_apply (n + 1)).prod
        (measurable_environmentTrajectoryReward_apply (n + 1))
    have hhistoryComp : history ∘ embed = Preorder.frestrictLe n := by
      rfl
    have hnextPairComp :
        nextPair ∘ embed =
          (fun trajectory : (k : Nat) -> Action × Reward =>
            trajectory (n + 1)) := by
      funext trajectory
      exact Prod.eta _
    have hfilter :
        (canonicalMeasure.map embed).map history =
          canonicalMeasure.map (Preorder.frestrictLe n) := by
      calc
        (canonicalMeasure.map embed).map history =
            canonicalMeasure.map (history ∘ embed) :=
          Measure.map_map hhistory hembed
        _ = canonicalMeasure.map (Preorder.frestrictLe n) := by
          rw [hhistoryComp]
    have hmap := ProbabilityTheory.condDistrib_map
      (ν := canonicalMeasure) (f := embed)
      (X := history) (Y := nextPair)
      hhistory.aemeasurable hnextPair.aemeasurable hembed.aemeasurable
    have hmap' :
        ProbabilityTheory.condDistrib nextPair history
            (canonicalMeasure.map embed) =ᵐ[
          canonicalMeasure.map (Preorder.frestrictLe n)]
          ProbabilityTheory.condDistrib
            (fun trajectory => trajectory (n + 1))
            (Preorder.frestrictLe n) canonicalMeasure := by
      simpa only [hnextPairComp, hhistoryComp] using hmap
    rw [hfilter]
    exact hmap'.trans <| by
      simpa only [canonicalMeasure] using
        (ProbabilityTheory.Kernel.condDistrib_trajMeasure
          (X := fun _ : Nat => Action × Reward)
          (μ₀ := algorithm.initialAction ⊗ₘ
            (feedbackEnvironment environment).initialFeedback)
          (κ := fun k => historyStepKernel algorithm
            (feedbackEnvironment environment) k) (a := n))

/--
A trajectory kernel whose value is the canonical fixed-environment law yields
the combined history-process contract after retaining its environment input.
-/
noncomputable def kernelWithInputHistoryAlgorithmEnvironmentSequence
    {Env : Type u} {Action : Type v} {Reward : Type w}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [StandardBorelSpace Action] [Nonempty Action]
    [MeasurableSpace Reward] [StandardBorelSpace Reward] [Nonempty Reward]
    (algorithm : HistoryAlgorithm Action Reward)
    (feedbackEnvironment : Env -> HistoryEnvironment Action Reward)
    (trajectoryKernel : ProbabilityTheory.Kernel
      Env ((n : Nat) -> Action × Reward))
    [ProbabilityTheory.IsMarkovKernel trajectoryKernel]
    (environment : Env)
    (hkernel : trajectoryKernel environment =
      canonicalHistoryTrajectoryMeasure algorithm
        (feedbackEnvironment environment)) :
    IsHistoryAlgorithmEnvironmentSequence
      (kernelWithInput trajectoryKernel environment)
      environmentTrajectoryAction environmentTrajectoryReward
      algorithm (feedbackEnvironment environment) := by
  have hmeasure :
      (canonicalHistoryTrajectoryMeasure algorithm
        (feedbackEnvironment environment)).map (Prod.mk environment) =
        kernelWithInput trajectoryKernel environment := by
    rw [kernelWithInput_apply, hkernel]
  exact historyAlgorithmEnvironmentSequence_of_measure_eq
    ((canonicalHistoryTrajectoryMeasure algorithm
      (feedbackEnvironment environment)).map (Prod.mk environment))
    (kernelWithInput trajectoryKernel environment)
    environmentTrajectoryAction environmentTrajectoryReward
    algorithm (feedbackEnvironment environment) hmeasure
    (mappedCanonicalHistoryAlgorithmEnvironmentSequence
      algorithm feedbackEnvironment environment)

/--
The regular conditional complete-sample law of a canonical environment/
trajectory composition product satisfies the history-process contract.
-/
theorem conditionalHistoryAlgorithmEnvironmentSequence_of_canonicalTrajectoryKernel
    {Env : Type u} {Action : Type v} {Reward : Type w}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [StandardBorelSpace Action] [Nonempty Action]
    [MeasurableSpace Reward] [StandardBorelSpace Reward] [Nonempty Reward]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (algorithm : HistoryAlgorithm Action Reward)
    (feedbackEnvironment : Env -> HistoryEnvironment Action Reward)
    (trajectoryKernel : ProbabilityTheory.Kernel
      Env ((n : Nat) -> Action × Reward))
    [ProbabilityTheory.IsMarkovKernel trajectoryKernel]
    (hkernel : forall environment,
      trajectoryKernel environment =
        canonicalHistoryTrajectoryMeasure algorithm
          (feedbackEnvironment environment)) :
    ∀ᵐ environment ∂(prior ⊗ₘ trajectoryKernel).map Prod.fst,
      IsHistoryAlgorithmEnvironmentSequence
        (ProbabilityTheory.condDistrib id Prod.fst
          (prior ⊗ₘ trajectoryKernel) environment)
        environmentTrajectoryAction environmentTrajectoryReward
        algorithm (feedbackEnvironment environment) := by
  have hfirst : (prior ⊗ₘ trajectoryKernel).map Prod.fst = prior := by
    change (prior ⊗ₘ trajectoryKernel).fst = prior
    exact Measure.fst_compProd prior trajectoryKernel
  have hcond := condDistrib_id_fst_compProd_ae_eq_kernelWithInput
    prior trajectoryKernel
  rw [hfirst]
  filter_upwards [hcond] with environment hcondAt
  exact historyAlgorithmEnvironmentSequence_of_measure_eq
    (kernelWithInput trajectoryKernel environment)
    (ProbabilityTheory.condDistrib id Prod.fst
      (prior ⊗ₘ trajectoryKernel) environment)
    environmentTrajectoryAction environmentTrajectoryReward
    algorithm (feedbackEnvironment environment) hcondAt.symm
    (kernelWithInputHistoryAlgorithmEnvironmentSequence
      algorithm feedbackEnvironment trajectoryKernel environment
      (hkernel environment))

/--
Canonical environment-indexed trajectory kernels supply all four conditional
split law families required by the Thompson density route.
-/
noncomputable def conditionalHistoryAlgorithmEnvironmentSplitSource_of_canonicalTrajectoryKernel
    {Env : Type u} {Action : Type v} {Reward : Type w}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [StandardBorelSpace Action] [Nonempty Action]
    [MeasurableSpace Reward] [StandardBorelSpace Reward] [Nonempty Reward]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (algorithm : HistoryAlgorithm Action Reward)
    (feedbackEnvironment : Env -> HistoryEnvironment Action Reward)
    (trajectoryKernel : ProbabilityTheory.Kernel
      Env ((n : Nat) -> Action × Reward))
    [ProbabilityTheory.IsMarkovKernel trajectoryKernel]
    (hkernel : forall environment,
      trajectoryKernel environment =
        canonicalHistoryTrajectoryMeasure algorithm
          (feedbackEnvironment environment)) :
    ConditionalHistoryAlgorithmEnvironmentSplitSource
      (prior ⊗ₘ trajectoryKernel) Prod.fst
      environmentTrajectoryAction environmentTrajectoryReward
      algorithm feedbackEnvironment where
  measurable_env := measurable_fst
  measurable_action := measurable_environmentTrajectoryAction_apply
  measurable_reward := measurable_environmentTrajectoryReward_apply
  initial_action := by
    filter_upwards [
      conditionalHistoryAlgorithmEnvironmentSequence_of_canonicalTrajectoryKernel
        prior algorithm feedbackEnvironment trajectoryKernel hkernel]
      with environment source
    exact initialAction_map_eq_of_historyAlgorithmEnvironmentSequence
      (ProbabilityTheory.condDistrib id Prod.fst
        (prior ⊗ₘ trajectoryKernel) environment)
      environmentTrajectoryAction environmentTrajectoryReward
      algorithm (feedbackEnvironment environment) source
  initial_feedback := by
    filter_upwards [
      conditionalHistoryAlgorithmEnvironmentSequence_of_canonicalTrajectoryKernel
        prior algorithm feedbackEnvironment trajectoryKernel hkernel]
      with environment source
    exact initialFeedback_condDistrib_of_historyAlgorithmEnvironmentSequence
      (ProbabilityTheory.condDistrib id Prod.fst
        (prior ⊗ₘ trajectoryKernel) environment)
      environmentTrajectoryAction environmentTrajectoryReward
      algorithm (feedbackEnvironment environment) source
  policy := fun n => by
    filter_upwards [
      conditionalHistoryAlgorithmEnvironmentSequence_of_canonicalTrajectoryKernel
        prior algorithm feedbackEnvironment trajectoryKernel hkernel]
      with environment source
    exact policy_condDistrib_of_historyAlgorithmEnvironmentSequence
      (ProbabilityTheory.condDistrib id Prod.fst
        (prior ⊗ₘ trajectoryKernel) environment)
      environmentTrajectoryAction environmentTrajectoryReward
      algorithm (feedbackEnvironment environment) source n
  feedback := fun n => by
    filter_upwards [
      conditionalHistoryAlgorithmEnvironmentSequence_of_canonicalTrajectoryKernel
        prior algorithm feedbackEnvironment trajectoryKernel hkernel]
      with environment source
    exact feedback_condDistrib_of_historyAlgorithmEnvironmentSequence
      (ProbabilityTheory.condDistrib id Prod.fst
        (prior ⊗ₘ trajectoryKernel) environment)
      environmentTrajectoryAction environmentTrajectoryReward
      algorithm (feedbackEnvironment environment) source n

/--
Paired canonical actual/reference trajectory kernels construct the complete
conditional split source consumed by algorithm-density transport.
-/
noncomputable def conditionalHistoryAlgorithmDensitySplitSource_of_canonicalTrajectoryKernels
    {Env : Type u} {Action : Type v} {Reward : Type w}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [StandardBorelSpace Action] [Nonempty Action]
    [MeasurableSpace Reward] [StandardBorelSpace Reward] [Nonempty Reward]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (algorithm referenceAlgorithm : HistoryAlgorithm Action Reward)
    (feedbackEnvironment : Env -> HistoryEnvironment Action Reward)
    (trajectoryKernel referenceTrajectoryKernel : ProbabilityTheory.Kernel
      Env ((n : Nat) -> Action × Reward))
    [ProbabilityTheory.IsMarkovKernel trajectoryKernel]
    [ProbabilityTheory.IsMarkovKernel referenceTrajectoryKernel]
    (htrajectoryKernel : forall environment,
      trajectoryKernel environment =
        canonicalHistoryTrajectoryMeasure algorithm
          (feedbackEnvironment environment))
    (hreferenceTrajectoryKernel : forall environment,
      referenceTrajectoryKernel environment =
        canonicalHistoryTrajectoryMeasure referenceAlgorithm
          (feedbackEnvironment environment))
    (absolutelyContinuous :
      HistoryAlgorithmAbsolutelyContinuous algorithm referenceAlgorithm) :
    ConditionalHistoryAlgorithmDensitySplitSource
      (prior ⊗ₘ trajectoryKernel) Prod.fst
      environmentTrajectoryAction environmentTrajectoryReward
      (prior ⊗ₘ referenceTrajectoryKernel) Prod.fst
      environmentTrajectoryAction environmentTrajectoryReward
      algorithm referenceAlgorithm feedbackEnvironment where
  actual :=
    conditionalHistoryAlgorithmEnvironmentSplitSource_of_canonicalTrajectoryKernel
      prior algorithm feedbackEnvironment trajectoryKernel htrajectoryKernel
  reference :=
    conditionalHistoryAlgorithmEnvironmentSplitSource_of_canonicalTrajectoryKernel
      prior referenceAlgorithm feedbackEnvironment referenceTrajectoryKernel
        hreferenceTrajectoryKernel
  env_map_eq := by
    change (prior ⊗ₘ trajectoryKernel).fst =
      (prior ⊗ₘ referenceTrajectoryKernel).fst
    rw [Measure.fst_compProd, Measure.fst_compProd]
  absolutelyContinuous := absolutelyContinuous

/--
Finite-prefix Thompson probability matching for paired canonical recursive
trajectory kernels. The remaining producer obligation is exactly the
measurable kernel family whose values are the fixed-environment canonical
`trajMeasure`s.
-/
theorem finitePairReferencePolicySampler_condDistrib_action_ae_eq_bestAction_of_canonicalTrajectoryKernels
    {Env : Type u} {Action : Type v} {Reward : Type w}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [StandardBorelSpace Action] [Nonempty Action]
    [MeasurableSpace Reward] [StandardBorelSpace Reward] [Nonempty Reward]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (algorithm referenceAlgorithm : HistoryAlgorithm Action Reward)
    (feedbackEnvironment : Env -> HistoryEnvironment Action Reward)
    (trajectoryKernel referenceTrajectoryKernel : ProbabilityTheory.Kernel
      Env ((n : Nat) -> Action × Reward))
    [ProbabilityTheory.IsMarkovKernel trajectoryKernel]
    [ProbabilityTheory.IsMarkovKernel referenceTrajectoryKernel]
    (htrajectoryKernel : forall environment,
      trajectoryKernel environment =
        canonicalHistoryTrajectoryMeasure algorithm
          (feedbackEnvironment environment))
    (hreferenceTrajectoryKernel : forall environment,
      referenceTrajectoryKernel environment =
        canonicalHistoryTrajectoryMeasure referenceAlgorithm
          (feedbackEnvironment environment))
    (absolutelyContinuous :
      HistoryAlgorithmAbsolutelyContinuous algorithm referenceAlgorithm)
    (n : Nat) (bestAction : Env -> Action)
    (hbestAction : Measurable bestAction) :
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
    finitePairReferencePolicySampler_condDistrib_action_ae_eq_bestAction_of_conditionalSplitSource
      (prior ⊗ₘ trajectoryKernel) Prod.fst
      environmentTrajectoryAction environmentTrajectoryReward
      (prior ⊗ₘ referenceTrajectoryKernel) Prod.fst
      environmentTrajectoryAction environmentTrajectoryReward
      algorithm referenceAlgorithm feedbackEnvironment
      (conditionalHistoryAlgorithmDensitySplitSource_of_canonicalTrajectoryKernels
        prior algorithm referenceAlgorithm feedbackEnvironment
        trajectoryKernel referenceTrajectoryKernel
        htrajectoryKernel hreferenceTrajectoryKernel absolutelyContinuous)
      n bestAction hbestAction

end Thompson
end BanditRLProof
