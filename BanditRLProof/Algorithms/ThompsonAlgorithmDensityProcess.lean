import BanditRLProof.Algorithms.ThompsonAlgorithmDensity
import BanditRLProof.Algorithms.ETCFiniteArmRewardLaw
import Mathlib.Probability.Kernel.RadonNikodym

/-!
# Recursive algorithm-density transport for finite pair histories

This module ports the process-facing core of LML's algorithm-density theorem.
Two stochastic history policies interact with the same feedback environment.
If every actual action law is absolutely continuous with respect to the
reference action law, the actual finite action/reward history law is the
reference history law weighted by the recursive product of policy
Radon-Nikodym derivatives.
-/

open MeasureTheory
open scoped ENNReal ProbabilityTheory

universe u v w x y

namespace BanditRLProof
namespace Thompson

/-- A stochastic policy indexed by inclusive finite action/reward histories. -/
structure HistoryAlgorithm
    (Action : Type u) (Reward : Type v)
    [MeasurableSpace Action] [MeasurableSpace Reward] where
  policy : (n : Nat) ->
    ProbabilityTheory.Kernel (History.FinitePairHistory Action Reward n) Action
  [policy_isMarkov : forall n, ProbabilityTheory.IsMarkovKernel (policy n)]
  initialAction : Measure Action
  [initialAction_isProbability : IsProbabilityMeasure initialAction]

instance instHistoryAlgorithmPolicyIsMarkovKernel
    {Action : Type u} {Reward : Type v}
    [MeasurableSpace Action] [MeasurableSpace Reward]
    (algorithm : HistoryAlgorithm Action Reward) (n : Nat) :
    ProbabilityTheory.IsMarkovKernel (algorithm.policy n) :=
  algorithm.policy_isMarkov n

instance instHistoryAlgorithmInitialActionIsProbability
    {Action : Type u} {Reward : Type v}
    [MeasurableSpace Action] [MeasurableSpace Reward]
    (algorithm : HistoryAlgorithm Action Reward) :
    IsProbabilityMeasure algorithm.initialAction :=
  algorithm.initialAction_isProbability

/-- A stochastic feedback environment shared by the compared algorithms. -/
structure HistoryEnvironment
    (Action : Type u) (Reward : Type v)
    [MeasurableSpace Action] [MeasurableSpace Reward] where
  feedback : (n : Nat) -> ProbabilityTheory.Kernel
    (History.FinitePairHistory Action Reward n × Action) Reward
  [feedback_isMarkov : forall n,
    ProbabilityTheory.IsMarkovKernel (feedback n)]
  initialFeedback : ProbabilityTheory.Kernel Action Reward
  [initialFeedback_isMarkov :
    ProbabilityTheory.IsMarkovKernel initialFeedback]

instance instHistoryEnvironmentFeedbackIsMarkovKernel
    {Action : Type u} {Reward : Type v}
    [MeasurableSpace Action] [MeasurableSpace Reward]
    (environment : HistoryEnvironment Action Reward) (n : Nat) :
    ProbabilityTheory.IsMarkovKernel (environment.feedback n) :=
  environment.feedback_isMarkov n

instance instHistoryEnvironmentInitialFeedbackIsMarkovKernel
    {Action : Type u} {Reward : Type v}
    [MeasurableSpace Action] [MeasurableSpace Reward]
    (environment : HistoryEnvironment Action Reward) :
    ProbabilityTheory.IsMarkovKernel environment.initialFeedback :=
  environment.initialFeedback_isMarkov

/-- Conditional law of the next action/reward pair after a finite history. -/
noncomputable def historyStepKernel
    {Action : Type u} {Reward : Type v}
    [MeasurableSpace Action] [MeasurableSpace Reward]
    (algorithm : HistoryAlgorithm Action Reward)
    (environment : HistoryEnvironment Action Reward) (n : Nat) :
    ProbabilityTheory.Kernel
      (History.FinitePairHistory Action Reward n) (Action × Reward) :=
  algorithm.policy n ⊗ₖ environment.feedback n

instance instHistoryStepKernelIsMarkovKernel
    {Action : Type u} {Reward : Type v}
    [MeasurableSpace Action] [MeasurableSpace Reward]
    (algorithm : HistoryAlgorithm Action Reward)
    (environment : HistoryEnvironment Action Reward) (n : Nat) :
    ProbabilityTheory.IsMarkovKernel
      (historyStepKernel algorithm environment n) := by
  unfold historyStepKernel
  infer_instance

/-- Pointwise action-law absolute continuity between two algorithms. -/
structure HistoryAlgorithmAbsolutelyContinuous
    {Action : Type u} {Reward : Type v}
    [MeasurableSpace Action] [MeasurableSpace Reward]
    (algorithm referenceAlgorithm : HistoryAlgorithm Action Reward) : Prop where
  initialAction : algorithm.initialAction ≪ referenceAlgorithm.initialAction
  policy : forall n history,
    algorithm.policy n history ≪ referenceAlgorithm.policy n history

/-- The unique history at time zero containing one action/reward pair. -/
def singletonPairHistory
    {Action : Type u} {Reward : Type v}
    (pair : Action × Reward) : History.FinitePairHistory Action Reward 0 :=
  fun _ => pair

/-- Remove the last coordinate from an inclusive successor history. -/
def pairHistoryPrefix
    {Action : Type u} {Reward : Type v} {n : Nat}
    (history : History.FinitePairHistory Action Reward (n + 1)) :
    History.FinitePairHistory Action Reward n :=
  fun i => history ⟨i.1, Finset.mem_Iic.mpr (le_trans (Finset.mem_Iic.mp i.2)
    (Nat.le_succ n))⟩

/-- Last pair in an inclusive successor history. -/
def pairHistoryLast
    {Action : Type u} {Reward : Type v} {n : Nat}
    (history : History.FinitePairHistory Action Reward (n + 1)) :
    Action × Reward :=
  history ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩

theorem measurable_singletonPairHistory
    {Action : Type u} {Reward : Type v}
    [MeasurableSpace Action] [MeasurableSpace Reward] :
    Measurable (@singletonPairHistory Action Reward) := by
  exact measurable_pi_lambda _ (fun _ => measurable_id)

theorem measurable_pairHistoryPrefix
    {Action : Type u} {Reward : Type v} {n : Nat}
    [MeasurableSpace Action] [MeasurableSpace Reward] :
    Measurable (@pairHistoryPrefix Action Reward n) := by
  exact measurable_pi_lambda _ (fun i => measurable_pi_apply _)

theorem measurable_pairHistoryLast
    {Action : Type u} {Reward : Type v} {n : Nat}
    [MeasurableSpace Action] [MeasurableSpace Reward] :
    Measurable (@pairHistoryLast Action Reward n) :=
  measurable_pi_apply _

@[simp]
theorem pairHistoryPrefix_extendPairHistorySucc
    {Action : Type u} {Reward : Type v} {n : Nat}
    (history : History.FinitePairHistory Action Reward n)
    (next : Action × Reward) :
    pairHistoryPrefix (History.extendPairHistorySucc history next) = history := by
  funext i
  exact History.extendPairHistorySucc_apply_of_le history next _
    (Finset.mem_Iic.mp i.2)

@[simp]
theorem pairHistoryLast_extendPairHistorySucc
    {Action : Type u} {Reward : Type v} {n : Nat}
    (history : History.FinitePairHistory Action Reward n)
    (next : Action × Reward) :
    pairHistoryLast (History.extendPairHistorySucc history next) = next := by
  simp [pairHistoryLast]

/-- Recursive product of the initial and policy action likelihood ratios. -/
noncomputable def historyDensity
    {Action : Type u} {Reward : Type v}
    [MeasurableSpace Action] [MeasurableSpace Reward]
    [MeasurableSpace.CountablyGenerated Action]
    (algorithm referenceAlgorithm : HistoryAlgorithm Action Reward) :
    (n : Nat) -> History.FinitePairHistory Action Reward n -> ENNReal
  | 0, history =>
      algorithm.initialAction.rnDeriv referenceAlgorithm.initialAction
        (history ⟨0, Finset.mem_Iic.mpr le_rfl⟩).1
  | n + 1, history =>
      historyDensity algorithm referenceAlgorithm n (pairHistoryPrefix history) *
        (algorithm.policy n).rnDeriv (referenceAlgorithm.policy n)
          (pairHistoryPrefix history) (pairHistoryLast history).1

theorem measurable_historyDensity
    {Action : Type u} {Reward : Type v}
    [MeasurableSpace Action] [MeasurableSpace Reward]
    [MeasurableSpace.CountablyGenerated Action]
    (algorithm referenceAlgorithm : HistoryAlgorithm Action Reward) (n : Nat) :
    Measurable (historyDensity algorithm referenceAlgorithm n) := by
  induction n with
  | zero =>
      exact (Measure.measurable_rnDeriv _ _).comp
        (measurable_fst.comp (measurable_pi_apply _))
  | succ n ih =>
      exact (ih.comp measurable_pairHistoryPrefix).mul
        ((ProbabilityTheory.Kernel.measurable_rnDeriv _ _).comp
          (measurable_pairHistoryPrefix.prodMk
            (measurable_fst.comp measurable_pairHistoryLast)))

/-- Mapping a weighted measure transports a density pulled back by the map. -/
theorem map_withDensity_comp
    {Source : Type u} {Target : Type v}
    [MeasurableSpace Source] [MeasurableSpace Target]
    (mu : Measure Source) (map : Source -> Target) (density : Target -> ENNReal)
    (hmap : Measurable map) (hdensity : Measurable density) :
    (mu.withDensity (density ∘ map)).map map =
      (mu.map map).withDensity density := by
  ext event hevent
  rw [Measure.map_apply hmap hevent,
    MeasureTheory.withDensity_apply _ (hmap hevent),
    MeasureTheory.withDensity_apply _ hevent,
    MeasureTheory.setLIntegral_map hevent hdensity hmap]
  rfl

/-- Weighting both a composition-product base and kernel multiplies densities. -/
theorem compProd_withDensity_withDensity
    {Base : Type u} {Target : Type v}
    [MeasurableSpace Base] [MeasurableSpace Target]
    (base : Measure Base) [SFinite base]
    (kernel : ProbabilityTheory.Kernel Base Target)
    [ProbabilityTheory.IsSFiniteKernel kernel]
    (baseDensity : Base -> ENNReal)
    (kernelDensity : Base -> Target -> ENNReal)
    (hbaseDensity : Measurable baseDensity)
    (hkernelDensity : Measurable (Function.uncurry kernelDensity))
    [ProbabilityTheory.IsSFiniteKernel (kernel.withDensity kernelDensity)] :
    base.withDensity baseDensity ⊗ₘ kernel.withDensity kernelDensity =
      (base ⊗ₘ kernel).withDensity
        (fun pair => baseDensity pair.1 * kernelDensity pair.1 pair.2) := by
  rw [Measure.compProd_withDensity hkernelDensity,
    compProd_withDensity_left base kernel baseDensity hbaseDensity]
  exact (MeasureTheory.withDensity_mul _
    (hbaseDensity.comp measurable_fst) hkernelDensity).symm

set_option maxHeartbeats 800000 in
/-- Kernel RN derivatives reconstruct a pointwise absolutely continuous kernel. -/
theorem kernel_withDensity_rnDeriv_eq_of_absolutelyContinuous
    {Index : Type u} {Target : Type v}
    [MeasurableSpace Index] [MeasurableSpace Target]
    [MeasurableSpace.CountableOrCountablyGenerated Index Target]
    (kernel referenceKernel : ProbabilityTheory.Kernel Index Target)
    [ProbabilityTheory.IsFiniteKernel kernel]
    [ProbabilityTheory.IsFiniteKernel referenceKernel]
    (h : forall index, kernel index ≪ referenceKernel index) :
    referenceKernel.withDensity (kernel.rnDeriv referenceKernel) = kernel := by
  apply ProbabilityTheory.Kernel.ext
  intro index
  exact ProbabilityTheory.Kernel.withDensity_rnDeriv_eq (h index)

set_option maxHeartbeats 800000 in
/-- Weighting the left kernel of a kernel composition product. -/
theorem kernel_compProd_withDensity_left
    {Index : Type u} {Middle : Type v} {Target : Type w}
    [MeasurableSpace Index] [MeasurableSpace Middle] [MeasurableSpace Target]
    (kernel : ProbabilityTheory.Kernel Index Middle)
    (nextKernel : ProbabilityTheory.Kernel (Index × Middle) Target)
    [ProbabilityTheory.IsSFiniteKernel kernel]
    [ProbabilityTheory.IsSFiniteKernel nextKernel]
    (density : Index -> Middle -> ENNReal)
    (hdensity : Measurable (Function.uncurry density))
    [ProbabilityTheory.IsSFiniteKernel (kernel.withDensity density)] :
    kernel.withDensity density ⊗ₖ nextKernel =
      (kernel ⊗ₖ nextKernel).withDensity
        (fun index pair => density index pair.1) := by
  apply ProbabilityTheory.Kernel.ext
  intro index
  calc
    (kernel.withDensity density ⊗ₖ nextKernel) index =
        (kernel index).withDensity (density index) ⊗ₘ
          nextKernel.sectR index := by
      rw [ProbabilityTheory.Kernel.compProd_apply_eq_compProd_sectR,
        ProbabilityTheory.Kernel.withDensity_apply _ hdensity]
    _ = (kernel index ⊗ₘ nextKernel.sectR index).withDensity
          (fun pair => density index pair.1) :=
      compProd_withDensity_left _ _ _ (by fun_prop)
    _ = ((kernel ⊗ₖ nextKernel).withDensity
          (fun index pair => density index pair.1)) index := by
      rw [← ProbabilityTheory.Kernel.compProd_apply_eq_compProd_sectR,
        ProbabilityTheory.Kernel.withDensity_apply _ (by fun_prop)]

/-- The actual one-step pair kernel is a density-weighted reference kernel. -/
theorem historyStepKernel_eq_withDensity
    {Action : Type u} {Reward : Type v}
    [MeasurableSpace Action] [MeasurableSpace Reward]
    (n : Nat)
    [MeasurableSpace.CountableOrCountablyGenerated
      (History.FinitePairHistory Action Reward n) Action]
    (algorithm referenceAlgorithm : HistoryAlgorithm Action Reward)
    (environment : HistoryEnvironment Action Reward)
    (hcontinuous :
      HistoryAlgorithmAbsolutelyContinuous algorithm referenceAlgorithm) :
    historyStepKernel algorithm environment n =
      (historyStepKernel referenceAlgorithm environment n).withDensity
        (fun history pair =>
          (algorithm.policy n).rnDeriv (referenceAlgorithm.policy n)
            history pair.1) := by
  let actionDensity :=
    (algorithm.policy n).rnDeriv (referenceAlgorithm.policy n)
  have hpolicy :
      (referenceAlgorithm.policy n).withDensity actionDensity =
        algorithm.policy n :=
    kernel_withDensity_rnDeriv_eq_of_absolutelyContinuous
      (algorithm.policy n) (referenceAlgorithm.policy n)
      (hcontinuous.policy n)
  change algorithm.policy n ⊗ₖ environment.feedback n =
    (referenceAlgorithm.policy n ⊗ₖ environment.feedback n).withDensity
      (fun history pair => actionDensity history pair.1)
  calc
    algorithm.policy n ⊗ₖ environment.feedback n =
        (referenceAlgorithm.policy n).withDensity actionDensity ⊗ₖ
          environment.feedback n :=
      congrArg (fun policy => policy ⊗ₖ environment.feedback n) hpolicy.symm
    _ = _ := kernel_compProd_withDensity_left
      (referenceAlgorithm.policy n) (environment.feedback n)
      actionDensity (ProbabilityTheory.Kernel.measurable_rnDeriv _ _)

/--
Process contract using the combined initial and successor pair laws. Split
action/feedback conditional laws are assembled into this contract below.
-/
structure IsHistoryAlgorithmEnvironmentSequence
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
  initialPair_map_eq :
    mu.map (fun omega => (action omega 0, reward omega 0)) =
      algorithm.initialAction ⊗ₘ environment.initialFeedback
  step_condDistrib : forall n,
    ProbabilityTheory.condDistrib
        (fun omega => (action omega (n + 1), reward omega (n + 1)))
        (fun omega => History.finitePairHistoryOfTrace
          (action omega) (reward omega) n) mu =ᵐ[
      mu.map (fun omega => History.finitePairHistoryOfTrace
        (action omega) (reward omega) n)]
      historyStepKernel algorithm environment n

/-- Build the pair-law process contract from LML-shaped split fields. -/
noncomputable def isHistoryAlgorithmEnvironmentSequence_of_split
    {Omega : Type w} {Action : Type u} {Reward : Type v}
    [MeasurableSpace Omega]
    [MeasurableSpace Action] [StandardBorelSpace Action] [Nonempty Action]
    [MeasurableSpace Reward] [StandardBorelSpace Reward] [Nonempty Reward]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Reward)
    (algorithm : HistoryAlgorithm Action Reward)
    (environment : HistoryEnvironment Action Reward)
    (haction : forall n, Measurable (fun omega => action omega n))
    (hreward : forall n, Measurable (fun omega => reward omega n))
    (hinitialAction :
      mu.map (fun omega => action omega 0) = algorithm.initialAction)
    (hinitialFeedback :
      ProbabilityTheory.condDistrib (fun omega => reward omega 0)
          (fun omega => action omega 0) mu =ᵐ[
        mu.map (fun omega => action omega 0)] environment.initialFeedback)
    (hpolicy : forall n,
      ProbabilityTheory.condDistrib (fun omega => action omega (n + 1))
          (fun omega => History.finitePairHistoryOfTrace
            (action omega) (reward omega) n) mu =ᵐ[
        mu.map (fun omega => History.finitePairHistoryOfTrace
          (action omega) (reward omega) n)] algorithm.policy n)
    (hfeedback : forall n,
      ProbabilityTheory.condDistrib (fun omega => reward omega (n + 1))
          (fun omega =>
            (History.finitePairHistoryOfTrace
              (action omega) (reward omega) n, action omega (n + 1))) mu =ᵐ[
        mu.map (fun omega =>
          (History.finitePairHistoryOfTrace
            (action omega) (reward omega) n, action omega (n + 1)))]
        environment.feedback n) :
    IsHistoryAlgorithmEnvironmentSequence mu action reward
      algorithm environment where
  measurable_action := haction
  measurable_reward := hreward
  initialPair_map_eq :=
    RewardKernel.pair_map_eq_compProd_of_map_eq_of_condDistrib
      mu (fun omega => action omega 0) (fun omega => reward omega 0)
      (hreward 0) algorithm.initialAction environment.initialFeedback
      hinitialAction hinitialFeedback
  step_condDistrib := fun n => by
    simpa only [historyStepKernel] using
      RewardKernel.condDistrib_pair_ae_eq_compProd_of_split
        mu
        (fun omega => History.finitePairHistoryOfTrace
          (action omega) (reward omega) n)
        (History.measurable_finitePairHistoryOfTrace
          action reward haction hreward n)
        (fun omega => action omega (n + 1)) (haction (n + 1))
        (fun omega => reward omega (n + 1)) (hreward (n + 1))
        (algorithm.policy n) (environment.feedback n)
        (hpolicy n) (hfeedback n)

/--
The process contract identifies the joint law of the current finite history and
the next action/reward pair with the corresponding measure composition product.
-/
theorem nextPairJointLaw_eq_compProd
    {Omega : Type w} {Action : Type u} {Reward : Type v}
    [MeasurableSpace Omega]
    [MeasurableSpace Action] [StandardBorelSpace Action] [Nonempty Action]
    [MeasurableSpace Reward] [StandardBorelSpace Reward] [Nonempty Reward]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Reward)
    (algorithm : HistoryAlgorithm Action Reward)
    (environment : HistoryEnvironment Action Reward)
    (source : IsHistoryAlgorithmEnvironmentSequence mu action reward
      algorithm environment)
    (n : Nat) :
    mu.map (fun omega =>
        (History.finitePairHistoryOfTrace (action omega) (reward omega) n,
          (action omega (n + 1), reward omega (n + 1)))) =
      mu.map (fun omega =>
          History.finitePairHistoryOfTrace (action omega) (reward omega) n) ⊗ₘ
        historyStepKernel algorithm environment n := by
  exact
    (ProbabilityTheory.condDistrib_ae_eq_iff_measure_eq_compProd
      (fun omega =>
        History.finitePairHistoryOfTrace (action omega) (reward omega) n)
      ((source.measurable_action (n + 1)).prod
        (source.measurable_reward (n + 1))).aemeasurable
      (historyStepKernel algorithm environment n)).mp
      (source.step_condDistrib n)

set_option maxHeartbeats 1600000 in
/--
Finite-history algorithm-density transport.

Two history-dependent stochastic policies use the same feedback environment.
Pointwise absolute continuity of the actual policy with respect to the
reference policy implies that every inclusive finite pair-history law is the
reference law weighted by the recursive product of action likelihood ratios.
-/
theorem finitePairHistory_map_eq_withDensity
    {Omega : Type w} {OmegaRef : Type x}
    {Action : Type u} {Reward : Type v}
    [MeasurableSpace Omega] [MeasurableSpace OmegaRef]
    [MeasurableSpace Action] [StandardBorelSpace Action] [Nonempty Action]
    [MeasurableSpace Reward] [StandardBorelSpace Reward] [Nonempty Reward]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (muRef : Measure OmegaRef) [IsFiniteMeasure muRef]
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Reward)
    (actionRef : OmegaRef -> ActionTrace Action)
    (rewardRef : OmegaRef -> RewardTrace Reward)
    (algorithm referenceAlgorithm : HistoryAlgorithm Action Reward)
    (environment : HistoryEnvironment Action Reward)
    (source : IsHistoryAlgorithmEnvironmentSequence mu action reward
      algorithm environment)
    (referenceSource : IsHistoryAlgorithmEnvironmentSequence
      muRef actionRef rewardRef referenceAlgorithm environment)
    (hcontinuous :
      HistoryAlgorithmAbsolutelyContinuous algorithm referenceAlgorithm)
    (n : Nat) :
    mu.map (fun omega =>
        History.finitePairHistoryOfTrace (action omega) (reward omega) n) =
      (muRef.map (fun omega =>
        History.finitePairHistoryOfTrace
          (actionRef omega) (rewardRef omega) n)).withDensity
        (historyDensity algorithm referenceAlgorithm n) := by
  induction n with
  | zero =>
      let pairActual : Omega -> Action × Reward :=
        fun omega => (action omega 0, reward omega 0)
      let pairRef : OmegaRef -> Action × Reward :=
        fun omega => (actionRef omega 0, rewardRef omega 0)
      have hpairActual : Measurable pairActual :=
        (source.measurable_action 0).prod (source.measurable_reward 0)
      have hpairRef : Measurable pairRef :=
        (referenceSource.measurable_action 0).prod
          (referenceSource.measurable_reward 0)
      have hactualFunction :
          (fun omega =>
            History.finitePairHistoryOfTrace
              (action omega) (reward omega) 0) =
            singletonPairHistory ∘ pairActual := by
        funext omega
        funext i
        have hi : i.1 = 0 :=
          Nat.eq_zero_of_le_zero (Finset.mem_Iic.mp i.2)
        simp [pairActual, singletonPairHistory,
          History.finitePairHistoryOfTrace, hi]
      have hrefFunction :
          (fun omega =>
            History.finitePairHistoryOfTrace
              (actionRef omega) (rewardRef omega) 0) =
            singletonPairHistory ∘ pairRef := by
        funext omega
        funext i
        have hi : i.1 = 0 :=
          Nat.eq_zero_of_le_zero (Finset.mem_Iic.mp i.2)
        simp [pairRef, singletonPairHistory,
          History.finitePairHistoryOfTrace, hi]
      have hinitialDensity :
          algorithm.initialAction =
            referenceAlgorithm.initialAction.withDensity
              (algorithm.initialAction.rnDeriv
                referenceAlgorithm.initialAction) :=
        (Measure.withDensity_rnDeriv_eq _ _
          hcontinuous.initialAction).symm
      have hpairDensity :
          algorithm.initialAction ⊗ₘ environment.initialFeedback =
            (referenceAlgorithm.initialAction ⊗ₘ
              environment.initialFeedback).withDensity
                (fun pair =>
                  algorithm.initialAction.rnDeriv
                    referenceAlgorithm.initialAction pair.1) := by
        calc
          algorithm.initialAction ⊗ₘ environment.initialFeedback =
              referenceAlgorithm.initialAction.withDensity
                  (algorithm.initialAction.rnDeriv
                    referenceAlgorithm.initialAction) ⊗ₘ
                environment.initialFeedback :=
            congrArg (fun initial =>
              initial ⊗ₘ environment.initialFeedback) hinitialDensity
          _ = _ := compProd_withDensity_left
            referenceAlgorithm.initialAction environment.initialFeedback
            (algorithm.initialAction.rnDeriv
              referenceAlgorithm.initialAction)
            (Measure.measurable_rnDeriv _ _)
      have hpushDensity :
          ((referenceAlgorithm.initialAction ⊗ₘ
              environment.initialFeedback).withDensity
                (fun pair =>
                  algorithm.initialAction.rnDeriv
                    referenceAlgorithm.initialAction pair.1)).map
              singletonPairHistory =
            ((referenceAlgorithm.initialAction ⊗ₘ
                environment.initialFeedback).map
              singletonPairHistory).withDensity
                (historyDensity algorithm referenceAlgorithm 0) := by
        simpa [Function.comp_def, historyDensity, singletonPairHistory] using
          map_withDensity_comp
            (referenceAlgorithm.initialAction ⊗ₘ
              environment.initialFeedback)
            singletonPairHistory
            (historyDensity algorithm referenceAlgorithm 0)
            measurable_singletonPairHistory
            (measurable_historyDensity algorithm referenceAlgorithm 0)
      calc
        mu.map (fun omega =>
            History.finitePairHistoryOfTrace
              (action omega) (reward omega) 0) =
            (mu.map pairActual).map singletonPairHistory := by
          rw [hactualFunction]
          exact (Measure.map_map measurable_singletonPairHistory
            hpairActual).symm
        _ = (algorithm.initialAction ⊗ₘ
            environment.initialFeedback).map singletonPairHistory := by
          rw [source.initialPair_map_eq]
        _ = ((referenceAlgorithm.initialAction ⊗ₘ
              environment.initialFeedback).withDensity
            (fun pair =>
              algorithm.initialAction.rnDeriv
                referenceAlgorithm.initialAction pair.1)).map
              singletonPairHistory := by rw [hpairDensity]
        _ = ((referenceAlgorithm.initialAction ⊗ₘ
              environment.initialFeedback).map
            singletonPairHistory).withDensity
              (historyDensity algorithm referenceAlgorithm 0) :=
          hpushDensity
        _ = ((muRef.map pairRef).map
              singletonPairHistory).withDensity
                (historyDensity algorithm referenceAlgorithm 0) := by
          rw [referenceSource.initialPair_map_eq]
        _ = (muRef.map (fun omega =>
              History.finitePairHistoryOfTrace
                (actionRef omega) (rewardRef omega) 0)).withDensity
              (historyDensity algorithm referenceAlgorithm 0) := by
          rw [hrefFunction, Measure.map_map measurable_singletonPairHistory
            hpairRef]
  | succ n ih =>
      let historyActual : Omega ->
          History.FinitePairHistory Action Reward n :=
        fun omega =>
          History.finitePairHistoryOfTrace
            (action omega) (reward omega) n
      let historyRef : OmegaRef ->
          History.FinitePairHistory Action Reward n :=
        fun omega =>
          History.finitePairHistoryOfTrace
            (actionRef omega) (rewardRef omega) n
      let nextActual : Omega -> Action × Reward :=
        fun omega => (action omega (n + 1), reward omega (n + 1))
      let nextRef : OmegaRef -> Action × Reward :=
        fun omega => (actionRef omega (n + 1), rewardRef omega (n + 1))
      let jointActual : Omega ->
          History.FinitePairHistory Action Reward n × (Action × Reward) :=
        fun omega => (historyActual omega, nextActual omega)
      let jointRef : OmegaRef ->
          History.FinitePairHistory Action Reward n × (Action × Reward) :=
        fun omega => (historyRef omega, nextRef omega)
      let extend :
          History.FinitePairHistory Action Reward n × (Action × Reward) ->
            History.FinitePairHistory Action Reward (n + 1) :=
        fun input => History.extendPairHistorySucc input.1 input.2
      let stepDensity :
          History.FinitePairHistory Action Reward n ->
            Action × Reward -> ENNReal :=
        fun history pair =>
          (algorithm.policy n).rnDeriv (referenceAlgorithm.policy n)
            history pair.1
      have hhistoryActual : Measurable historyActual :=
        History.measurable_finitePairHistoryOfTrace
          action reward source.measurable_action source.measurable_reward n
      have hhistoryRef : Measurable historyRef :=
        History.measurable_finitePairHistoryOfTrace
          actionRef rewardRef referenceSource.measurable_action
            referenceSource.measurable_reward n
      have hnextActual : Measurable nextActual :=
        (source.measurable_action (n + 1)).prod
          (source.measurable_reward (n + 1))
      have hnextRef : Measurable nextRef :=
        (referenceSource.measurable_action (n + 1)).prod
          (referenceSource.measurable_reward (n + 1))
      have hjointActual : Measurable jointActual :=
        hhistoryActual.prod hnextActual
      have hjointRef : Measurable jointRef :=
        hhistoryRef.prod hnextRef
      have hextend : Measurable extend :=
        History.measurable_extendPairHistorySucc
      have hstepDensity : Measurable (Function.uncurry stepDensity) := by
        simpa [stepDensity, Function.uncurry] using
          (ProbabilityTheory.Kernel.measurable_rnDeriv
            (algorithm.policy n) (referenceAlgorithm.policy n)).comp
              (measurable_fst.prodMk
                (measurable_fst.comp measurable_snd))
      have hstepLaw :
          historyStepKernel algorithm environment n =
            (historyStepKernel referenceAlgorithm environment n).withDensity
              stepDensity := by
        exact historyStepKernel_eq_withDensity n algorithm referenceAlgorithm
          environment hcontinuous
      letI : ProbabilityTheory.IsSFiniteKernel
          ((historyStepKernel referenceAlgorithm environment n).withDensity
            stepDensity) := by
        rw [← hstepLaw]
        infer_instance
      have hjointLaw :
          mu.map jointActual =
            (muRef.map jointRef).withDensity
              (fun pair =>
                historyDensity algorithm referenceAlgorithm n pair.1 *
                  stepDensity pair.1 pair.2) := by
        calc
          mu.map jointActual =
              mu.map historyActual ⊗ₘ
                historyStepKernel algorithm environment n := by
            simpa [jointActual, historyActual, nextActual] using
              nextPairJointLaw_eq_compProd
                mu action reward algorithm environment source n
          _ = (muRef.map historyRef).withDensity
                (historyDensity algorithm referenceAlgorithm n) ⊗ₘ
              (historyStepKernel referenceAlgorithm environment n).withDensity
                stepDensity := by rw [ih, hstepLaw]
          _ = _ := compProd_withDensity_withDensity
            (muRef.map historyRef)
            (historyStepKernel referenceAlgorithm environment n)
            (historyDensity algorithm referenceAlgorithm n)
            stepDensity
            (measurable_historyDensity algorithm referenceAlgorithm n)
            hstepDensity
          _ = (muRef.map jointRef).withDensity
                (fun pair =>
                  historyDensity algorithm referenceAlgorithm n pair.1 *
                    stepDensity pair.1 pair.2) := by
            congr 1
            simpa [jointRef, historyRef, nextRef] using
              (nextPairJointLaw_eq_compProd
                muRef actionRef rewardRef referenceAlgorithm environment
                  referenceSource n).symm
      have hcombinedDensity :
          (fun pair =>
            historyDensity algorithm referenceAlgorithm n pair.1 *
              stepDensity pair.1 pair.2) =
            historyDensity algorithm referenceAlgorithm (n + 1) ∘ extend := by
        funext pair
        simp [historyDensity, stepDensity, extend]
      have hactualSucc :
          mu.map (fun omega =>
              History.finitePairHistoryOfTrace
                (action omega) (reward omega) (n + 1)) =
            (mu.map jointActual).map extend := by
        rw [Measure.map_map hextend hjointActual]
        apply Measure.map_congr
        filter_upwards with omega
        exact (History.finitePairHistoryOfTrace_succ
          (action omega) (reward omega) n)
      have hrefSucc :
          muRef.map (fun omega =>
              History.finitePairHistoryOfTrace
                (actionRef omega) (rewardRef omega) (n + 1)) =
            (muRef.map jointRef).map extend := by
        rw [Measure.map_map hextend hjointRef]
        apply Measure.map_congr
        filter_upwards with omega
        exact (History.finitePairHistoryOfTrace_succ
          (actionRef omega) (rewardRef omega) n)
      calc
        mu.map (fun omega =>
            History.finitePairHistoryOfTrace
              (action omega) (reward omega) (n + 1)) =
            (mu.map jointActual).map extend := hactualSucc
        _ = ((muRef.map jointRef).withDensity
              (fun pair =>
                historyDensity algorithm referenceAlgorithm n pair.1 *
                  stepDensity pair.1 pair.2)).map extend := by
          rw [hjointLaw]
        _ = ((muRef.map jointRef).withDensity
              (historyDensity algorithm referenceAlgorithm (n + 1) ∘
                extend)).map extend := by rw [hcombinedDensity]
        _ = ((muRef.map jointRef).map extend).withDensity
              (historyDensity algorithm referenceAlgorithm (n + 1)) :=
          map_withDensity_comp
            (muRef.map jointRef) extend
            (historyDensity algorithm referenceAlgorithm (n + 1))
            hextend
            (measurable_historyDensity algorithm referenceAlgorithm (n + 1))
        _ = (muRef.map (fun omega =>
              History.finitePairHistoryOfTrace
                (actionRef omega) (rewardRef omega) (n + 1))).withDensity
              (historyDensity algorithm referenceAlgorithm (n + 1)) := by
          rw [hrefSucc]

/--
Environment-indexed process realization for algorithm-density transport.

The regular conditional sample laws `condDistrib id env mu` and
`condDistrib id referenceEnv referenceMu` must satisfy the actual and
reference process contracts almost everywhere. The compared algorithms share
the same environment-indexed feedback law.
-/
structure ConditionalHistoryAlgorithmDensitySource
    {Omega : Type u} {OmegaRef : Type v} {Env : Type w}
    {Action : Type x} {Reward : Type y}
    [MeasurableSpace Omega] [StandardBorelSpace Omega] [Nonempty Omega]
    [MeasurableSpace OmegaRef] [StandardBorelSpace OmegaRef]
    [Nonempty OmegaRef]
    [MeasurableSpace Env]
    [MeasurableSpace Action] [StandardBorelSpace Action] [Nonempty Action]
    [MeasurableSpace Reward] [StandardBorelSpace Reward] [Nonempty Reward]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (env : Omega -> Env)
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Reward)
    (referenceMu : Measure OmegaRef) [IsFiniteMeasure referenceMu]
    (referenceEnv : OmegaRef -> Env)
    (referenceAction : OmegaRef -> ActionTrace Action)
    (referenceReward : OmegaRef -> RewardTrace Reward)
    (algorithm referenceAlgorithm : HistoryAlgorithm Action Reward)
    (feedbackEnvironment : Env -> HistoryEnvironment Action Reward) : Prop where
  measurable_env : Measurable env
  measurable_action : forall n, Measurable (fun omega => action omega n)
  measurable_reward : forall n, Measurable (fun omega => reward omega n)
  measurable_referenceEnv : Measurable referenceEnv
  measurable_referenceAction :
    forall n, Measurable (fun omega => referenceAction omega n)
  measurable_referenceReward :
    forall n, Measurable (fun omega => referenceReward omega n)
  env_map_eq : mu.map env = referenceMu.map referenceEnv
  absolutelyContinuous :
    HistoryAlgorithmAbsolutelyContinuous algorithm referenceAlgorithm
  actual_process : ∀ᵐ environment ∂mu.map env,
    IsHistoryAlgorithmEnvironmentSequence
      (ProbabilityTheory.condDistrib id env mu environment)
      action reward algorithm (feedbackEnvironment environment)
  reference_process : ∀ᵐ environment ∂referenceMu.map referenceEnv,
    IsHistoryAlgorithmEnvironmentSequence
      (ProbabilityTheory.condDistrib id referenceEnv referenceMu environment)
      referenceAction referenceReward referenceAlgorithm
        (feedbackEnvironment environment)

/--
The environment-indexed process realization produces the conditional finite
history density law required by the posterior-invariance source constructor.
-/
theorem condDistrib_finitePairHistory_eq_withDensity_of_conditionalProcessSource
    {Omega : Type u} {OmegaRef : Type v} {Env : Type w}
    {Action : Type x} {Reward : Type y}
    [MeasurableSpace Omega] [StandardBorelSpace Omega] [Nonempty Omega]
    [MeasurableSpace OmegaRef] [StandardBorelSpace OmegaRef]
    [Nonempty OmegaRef]
    [MeasurableSpace Env]
    [MeasurableSpace Action] [StandardBorelSpace Action] [Nonempty Action]
    [MeasurableSpace Reward] [StandardBorelSpace Reward] [Nonempty Reward]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (env : Omega -> Env)
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Reward)
    (referenceMu : Measure OmegaRef) [IsFiniteMeasure referenceMu]
    (referenceEnv : OmegaRef -> Env)
    (referenceAction : OmegaRef -> ActionTrace Action)
    (referenceReward : OmegaRef -> RewardTrace Reward)
    (algorithm referenceAlgorithm : HistoryAlgorithm Action Reward)
    (feedbackEnvironment : Env -> HistoryEnvironment Action Reward)
    (source : ConditionalHistoryAlgorithmDensitySource
      mu env action reward referenceMu referenceEnv referenceAction
        referenceReward algorithm referenceAlgorithm feedbackEnvironment)
    (n : Nat) :
    ProbabilityTheory.condDistrib
        (fun omega => History.finitePairHistoryOfTrace
          (action omega) (reward omega) n) env mu =ᵐ[mu.map env]
      (ProbabilityTheory.condDistrib
        (fun omega => History.finitePairHistoryOfTrace
          (referenceAction omega) (referenceReward omega) n)
        referenceEnv referenceMu).withDensity
          (fun _ history =>
            historyDensity algorithm referenceAlgorithm n history) := by
  let actualHistory := fun omega =>
    History.finitePairHistoryOfTrace (action omega) (reward omega) n
  let referenceHistory := fun omega =>
    History.finitePairHistoryOfTrace
      (referenceAction omega) (referenceReward omega) n
  have hactualHistory : Measurable actualHistory :=
    History.measurable_finitePairHistoryOfTrace
      action reward source.measurable_action source.measurable_reward n
  have hreferenceHistory : Measurable referenceHistory :=
    History.measurable_finitePairHistoryOfTrace
      referenceAction referenceReward source.measurable_referenceAction
        source.measurable_referenceReward n
  have hactualMap :
      ProbabilityTheory.condDistrib actualHistory env mu =ᵐ[mu.map env]
        (ProbabilityTheory.condDistrib id env mu).map actualHistory := by
    simpa [Function.comp_def] using
      (ProbabilityTheory.condDistrib_comp
        (Y := id) env measurable_id.aemeasurable hactualHistory)
  have hreferenceMap :
      ProbabilityTheory.condDistrib referenceHistory referenceEnv referenceMu
          =ᵐ[referenceMu.map referenceEnv]
        (ProbabilityTheory.condDistrib id referenceEnv referenceMu).map
          referenceHistory := by
    simpa [Function.comp_def] using
      (ProbabilityTheory.condDistrib_comp
        (Y := id) referenceEnv measurable_id.aemeasurable hreferenceHistory)
  have hreferenceMap' :
      ProbabilityTheory.condDistrib referenceHistory referenceEnv referenceMu
          =ᵐ[mu.map env]
        (ProbabilityTheory.condDistrib id referenceEnv referenceMu).map
          referenceHistory := by
    rw [source.env_map_eq]
    exact hreferenceMap
  have hreferenceProcess :
      ∀ᵐ environment ∂mu.map env,
        IsHistoryAlgorithmEnvironmentSequence
          (ProbabilityTheory.condDistrib id referenceEnv referenceMu environment)
          referenceAction referenceReward referenceAlgorithm
            (feedbackEnvironment environment) := by
    rw [source.env_map_eq]
    exact source.reference_process
  have hdensityKernel :
      Measurable (Function.uncurry
        (fun _ : Env => historyDensity algorithm referenceAlgorithm n)) :=
    (measurable_historyDensity algorithm referenceAlgorithm n).comp
      measurable_snd
  filter_upwards [hactualMap, hreferenceMap', source.actual_process,
    hreferenceProcess] with environment hactual hreference
      hactualProcess hreferenceProcessAt
  rw [hactual,
    ProbabilityTheory.Kernel.withDensity_apply _ hdensityKernel,
    hreference,
    ProbabilityTheory.Kernel.map_apply _ hactualHistory,
    ProbabilityTheory.Kernel.map_apply _ hreferenceHistory]
  exact finitePairHistory_map_eq_withDensity
    (ProbabilityTheory.condDistrib id env mu environment)
    (ProbabilityTheory.condDistrib id referenceEnv referenceMu environment)
    action reward referenceAction referenceReward
    algorithm referenceAlgorithm (feedbackEnvironment environment)
    hactualProcess hreferenceProcessAt source.absolutelyContinuous n

/--
Finite-prefix Thompson probability matching produced directly from the
environment-indexed recursive process contracts.
-/
theorem finitePairReferencePolicySampler_condDistrib_action_ae_eq_bestAction_of_conditionalProcessSource
    {Omega : Type u} {OmegaRef : Type v} {Env : Type w}
    {Action : Type x} {Reward : Type y}
    [MeasurableSpace Omega] [StandardBorelSpace Omega] [Nonempty Omega]
    [MeasurableSpace OmegaRef] [StandardBorelSpace OmegaRef]
    [Nonempty OmegaRef]
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [StandardBorelSpace Action] [Nonempty Action]
    [MeasurableSpace Reward] [StandardBorelSpace Reward] [Nonempty Reward]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (env : Omega -> Env)
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Reward)
    (referenceMu : Measure OmegaRef) [IsFiniteMeasure referenceMu]
    (referenceEnv : OmegaRef -> Env)
    (referenceAction : OmegaRef -> ActionTrace Action)
    (referenceReward : OmegaRef -> RewardTrace Reward)
    (algorithm referenceAlgorithm : HistoryAlgorithm Action Reward)
    (feedbackEnvironment : Env -> HistoryEnvironment Action Reward)
    (source : ConditionalHistoryAlgorithmDensitySource
      mu env action reward referenceMu referenceEnv referenceAction
        referenceReward algorithm referenceAlgorithm feedbackEnvironment)
    (n : Nat)
    (bestAction : Env -> Action) (hbestAction : Measurable bestAction) :
    let actualHistory := fun omega => History.finitePairHistoryOfTrace
      (action omega) (reward omega) n
    let referenceHistory := fun omega => History.finitePairHistoryOfTrace
      (referenceAction omega) (referenceReward omega) n
    let policy := referenceActionKernel referenceMu referenceEnv referenceHistory
      source.measurable_referenceEnv
      (History.measurable_finitePairHistoryOfTrace
        referenceAction referenceReward source.measurable_referenceAction
          source.measurable_referenceReward n)
      bestAction hbestAction
    let sampler := policySamplerMeasure mu actualHistory
      (History.measurable_finitePairHistoryOfTrace
        action reward source.measurable_action source.measurable_reward n) policy
    ProbabilityTheory.condDistrib policySamplerAction
        (policySamplerHistory actualHistory) sampler =ᵐ[
      sampler.map (policySamplerHistory actualHistory)]
      ProbabilityTheory.condDistrib (bestAction ∘ policySamplerEnv env)
        (policySamplerHistory actualHistory) sampler := by
  exact
    finitePairReferencePolicySampler_condDistrib_action_ae_eq_bestAction_of_condDistrib_history_withDensity
      mu env action reward source.measurable_env
      source.measurable_action source.measurable_reward
      referenceMu referenceEnv referenceAction referenceReward
      source.measurable_referenceEnv source.measurable_referenceAction
      source.measurable_referenceReward n
      (historyDensity algorithm referenceAlgorithm n)
      (measurable_historyDensity algorithm referenceAlgorithm n)
      source.env_map_eq
      (condDistrib_finitePairHistory_eq_withDensity_of_conditionalProcessSource
        mu env action reward referenceMu referenceEnv referenceAction
          referenceReward algorithm referenceAlgorithm feedbackEnvironment
          source n)
      bestAction hbestAction

/--
LML-shaped split laws for one algorithm/environment process under the regular
conditional sample measure at almost every environment.
-/
structure ConditionalHistoryAlgorithmEnvironmentSplitSource
    {Omega : Type u} {Env : Type v} {Action : Type w} {Reward : Type x}
    [MeasurableSpace Omega] [StandardBorelSpace Omega] [Nonempty Omega]
    [MeasurableSpace Env]
    [MeasurableSpace Action] [StandardBorelSpace Action] [Nonempty Action]
    [MeasurableSpace Reward] [StandardBorelSpace Reward] [Nonempty Reward]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (env : Omega -> Env)
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Reward)
    (algorithm : HistoryAlgorithm Action Reward)
    (feedbackEnvironment : Env -> HistoryEnvironment Action Reward) : Prop where
  measurable_env : Measurable env
  measurable_action : forall n, Measurable (fun omega => action omega n)
  measurable_reward : forall n, Measurable (fun omega => reward omega n)
  initial_action : ∀ᵐ environment ∂mu.map env,
    (ProbabilityTheory.condDistrib id env mu environment).map
        (fun omega => action omega 0) =
      algorithm.initialAction
  initial_feedback : ∀ᵐ environment ∂mu.map env,
    ProbabilityTheory.condDistrib
        (fun omega => reward omega 0)
        (fun omega => action omega 0)
        (ProbabilityTheory.condDistrib id env mu environment) =ᵐ[
      (ProbabilityTheory.condDistrib id env mu environment).map
        (fun omega => action omega 0)]
      (feedbackEnvironment environment).initialFeedback
  policy : forall n, ∀ᵐ environment ∂mu.map env,
    ProbabilityTheory.condDistrib
        (fun omega => action omega (n + 1))
        (fun omega => History.finitePairHistoryOfTrace
          (action omega) (reward omega) n)
        (ProbabilityTheory.condDistrib id env mu environment) =ᵐ[
      (ProbabilityTheory.condDistrib id env mu environment).map
        (fun omega => History.finitePairHistoryOfTrace
          (action omega) (reward omega) n)]
      algorithm.policy n
  feedback : forall n, ∀ᵐ environment ∂mu.map env,
    ProbabilityTheory.condDistrib
        (fun omega => reward omega (n + 1))
        (fun omega =>
          (History.finitePairHistoryOfTrace
            (action omega) (reward omega) n, action omega (n + 1)))
        (ProbabilityTheory.condDistrib id env mu environment) =ᵐ[
      (ProbabilityTheory.condDistrib id env mu environment).map
        (fun omega =>
          (History.finitePairHistoryOfTrace
            (action omega) (reward omega) n, action omega (n + 1)))]
      (feedbackEnvironment environment).feedback n

/--
Actual/reference split conditional-process laws together with the common
environment marginal and policy absolute-continuity contract.
-/
structure ConditionalHistoryAlgorithmDensitySplitSource
    {Omega : Type u} {OmegaRef : Type v} {Env : Type w}
    {Action : Type x} {Reward : Type y}
    [MeasurableSpace Omega] [StandardBorelSpace Omega] [Nonempty Omega]
    [MeasurableSpace OmegaRef] [StandardBorelSpace OmegaRef]
    [Nonempty OmegaRef]
    [MeasurableSpace Env]
    [MeasurableSpace Action] [StandardBorelSpace Action] [Nonempty Action]
    [MeasurableSpace Reward] [StandardBorelSpace Reward] [Nonempty Reward]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (env : Omega -> Env)
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Reward)
    (referenceMu : Measure OmegaRef) [IsFiniteMeasure referenceMu]
    (referenceEnv : OmegaRef -> Env)
    (referenceAction : OmegaRef -> ActionTrace Action)
    (referenceReward : OmegaRef -> RewardTrace Reward)
    (algorithm referenceAlgorithm : HistoryAlgorithm Action Reward)
    (feedbackEnvironment : Env -> HistoryEnvironment Action Reward) : Prop where
  actual : ConditionalHistoryAlgorithmEnvironmentSplitSource
    mu env action reward algorithm feedbackEnvironment
  reference : ConditionalHistoryAlgorithmEnvironmentSplitSource
    referenceMu referenceEnv referenceAction referenceReward referenceAlgorithm
      feedbackEnvironment
  env_map_eq : mu.map env = referenceMu.map referenceEnv
  absolutelyContinuous :
    HistoryAlgorithmAbsolutelyContinuous algorithm referenceAlgorithm

/--
Assemble the conditional process source from the four split law families for
the actual and reference processes.
-/
noncomputable def conditionalHistoryAlgorithmDensitySource_of_split
    {Omega : Type u} {OmegaRef : Type v} {Env : Type w}
    {Action : Type x} {Reward : Type y}
    [MeasurableSpace Omega] [StandardBorelSpace Omega] [Nonempty Omega]
    [MeasurableSpace OmegaRef] [StandardBorelSpace OmegaRef]
    [Nonempty OmegaRef]
    [MeasurableSpace Env]
    [MeasurableSpace Action] [StandardBorelSpace Action] [Nonempty Action]
    [MeasurableSpace Reward] [StandardBorelSpace Reward] [Nonempty Reward]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (env : Omega -> Env)
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Reward)
    (referenceMu : Measure OmegaRef) [IsFiniteMeasure referenceMu]
    (referenceEnv : OmegaRef -> Env)
    (referenceAction : OmegaRef -> ActionTrace Action)
    (referenceReward : OmegaRef -> RewardTrace Reward)
    (algorithm referenceAlgorithm : HistoryAlgorithm Action Reward)
    (feedbackEnvironment : Env -> HistoryEnvironment Action Reward)
    (source : ConditionalHistoryAlgorithmDensitySplitSource
      mu env action reward referenceMu referenceEnv referenceAction
        referenceReward algorithm referenceAlgorithm feedbackEnvironment) :
    ConditionalHistoryAlgorithmDensitySource
      mu env action reward referenceMu referenceEnv referenceAction
        referenceReward algorithm referenceAlgorithm feedbackEnvironment := by
  have hactualPolicy : ∀ᵐ environment ∂mu.map env, forall n,
      ProbabilityTheory.condDistrib
          (fun omega => action omega (n + 1))
          (fun omega => History.finitePairHistoryOfTrace
            (action omega) (reward omega) n)
          (ProbabilityTheory.condDistrib id env mu environment) =ᵐ[
        (ProbabilityTheory.condDistrib id env mu environment).map
          (fun omega => History.finitePairHistoryOfTrace
            (action omega) (reward omega) n)]
        algorithm.policy n := by
    rw [ae_all_iff]
    exact source.actual.policy
  have hactualFeedback : ∀ᵐ environment ∂mu.map env, forall n,
      ProbabilityTheory.condDistrib
          (fun omega => reward omega (n + 1))
          (fun omega =>
            (History.finitePairHistoryOfTrace
              (action omega) (reward omega) n, action omega (n + 1)))
          (ProbabilityTheory.condDistrib id env mu environment) =ᵐ[
        (ProbabilityTheory.condDistrib id env mu environment).map
          (fun omega =>
            (History.finitePairHistoryOfTrace
              (action omega) (reward omega) n, action omega (n + 1)))]
        (feedbackEnvironment environment).feedback n := by
    rw [ae_all_iff]
    exact source.actual.feedback
  have hreferencePolicy :
      ∀ᵐ environment ∂referenceMu.map referenceEnv, forall n,
        ProbabilityTheory.condDistrib
            (fun omega => referenceAction omega (n + 1))
            (fun omega => History.finitePairHistoryOfTrace
              (referenceAction omega) (referenceReward omega) n)
            (ProbabilityTheory.condDistrib id referenceEnv referenceMu
              environment) =ᵐ[
          (ProbabilityTheory.condDistrib id referenceEnv referenceMu
            environment).map
            (fun omega => History.finitePairHistoryOfTrace
              (referenceAction omega) (referenceReward omega) n)]
          referenceAlgorithm.policy n := by
    rw [ae_all_iff]
    exact source.reference.policy
  have hreferenceFeedback :
      ∀ᵐ environment ∂referenceMu.map referenceEnv, forall n,
        ProbabilityTheory.condDistrib
            (fun omega => referenceReward omega (n + 1))
            (fun omega =>
              (History.finitePairHistoryOfTrace
                (referenceAction omega) (referenceReward omega) n,
                  referenceAction omega (n + 1)))
            (ProbabilityTheory.condDistrib id referenceEnv referenceMu
              environment) =ᵐ[
          (ProbabilityTheory.condDistrib id referenceEnv referenceMu
            environment).map
            (fun omega =>
              (History.finitePairHistoryOfTrace
                (referenceAction omega) (referenceReward omega) n,
                  referenceAction omega (n + 1)))]
          (feedbackEnvironment environment).feedback n := by
    rw [ae_all_iff]
    exact source.reference.feedback
  exact
    { measurable_env := source.actual.measurable_env
      measurable_action := source.actual.measurable_action
      measurable_reward := source.actual.measurable_reward
      measurable_referenceEnv := source.reference.measurable_env
      measurable_referenceAction := source.reference.measurable_action
      measurable_referenceReward := source.reference.measurable_reward
      env_map_eq := source.env_map_eq
      absolutelyContinuous := source.absolutelyContinuous
      actual_process := by
        filter_upwards [source.actual.initial_action,
          source.actual.initial_feedback, hactualPolicy, hactualFeedback] with
          environment hinitialAction hinitialFeedback hpolicy hfeedback
        exact isHistoryAlgorithmEnvironmentSequence_of_split
          (ProbabilityTheory.condDistrib id env mu environment)
          action reward algorithm (feedbackEnvironment environment)
          source.actual.measurable_action source.actual.measurable_reward
          hinitialAction hinitialFeedback hpolicy hfeedback
      reference_process := by
        filter_upwards [source.reference.initial_action,
          source.reference.initial_feedback, hreferencePolicy,
          hreferenceFeedback] with
          environment hinitialAction hinitialFeedback hpolicy hfeedback
        exact isHistoryAlgorithmEnvironmentSequence_of_split
          (ProbabilityTheory.condDistrib id referenceEnv referenceMu
            environment)
          referenceAction referenceReward referenceAlgorithm
          (feedbackEnvironment environment)
          source.reference.measurable_action source.reference.measurable_reward
          hinitialAction hinitialFeedback hpolicy hfeedback }

/--
The split conditional laws directly produce the conditional finite-history
density equality.
-/
theorem condDistrib_finitePairHistory_eq_withDensity_of_conditionalSplitSource
    {Omega : Type u} {OmegaRef : Type v} {Env : Type w}
    {Action : Type x} {Reward : Type y}
    [MeasurableSpace Omega] [StandardBorelSpace Omega] [Nonempty Omega]
    [MeasurableSpace OmegaRef] [StandardBorelSpace OmegaRef]
    [Nonempty OmegaRef]
    [MeasurableSpace Env]
    [MeasurableSpace Action] [StandardBorelSpace Action] [Nonempty Action]
    [MeasurableSpace Reward] [StandardBorelSpace Reward] [Nonempty Reward]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (env : Omega -> Env)
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Reward)
    (referenceMu : Measure OmegaRef) [IsFiniteMeasure referenceMu]
    (referenceEnv : OmegaRef -> Env)
    (referenceAction : OmegaRef -> ActionTrace Action)
    (referenceReward : OmegaRef -> RewardTrace Reward)
    (algorithm referenceAlgorithm : HistoryAlgorithm Action Reward)
    (feedbackEnvironment : Env -> HistoryEnvironment Action Reward)
    (source : ConditionalHistoryAlgorithmDensitySplitSource
      mu env action reward referenceMu referenceEnv referenceAction
        referenceReward algorithm referenceAlgorithm feedbackEnvironment)
    (n : Nat) :
    ProbabilityTheory.condDistrib
        (fun omega => History.finitePairHistoryOfTrace
          (action omega) (reward omega) n) env mu =ᵐ[mu.map env]
      (ProbabilityTheory.condDistrib
        (fun omega => History.finitePairHistoryOfTrace
          (referenceAction omega) (referenceReward omega) n)
        referenceEnv referenceMu).withDensity
          (fun _ history =>
            historyDensity algorithm referenceAlgorithm n history) := by
  exact
    condDistrib_finitePairHistory_eq_withDensity_of_conditionalProcessSource
      mu env action reward referenceMu referenceEnv referenceAction
        referenceReward algorithm referenceAlgorithm feedbackEnvironment
        (conditionalHistoryAlgorithmDensitySource_of_split
          mu env action reward referenceMu referenceEnv referenceAction
            referenceReward algorithm referenceAlgorithm feedbackEnvironment
            source)
        n

/--
Finite-prefix Thompson probability matching from the concrete four-family
split conditional-law interface.
-/
theorem finitePairReferencePolicySampler_condDistrib_action_ae_eq_bestAction_of_conditionalSplitSource
    {Omega : Type u} {OmegaRef : Type v} {Env : Type w}
    {Action : Type x} {Reward : Type y}
    [MeasurableSpace Omega] [StandardBorelSpace Omega] [Nonempty Omega]
    [MeasurableSpace OmegaRef] [StandardBorelSpace OmegaRef]
    [Nonempty OmegaRef]
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [StandardBorelSpace Action] [Nonempty Action]
    [MeasurableSpace Reward] [StandardBorelSpace Reward] [Nonempty Reward]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (env : Omega -> Env)
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Reward)
    (referenceMu : Measure OmegaRef) [IsFiniteMeasure referenceMu]
    (referenceEnv : OmegaRef -> Env)
    (referenceAction : OmegaRef -> ActionTrace Action)
    (referenceReward : OmegaRef -> RewardTrace Reward)
    (algorithm referenceAlgorithm : HistoryAlgorithm Action Reward)
    (feedbackEnvironment : Env -> HistoryEnvironment Action Reward)
    (source : ConditionalHistoryAlgorithmDensitySplitSource
      mu env action reward referenceMu referenceEnv referenceAction
        referenceReward algorithm referenceAlgorithm feedbackEnvironment)
    (n : Nat)
    (bestAction : Env -> Action) (hbestAction : Measurable bestAction) :
    let actualHistory := fun omega => History.finitePairHistoryOfTrace
      (action omega) (reward omega) n
    let referenceHistory := fun omega => History.finitePairHistoryOfTrace
      (referenceAction omega) (referenceReward omega) n
    let policy := referenceActionKernel referenceMu referenceEnv referenceHistory
      source.reference.measurable_env
      (History.measurable_finitePairHistoryOfTrace
        referenceAction referenceReward source.reference.measurable_action
          source.reference.measurable_reward n)
      bestAction hbestAction
    let sampler := policySamplerMeasure mu actualHistory
      (History.measurable_finitePairHistoryOfTrace
        action reward source.actual.measurable_action
          source.actual.measurable_reward n) policy
    ProbabilityTheory.condDistrib policySamplerAction
        (policySamplerHistory actualHistory) sampler =ᵐ[
      sampler.map (policySamplerHistory actualHistory)]
      ProbabilityTheory.condDistrib (bestAction ∘ policySamplerEnv env)
        (policySamplerHistory actualHistory) sampler := by
  exact
    finitePairReferencePolicySampler_condDistrib_action_ae_eq_bestAction_of_conditionalProcessSource
      mu env action reward referenceMu referenceEnv referenceAction
        referenceReward algorithm referenceAlgorithm feedbackEnvironment
        (conditionalHistoryAlgorithmDensitySource_of_split
          mu env action reward referenceMu referenceEnv referenceAction
            referenceReward algorithm referenceAlgorithm feedbackEnvironment
            source)
        n bestAction hbestAction

end Thompson
end BanditRLProof
