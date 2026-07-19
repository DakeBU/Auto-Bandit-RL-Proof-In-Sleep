import BanditRLProof.Algorithms.ThompsonCanonicalSampler
import BanditRLProof.HistoryFiltration

/-!
# Thompson sampling from a reference posterior policy

LML defines Thompson sampling from the posterior under a fixed reference
algorithm and then transports that posterior to the actual process by an
algorithm-density theorem.  This module isolates the corresponding local
Mathlib boundary.

The next action is genuinely sampled by a composition-product measure, so no
action conditional-law premise remains.  The only process-level premise in the
final theorem is posterior invariance between the reference and actual history
laws.
-/

open MeasureTheory
open scoped ProbabilityTheory

universe u v w x y

namespace BanditRLProof
namespace Thompson

/-- A reference source's environment posterior given its history. -/
noncomputable def referencePosterior
    {OmegaRef : Type u} {History : Type v} {Env : Type w}
    [MeasurableSpace OmegaRef] [MeasurableSpace History]
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    (referenceMu : Measure OmegaRef) [IsFiniteMeasure referenceMu]
    (referenceEnv : OmegaRef -> Env)
    (referenceHistory : OmegaRef -> History)
    (_hreferenceEnv : Measurable referenceEnv)
    (_hreferenceHistory : Measurable referenceHistory) :
    PosteriorKernel.MarkovPosteriorKernel History Env :=
  PosteriorKernel.ofKernel
    (ProbabilityTheory.condDistrib referenceEnv referenceHistory referenceMu)
    inferInstance

@[simp]
theorem referencePosterior_kernel
    {OmegaRef : Type u} {History : Type v} {Env : Type w}
    [MeasurableSpace OmegaRef] [MeasurableSpace History]
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    (referenceMu : Measure OmegaRef) [IsFiniteMeasure referenceMu]
    (referenceEnv : OmegaRef -> Env)
    (referenceHistory : OmegaRef -> History)
    (hreferenceEnv : Measurable referenceEnv)
    (hreferenceHistory : Measurable referenceHistory) :
    (referencePosterior referenceMu referenceEnv referenceHistory
      hreferenceEnv hreferenceHistory).kernel =
      ProbabilityTheory.condDistrib referenceEnv referenceHistory referenceMu :=
  rfl

/-- The Thompson action policy obtained by mapping a reference posterior. -/
noncomputable def referenceActionKernel
    {OmegaRef : Type u} {History : Type v} {Env : Type w} {Action : Type x}
    [MeasurableSpace OmegaRef] [MeasurableSpace History]
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action]
    (referenceMu : Measure OmegaRef) [IsFiniteMeasure referenceMu]
    (referenceEnv : OmegaRef -> Env)
    (referenceHistory : OmegaRef -> History)
    (hreferenceEnv : Measurable referenceEnv)
    (hreferenceHistory : Measurable referenceHistory)
    (bestAction : Env -> Action) (_hbestAction : Measurable bestAction) :
    ProbabilityTheory.Kernel History Action :=
  (referencePosterior referenceMu referenceEnv referenceHistory
    hreferenceEnv hreferenceHistory).kernel.map bestAction

instance instReferenceActionKernelIsMarkovKernel
    {OmegaRef : Type u} {History : Type v} {Env : Type w} {Action : Type x}
    [MeasurableSpace OmegaRef] [MeasurableSpace History]
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action]
    (referenceMu : Measure OmegaRef) [IsFiniteMeasure referenceMu]
    (referenceEnv : OmegaRef -> Env)
    (referenceHistory : OmegaRef -> History)
    (hreferenceEnv : Measurable referenceEnv)
    (hreferenceHistory : Measurable referenceHistory)
    (bestAction : Env -> Action) (hbestAction : Measurable bestAction) :
    ProbabilityTheory.IsMarkovKernel
      (referenceActionKernel referenceMu referenceEnv referenceHistory
        hreferenceEnv hreferenceHistory bestAction hbestAction) := by
  unfold referenceActionKernel
  exact ProbabilityTheory.Kernel.IsMarkovKernel.map _ hbestAction

/-- Extend a base process by sampling an action from a history-indexed policy. -/
noncomputable def policySamplerMeasure
    {Omega : Type u} {History : Type v} {Action : Type w}
    [MeasurableSpace Omega] [MeasurableSpace History] [MeasurableSpace Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (history : Omega -> History) (hhistory : Measurable history)
    (policy : ProbabilityTheory.Kernel History Action)
    [ProbabilityTheory.IsMarkovKernel policy] :
    Measure (Omega × Action) :=
  mu ⊗ₘ policy.comap history hhistory

instance instPolicySamplerMeasureIsFiniteMeasure
    {Omega : Type u} {History : Type v} {Action : Type w}
    [MeasurableSpace Omega] [MeasurableSpace History] [MeasurableSpace Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (history : Omega -> History) (hhistory : Measurable history)
    (policy : ProbabilityTheory.Kernel History Action)
    [ProbabilityTheory.IsMarkovKernel policy] :
    IsFiniteMeasure (policySamplerMeasure mu history hhistory policy) := by
  unfold policySamplerMeasure
  infer_instance

/-- Base environment coordinate after adjoining a sampled action. -/
def policySamplerEnv
    {Omega Env Action : Type*} (env : Omega -> Env) :
    Omega × Action -> Env :=
  fun sample => env sample.1

/-- Base history coordinate after adjoining a sampled action. -/
def policySamplerHistory
    {Omega History Action : Type*} (history : Omega -> History) :
    Omega × Action -> History :=
  fun sample => history sample.1

/-- Newly sampled action coordinate. -/
def policySamplerAction {Omega Action : Type*} : Omega × Action -> Action :=
  Prod.snd

theorem policySamplerEnv_measurable
    {Omega Env Action : Type*}
    [MeasurableSpace Omega] [MeasurableSpace Env] [MeasurableSpace Action]
    (env : Omega -> Env) (henv : Measurable env) :
    Measurable (@policySamplerEnv Omega Env Action env) :=
  henv.comp measurable_fst

theorem policySamplerHistory_measurable
    {Omega History Action : Type*}
    [MeasurableSpace Omega] [MeasurableSpace History] [MeasurableSpace Action]
    (history : Omega -> History) (hhistory : Measurable history) :
    Measurable (@policySamplerHistory Omega History Action history) :=
  hhistory.comp measurable_fst

theorem policySamplerAction_measurable
    {Omega Action : Type*}
    [MeasurableSpace Omega] [MeasurableSpace Action] :
    Measurable (@policySamplerAction Omega Action) :=
  measurable_snd

/--
History/action projection of a policy sampler.

This is the arbitrary-history-map version of `map_compProd_comap_snd` and is a
generic Mathlib candidate.
-/
theorem map_compProd_comap_history
    {Omega History Action : Type*}
    [MeasurableSpace Omega] [MeasurableSpace History] [MeasurableSpace Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (history : Omega -> History) (hhistory : Measurable history)
    (policy : ProbabilityTheory.Kernel History Action)
    [ProbabilityTheory.IsMarkovKernel policy] :
    (mu ⊗ₘ policy.comap history hhistory).map
        (fun sample => (history sample.1, sample.2)) =
      mu.map history ⊗ₘ policy := by
  apply Measure.ext_prod
  intro historyEvent actionEvent hhistoryEvent hactionEvent
  have hmap : Measurable
      (fun sample : Omega × Action => (history sample.1, sample.2)) :=
    (hhistory.comp measurable_fst).prodMk measurable_snd
  rw [Measure.map_apply hmap (hhistoryEvent.prod hactionEvent)]
  have hpreimage :
      (fun sample : Omega × Action => (history sample.1, sample.2)) ⁻¹'
          (historyEvent ×ˢ actionEvent) =
        (history ⁻¹' historyEvent) ×ˢ actionEvent := by
    ext sample
    simp
  rw [hpreimage,
    Measure.compProd_apply_prod (hhistory hhistoryEvent) hactionEvent,
    Measure.compProd_apply_prod hhistoryEvent hactionEvent]
  simp_rw [ProbabilityTheory.Kernel.comap_apply]
  rw [MeasureTheory.setLIntegral_map hhistoryEvent
    (policy.measurable_coe hactionEvent) hhistory]

/-- Adjoining a Markov-policy sample preserves every measurable base map. -/
theorem policySampler_base_map_eq
    {Omega History Action Target : Type*}
    [MeasurableSpace Omega] [MeasurableSpace History]
    [MeasurableSpace Action] [MeasurableSpace Target]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (history : Omega -> History) (hhistory : Measurable history)
    (policy : ProbabilityTheory.Kernel History Action)
    [ProbabilityTheory.IsMarkovKernel policy]
    (f : Omega -> Target) (hf : Measurable f) :
    (policySamplerMeasure mu history hhistory policy).map
        (fun sample => f sample.1) =
      mu.map f := by
  calc
    (policySamplerMeasure mu history hhistory policy).map
        (fun sample => f sample.1) =
        ((policySamplerMeasure mu history hhistory policy).map Prod.fst).map f := by
          rw [Measure.map_map hf measurable_fst]
          rfl
    _ = mu.map f := by
      congr 1
      change (mu ⊗ₘ policy.comap history hhistory).fst = mu
      rw [Measure.fst_compProd]

/-- The constructed sampler's history/action joint law is `historyLaw ⊗ policy`. -/
theorem policySampler_history_action_map_eq
    {Omega History Action : Type*}
    [MeasurableSpace Omega] [MeasurableSpace History] [MeasurableSpace Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (history : Omega -> History) (hhistory : Measurable history)
    (policy : ProbabilityTheory.Kernel History Action)
    [ProbabilityTheory.IsMarkovKernel policy] :
    (policySamplerMeasure mu history hhistory policy).map
        (fun sample =>
          (policySamplerHistory history sample, policySamplerAction sample)) =
      (policySamplerMeasure mu history hhistory policy).map
          (policySamplerHistory history) ⊗ₘ policy := by
  have hhistoryLaw :
      (policySamplerMeasure mu history hhistory policy).map
          (policySamplerHistory history) = mu.map history := by
    simpa only [policySamplerHistory] using
      policySampler_base_map_eq mu history hhistory policy history hhistory
  rw [hhistoryLaw]
  simpa only [policySamplerMeasure, policySamplerHistory, policySamplerAction] using
    map_compProd_comap_history mu history hhistory policy

/-- The sampled action has the policy as its conditional law given history. -/
theorem policySampler_condDistrib_action_ae_eq_policy
    {Omega History Action : Type*}
    [MeasurableSpace Omega] [MeasurableSpace History]
    [MeasurableSpace Action] [StandardBorelSpace Action] [Nonempty Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (history : Omega -> History) (hhistory : Measurable history)
    (policy : ProbabilityTheory.Kernel History Action)
    [ProbabilityTheory.IsMarkovKernel policy] :
    ProbabilityTheory.condDistrib policySamplerAction
        (policySamplerHistory history)
        (policySamplerMeasure mu history hhistory policy) =ᵐ[
      (policySamplerMeasure mu history hhistory policy).map
        (policySamplerHistory history)] policy := by
  exact (ProbabilityTheory.condDistrib_ae_eq_iff_measure_eq_compProd
    (μ := policySamplerMeasure mu history hhistory policy)
    (policySamplerHistory history) policySamplerAction_measurable.aemeasurable
    policy).2 (policySampler_history_action_map_eq
      mu history hhistory policy)

/--
Adjoining a history-dependent action sample preserves an environment posterior.
-/
theorem policySampler_condDistrib_env_ae_eq_of_base
    {Omega History Env Action : Type*}
    [MeasurableSpace Omega] [MeasurableSpace History]
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (env : Omega -> Env) (history : Omega -> History)
    (henv : Measurable env) (hhistory : Measurable history)
    (policy : ProbabilityTheory.Kernel History Action)
    [ProbabilityTheory.IsMarkovKernel policy]
    (posterior : ProbabilityTheory.Kernel History Env)
    [ProbabilityTheory.IsMarkovKernel posterior]
    (hbase :
      ProbabilityTheory.condDistrib env history mu =ᵐ[mu.map history]
        posterior) :
    ProbabilityTheory.condDistrib (policySamplerEnv env)
        (policySamplerHistory history)
        (policySamplerMeasure mu history hhistory policy) =ᵐ[
      (policySamplerMeasure mu history hhistory policy).map
        (policySamplerHistory history)] posterior := by
  have hbaseJoint :
      mu.map (fun omega => (history omega, env omega)) =
        mu.map history ⊗ₘ posterior :=
    (ProbabilityTheory.condDistrib_ae_eq_iff_measure_eq_compProd
      (μ := mu) history henv.aemeasurable posterior).1 hbase
  have hhistoryLaw :
      (policySamplerMeasure mu history hhistory policy).map
          (policySamplerHistory history) = mu.map history := by
    simpa only [policySamplerHistory] using
      policySampler_base_map_eq mu history hhistory policy history hhistory
  have hjointLaw :
      (policySamplerMeasure mu history hhistory policy).map
          (fun sample =>
            (policySamplerHistory history sample, policySamplerEnv env sample)) =
        (policySamplerMeasure mu history hhistory policy).map
            (policySamplerHistory history) ⊗ₘ posterior := by
    calc
      _ = mu.map (fun omega => (history omega, env omega)) := by
        simpa only [policySamplerHistory, policySamplerEnv] using
          policySampler_base_map_eq mu history hhistory policy
            (fun omega => (history omega, env omega)) (hhistory.prodMk henv)
      _ = mu.map history ⊗ₘ posterior := hbaseJoint
      _ = _ := by rw [hhistoryLaw]
  exact (ProbabilityTheory.condDistrib_ae_eq_iff_measure_eq_compProd
    (μ := policySamplerMeasure mu history hhistory policy)
    (policySamplerHistory history)
    (policySamplerEnv_measurable env henv).aemeasurable posterior).2 hjointLaw

/--
Reference-posterior Thompson probability matching with a constructed sampler.

The action law is generated by `policySamplerMeasure`.  The sole law transport
premise is that the reference posterior agrees with the actual environment
posterior at the actual history law; this is the conclusion supplied by LML's
algorithm-density route.
-/
theorem referencePolicySampler_condDistrib_action_ae_eq_bestAction_of_posterior_invariance
    {Omega : Type u} {OmegaRef : Type v}
    {History : Type w} {Env : Type x} {Action : Type y}
    [MeasurableSpace Omega] [MeasurableSpace OmegaRef]
    [MeasurableSpace History]
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [StandardBorelSpace Action] [Nonempty Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (env : Omega -> Env) (history : Omega -> History)
    (henv : Measurable env) (hhistory : Measurable history)
    (referenceMu : Measure OmegaRef) [IsFiniteMeasure referenceMu]
    (referenceEnv : OmegaRef -> Env)
    (referenceHistory : OmegaRef -> History)
    (hreferenceEnv : Measurable referenceEnv)
    (hreferenceHistory : Measurable referenceHistory)
    (bestAction : Env -> Action) (hbestAction : Measurable bestAction)
    (hposteriorInvariance :
      (referencePosterior referenceMu referenceEnv referenceHistory
        hreferenceEnv hreferenceHistory).kernel =ᵐ[mu.map history]
        ProbabilityTheory.condDistrib env history mu) :
    let policy := referenceActionKernel referenceMu referenceEnv referenceHistory
      hreferenceEnv hreferenceHistory bestAction hbestAction
    let sampler := policySamplerMeasure mu history hhistory policy
    ProbabilityTheory.condDistrib policySamplerAction
        (policySamplerHistory history) sampler =ᵐ[
      sampler.map (policySamplerHistory history)]
      ProbabilityTheory.condDistrib (bestAction ∘ policySamplerEnv env)
        (policySamplerHistory history) sampler := by
  dsimp only
  let posterior := referencePosterior referenceMu referenceEnv referenceHistory
    hreferenceEnv hreferenceHistory
  let policy := referenceActionKernel referenceMu referenceEnv referenceHistory
    hreferenceEnv hreferenceHistory bestAction hbestAction
  let sampler := policySamplerMeasure mu history hhistory policy
  have haction :
      ProbabilityTheory.condDistrib policySamplerAction
          (policySamplerHistory history) sampler =ᵐ[
        sampler.map (policySamplerHistory history)]
        posterior.kernel.map bestAction := by
    simpa only [sampler, policy, posterior, referenceActionKernel] using
      policySampler_condDistrib_action_ae_eq_policy
        mu history hhistory policy
  have hposterior :
      posterior.kernel =ᵐ[sampler.map (policySamplerHistory history)]
        ProbabilityTheory.condDistrib (policySamplerEnv env)
          (policySamplerHistory history) sampler := by
    have hbase :
        ProbabilityTheory.condDistrib env history mu =ᵐ[mu.map history]
          posterior.kernel := by
      simpa only [posterior] using hposteriorInvariance.symm
    exact (policySampler_condDistrib_env_ae_eq_of_base
      mu env history henv hhistory policy posterior.kernel hbase).symm
  exact condDistrib_action_ae_eq_bestAction_of_posteriorMap
    sampler (policySamplerEnv env) (policySamplerHistory history)
    policySamplerAction posterior bestAction hbestAction
    (policySamplerEnv_measurable env henv)
    (policySamplerHistory_measurable history hhistory)
    policySamplerAction_measurable haction hposterior

/--
Finite action/reward-prefix specialization of the reference-policy theorem.

This is the per-time interface used by the recursive bandit route.  The
remaining premise is exactly posterior invariance between the reference and
actual finite-pair history laws.
-/
theorem finitePairReferencePolicySampler_condDistrib_action_ae_eq_bestAction_of_posterior_invariance
    {Omega : Type u} {OmegaRef : Type v}
    {Env : Type w} {Action : Type x} {Reward : Type y}
    [MeasurableSpace Omega] [MeasurableSpace OmegaRef]
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [StandardBorelSpace Action] [Nonempty Action]
    [MeasurableSpace Reward]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (env : Omega -> Env)
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Reward)
    (henv : Measurable env)
    (haction : forall t : Nat, Measurable (fun omega => action omega t))
    (hreward : forall t : Nat, Measurable (fun omega => reward omega t))
    (referenceMu : Measure OmegaRef) [IsFiniteMeasure referenceMu]
    (referenceEnv : OmegaRef -> Env)
    (referenceAction : OmegaRef -> ActionTrace Action)
    (referenceReward : OmegaRef -> RewardTrace Reward)
    (hreferenceEnv : Measurable referenceEnv)
    (hreferenceAction : forall t : Nat,
      Measurable (fun omega => referenceAction omega t))
    (hreferenceReward : forall t : Nat,
      Measurable (fun omega => referenceReward omega t))
    (n : Nat)
    (bestAction : Env -> Action) (hbestAction : Measurable bestAction)
    (hposteriorInvariance :
      ProbabilityTheory.condDistrib referenceEnv
          (fun omega => History.finitePairHistoryOfTrace
            (referenceAction omega) (referenceReward omega) n)
          referenceMu =ᵐ[
        mu.map (fun omega => History.finitePairHistoryOfTrace
          (action omega) (reward omega) n)]
        ProbabilityTheory.condDistrib env
          (fun omega => History.finitePairHistoryOfTrace
            (action omega) (reward omega) n) mu) :
    let actualHistory := fun omega => History.finitePairHistoryOfTrace
      (action omega) (reward omega) n
    let referenceHistory := fun omega => History.finitePairHistoryOfTrace
      (referenceAction omega) (referenceReward omega) n
    let policy := referenceActionKernel referenceMu referenceEnv referenceHistory
      hreferenceEnv
      (History.measurable_finitePairHistoryOfTrace
        referenceAction referenceReward hreferenceAction hreferenceReward n)
      bestAction hbestAction
    let sampler := policySamplerMeasure mu actualHistory
      (History.measurable_finitePairHistoryOfTrace
        action reward haction hreward n) policy
    ProbabilityTheory.condDistrib policySamplerAction
        (policySamplerHistory actualHistory) sampler =ᵐ[
      sampler.map (policySamplerHistory actualHistory)]
      ProbabilityTheory.condDistrib (bestAction ∘ policySamplerEnv env)
        (policySamplerHistory actualHistory) sampler := by
  dsimp only
  let actualHistory := fun omega => History.finitePairHistoryOfTrace
    (action omega) (reward omega) n
  let referenceHistory := fun omega => History.finitePairHistoryOfTrace
    (referenceAction omega) (referenceReward omega) n
  have hactualHistory : Measurable actualHistory :=
    History.measurable_finitePairHistoryOfTrace
      action reward haction hreward n
  have hreferenceHistory : Measurable referenceHistory :=
    History.measurable_finitePairHistoryOfTrace
      referenceAction referenceReward hreferenceAction hreferenceReward n
  have hinvariance :
      (referencePosterior referenceMu referenceEnv referenceHistory
        hreferenceEnv hreferenceHistory).kernel =ᵐ[mu.map actualHistory]
        ProbabilityTheory.condDistrib env actualHistory mu := by
    simpa only [referencePosterior_kernel, actualHistory, referenceHistory] using
      hposteriorInvariance
  have hresult :=
    referencePolicySampler_condDistrib_action_ae_eq_bestAction_of_posterior_invariance
      mu env actualHistory henv hactualHistory
      referenceMu referenceEnv referenceHistory hreferenceEnv hreferenceHistory
      bestAction hbestAction hinvariance
  simpa only [actualHistory, referenceHistory] using hresult

end Thompson
end BanditRLProof
