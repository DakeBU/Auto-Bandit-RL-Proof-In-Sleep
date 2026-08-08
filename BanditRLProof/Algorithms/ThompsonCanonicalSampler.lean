import BanditRLProof.Algorithms.Thompson
import Mathlib.Probability.Kernel.Composition.Lemmas

/-!
# Canonical one-step Thompson sampler

This module constructs the one-step joint law obtained by sampling an
environment/history pair from a Bayesian prior-likelihood model and then
sampling an action from the canonical posterior pushed through a measurable
best-action selector.  The resulting probability-matching theorem has no
separate pair-law or action-law premise.
-/

open MeasureTheory
open scoped ProbabilityTheory

universe u v w

namespace BanditRLProof
namespace Thompson

/-- The Thompson action kernel induced by Mathlib's canonical posterior. -/
noncomputable def canonicalActionKernel
    {History : Type u} {Env : Type v} {Action : Type w}
    [MeasurableSpace History]
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (likelihood : ProbabilityTheory.Kernel Env History)
    [ProbabilityTheory.IsMarkovKernel likelihood]
    (bestAction : Env -> Action) (_hbestAction : Measurable bestAction) :
    ProbabilityTheory.Kernel History Action :=
  (PosteriorKernel.canonicalPosterior prior likelihood).kernel.map bestAction

instance instCanonicalActionKernelIsMarkovKernel
    {History : Type u} {Env : Type v} {Action : Type w}
    [MeasurableSpace History]
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (likelihood : ProbabilityTheory.Kernel Env History)
    [ProbabilityTheory.IsMarkovKernel likelihood]
    (bestAction : Env -> Action) (hbestAction : Measurable bestAction) :
    ProbabilityTheory.IsMarkovKernel
      (canonicalActionKernel prior likelihood bestAction hbestAction) := by
  unfold canonicalActionKernel
  exact ProbabilityTheory.Kernel.IsMarkovKernel.map _ hbestAction

/-- Lift the history-indexed action kernel to environment/history pairs. -/
noncomputable def canonicalActionKernelOnPair
    {History : Type u} {Env : Type v} {Action : Type w}
    [MeasurableSpace History]
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (likelihood : ProbabilityTheory.Kernel Env History)
    [ProbabilityTheory.IsMarkovKernel likelihood]
    (bestAction : Env -> Action) (hbestAction : Measurable bestAction) :
    ProbabilityTheory.Kernel (Env × History) Action :=
  (canonicalActionKernel prior likelihood bestAction hbestAction).comap
    Prod.snd measurable_snd

instance instCanonicalActionKernelOnPairIsMarkovKernel
    {History : Type u} {Env : Type v} {Action : Type w}
    [MeasurableSpace History]
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (likelihood : ProbabilityTheory.Kernel Env History)
    [ProbabilityTheory.IsMarkovKernel likelihood]
    (bestAction : Env -> Action) (hbestAction : Measurable bestAction) :
    ProbabilityTheory.IsMarkovKernel
      (canonicalActionKernelOnPair prior likelihood bestAction hbestAction) := by
  unfold canonicalActionKernelOnPair
  infer_instance

/--
The canonical one-step Thompson law on `(Env × History) × Action`.

The first component is sampled from `prior ⊗ₘ likelihood`; the action is then
sampled from the canonical posterior mapped by `bestAction` at that history.
-/
noncomputable def canonicalSamplerMeasure
    {History : Type u} {Env : Type v} {Action : Type w}
    [MeasurableSpace History]
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (likelihood : ProbabilityTheory.Kernel Env History)
    [ProbabilityTheory.IsMarkovKernel likelihood]
    (bestAction : Env -> Action) (hbestAction : Measurable bestAction) :
    Measure ((Env × History) × Action) :=
  PosteriorKernel.canonicalJointMeasure prior likelihood ⊗ₘ
    canonicalActionKernelOnPair prior likelihood bestAction hbestAction

instance instCanonicalSamplerMeasureIsProbabilityMeasure
    {History : Type u} {Env : Type v} {Action : Type w}
    [MeasurableSpace History]
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (likelihood : ProbabilityTheory.Kernel Env History)
    [ProbabilityTheory.IsMarkovKernel likelihood]
    (bestAction : Env -> Action) (hbestAction : Measurable bestAction) :
    IsProbabilityMeasure
      (canonicalSamplerMeasure prior likelihood bestAction hbestAction) := by
  unfold canonicalSamplerMeasure
  infer_instance

/-- Environment coordinate of the canonical sampler source. -/
def canonicalSamplerEnv {Env History Action : Type*} :
    (Env × History) × Action -> Env :=
  fun sample => sample.1.1

/-- History coordinate of the canonical sampler source. -/
def canonicalSamplerHistory {Env History Action : Type*} :
    (Env × History) × Action -> History :=
  fun sample => sample.1.2

/-- Action coordinate of the canonical sampler source. -/
def canonicalSamplerAction {Env History Action : Type*} :
    (Env × History) × Action -> Action :=
  fun sample => sample.2

theorem canonicalSamplerEnv_measurable
    {Env History Action : Type*}
    [MeasurableSpace Env] [MeasurableSpace History] [MeasurableSpace Action] :
    Measurable (@canonicalSamplerEnv Env History Action) :=
  measurable_fst.comp measurable_fst

theorem canonicalSamplerHistory_measurable
    {Env History Action : Type*}
    [MeasurableSpace Env] [MeasurableSpace History] [MeasurableSpace Action] :
    Measurable (@canonicalSamplerHistory Env History Action) :=
  measurable_snd.comp measurable_fst

theorem canonicalSamplerAction_measurable
    {Env History Action : Type*}
    [MeasurableSpace Env] [MeasurableSpace History] [MeasurableSpace Action] :
    Measurable (@canonicalSamplerAction Env History Action) :=
  measurable_snd

/--
Projecting a composition product whose kernel depends only on the second base
coordinate gives the second-coordinate marginal composed with that kernel.
-/
theorem map_compProd_comap_snd
    {Env History Action : Type*}
    [MeasurableSpace Env] [MeasurableSpace History] [MeasurableSpace Action]
    (mu : Measure (Env × History)) [IsFiniteMeasure mu]
    (actionKernel : ProbabilityTheory.Kernel History Action)
    [ProbabilityTheory.IsMarkovKernel actionKernel] :
    (mu ⊗ₘ actionKernel.comap Prod.snd measurable_snd).map
        (fun sample => (sample.1.2, sample.2)) =
      mu.map Prod.snd ⊗ₘ actionKernel := by
  apply Measure.ext_prod
  intro historyEvent actionEvent hhistoryEvent hactionEvent
  have hmap : Measurable
      (fun sample : (Env × History) × Action => (sample.1.2, sample.2)) :=
    (measurable_snd.comp measurable_fst).prodMk measurable_snd
  rw [Measure.map_apply hmap (hhistoryEvent.prod hactionEvent)]
  have hpreimage :
      (fun sample : (Env × History) × Action => (sample.1.2, sample.2)) ⁻¹'
          (historyEvent ×ˢ actionEvent) =
        (Set.univ ×ˢ historyEvent) ×ˢ actionEvent := by
    ext sample
    simp
  rw [hpreimage,
    Measure.compProd_apply_prod (MeasurableSet.univ.prod hhistoryEvent) hactionEvent,
    Measure.compProd_apply_prod hhistoryEvent hactionEvent]
  simp_rw [ProbabilityTheory.Kernel.comap_apply]
  rw [MeasureTheory.setLIntegral_map hhistoryEvent
    (actionKernel.measurable_coe hactionEvent) measurable_snd]
  have hsndPreimage :
      Prod.snd ⁻¹' historyEvent = (Set.univ ×ˢ historyEvent : Set (Env × History)) := by
    ext sample
    simp
  rw [hsndPreimage]

/-- The canonical sampler preserves the prescribed environment/history law. -/
theorem canonicalSampler_env_history_map_eq
    {History : Type u} {Env : Type v} {Action : Type w}
    [MeasurableSpace History]
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (likelihood : ProbabilityTheory.Kernel Env History)
    [ProbabilityTheory.IsMarkovKernel likelihood]
    (bestAction : Env -> Action) (hbestAction : Measurable bestAction) :
    (canonicalSamplerMeasure prior likelihood bestAction hbestAction).map
        (fun sample =>
          (canonicalSamplerEnv sample, canonicalSamplerHistory sample)) =
      PosteriorKernel.canonicalJointMeasure prior likelihood := by
  change
    (canonicalSamplerMeasure prior likelihood bestAction hbestAction).fst =
      PosteriorKernel.canonicalJointMeasure prior likelihood
  rw [canonicalSamplerMeasure, Measure.fst_compProd]

/-- The history/action marginal is generated by the canonical action kernel. -/
theorem canonicalSampler_history_action_map_eq
    {History : Type u} {Env : Type v} {Action : Type w}
    [MeasurableSpace History]
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (likelihood : ProbabilityTheory.Kernel Env History)
    [ProbabilityTheory.IsMarkovKernel likelihood]
    (bestAction : Env -> Action) (hbestAction : Measurable bestAction) :
    (canonicalSamplerMeasure prior likelihood bestAction hbestAction).map
        (fun sample =>
          (canonicalSamplerHistory sample, canonicalSamplerAction sample)) =
      (canonicalSamplerMeasure prior likelihood bestAction hbestAction).map
          canonicalSamplerHistory ⊗ₘ
        canonicalActionKernel prior likelihood bestAction hbestAction := by
  have hhistoryLaw :
      (canonicalSamplerMeasure prior likelihood bestAction hbestAction).map
          canonicalSamplerHistory =
        (PosteriorKernel.canonicalJointMeasure prior likelihood).map Prod.snd := by
    calc
      (canonicalSamplerMeasure prior likelihood bestAction hbestAction).map
          canonicalSamplerHistory =
          ((canonicalSamplerMeasure prior likelihood bestAction hbestAction).map
            Prod.fst).map Prod.snd := by
              rw [Measure.map_map measurable_snd measurable_fst]
              rfl
      _ = (PosteriorKernel.canonicalJointMeasure prior likelihood).map Prod.snd := by
        rw [show
          (canonicalSamplerMeasure prior likelihood bestAction hbestAction).map
              Prod.fst =
            PosteriorKernel.canonicalJointMeasure prior likelihood by
          simpa only [canonicalSamplerEnv, canonicalSamplerHistory] using
            canonicalSampler_env_history_map_eq
              prior likelihood bestAction hbestAction]
  have htransport := map_compProd_comap_snd
    (PosteriorKernel.canonicalJointMeasure prior likelihood)
    (canonicalActionKernel prior likelihood bestAction hbestAction)
  rw [hhistoryLaw]
  simpa only [canonicalSamplerMeasure, canonicalActionKernelOnPair,
    canonicalSamplerHistory, canonicalSamplerAction] using htransport

/-- The constructed sampler has the intended next-action conditional law. -/
theorem canonicalSampler_condDistrib_action_ae_eq_actionKernel
    {History : Type u} {Env : Type v} {Action : Type w}
    [MeasurableSpace History]
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [StandardBorelSpace Action] [Nonempty Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (likelihood : ProbabilityTheory.Kernel Env History)
    [ProbabilityTheory.IsMarkovKernel likelihood]
    (bestAction : Env -> Action) (hbestAction : Measurable bestAction) :
    ProbabilityTheory.condDistrib canonicalSamplerAction canonicalSamplerHistory
        (canonicalSamplerMeasure prior likelihood bestAction hbestAction) =ᵐ[
      (canonicalSamplerMeasure prior likelihood bestAction hbestAction).map
        canonicalSamplerHistory]
      canonicalActionKernel prior likelihood bestAction hbestAction := by
  exact (ProbabilityTheory.condDistrib_ae_eq_iff_measure_eq_compProd
    (μ := canonicalSamplerMeasure prior likelihood bestAction hbestAction)
    canonicalSamplerHistory canonicalSamplerAction_measurable.aemeasurable
    (canonicalActionKernel prior likelihood bestAction hbestAction)).2
      (canonicalSampler_history_action_map_eq
        prior likelihood bestAction hbestAction)

/--
Premise-free one-step Thompson probability matching for the canonical sampler.

Both law premises of the generic theorem are discharged by the constructed
composition-product measure: its environment/history marginal is the canonical
Bayesian joint law, and its history/action marginal is generated by the mapped
canonical posterior.
-/
theorem canonicalSampler_condDistrib_action_ae_eq_bestAction
    {History : Type u} {Env : Type v} {Action : Type w}
    [MeasurableSpace History]
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [StandardBorelSpace Action] [Nonempty Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (likelihood : ProbabilityTheory.Kernel Env History)
    [ProbabilityTheory.IsMarkovKernel likelihood]
    (bestAction : Env -> Action) (hbestAction : Measurable bestAction) :
    ProbabilityTheory.condDistrib canonicalSamplerAction canonicalSamplerHistory
        (canonicalSamplerMeasure prior likelihood bestAction hbestAction) =ᵐ[
      (canonicalSamplerMeasure prior likelihood bestAction hbestAction).map
        canonicalSamplerHistory]
      ProbabilityTheory.condDistrib (bestAction ∘ canonicalSamplerEnv)
        canonicalSamplerHistory
        (canonicalSamplerMeasure prior likelihood bestAction hbestAction) := by
  exact condDistrib_action_ae_eq_bestAction_of_bayesianPairMap
    (canonicalSamplerMeasure prior likelihood bestAction hbestAction)
    canonicalSamplerEnv canonicalSamplerHistory canonicalSamplerAction
    prior likelihood bestAction hbestAction
    canonicalSamplerEnv_measurable canonicalSamplerHistory_measurable
    canonicalSamplerAction_measurable
    (canonicalSampler_env_history_map_eq prior likelihood bestAction hbestAction)
    (canonicalSampler_condDistrib_action_ae_eq_actionKernel
      prior likelihood bestAction hbestAction)

end Thompson
end BanditRLProof
