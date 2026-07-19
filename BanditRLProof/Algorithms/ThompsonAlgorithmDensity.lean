import BanditRLProof.Algorithms.ThompsonReferencePolicy
import Mathlib.Probability.Kernel.CompProdEqIff

/-!
# Thompson posterior invariance from algorithm-density laws

This module isolates the measure-theoretic core of LML's algorithm-density
posterior transport.  If the actual history law and the actual
history/environment joint law are obtained from their reference counterparts
by the same density depending only on history, then the reference and actual
environment posteriors agree at the actual history law.
-/

open MeasureTheory
open scoped ENNReal ProbabilityTheory

universe u v w x y

namespace BanditRLProof
namespace Thompson

/--
Weighting the base measure of a composition product is the same as weighting
the product by the density pulled back through the first projection.
-/
theorem compProd_withDensity_left
    {History : Type u} {Env : Type v}
    [MeasurableSpace History] [MeasurableSpace Env]
    (historyLaw : Measure History)
    [SFinite historyLaw]
    (posterior : ProbabilityTheory.Kernel History Env)
    [ProbabilityTheory.IsSFiniteKernel posterior]
    (density : History -> ENNReal) (hdensity : Measurable density) :
    historyLaw.withDensity density ⊗ₘ posterior =
      (historyLaw ⊗ₘ posterior).withDensity (density ∘ Prod.fst) := by
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  calc
    ∫⁻ pair, f pair ∂(historyLaw.withDensity density ⊗ₘ posterior) =
        ∫⁻ history, ∫⁻ environment, f (history, environment) ∂posterior history
          ∂(historyLaw.withDensity density) :=
      Measure.lintegral_compProd hf
    _ = ∫⁻ history, density history *
          ∫⁻ environment, f (history, environment) ∂posterior history
          ∂historyLaw :=
      MeasureTheory.lintegral_withDensity_eq_lintegral_mul _ hdensity
        hf.lintegral_kernel_prod_right'
    _ = ∫⁻ history, ∫⁻ environment,
          density history * f (history, environment) ∂posterior history
          ∂historyLaw := by
      apply lintegral_congr
      intro history
      exact (MeasureTheory.lintegral_const_mul _ (by fun_prop)).symm
    _ = ∫⁻ pair, (density ∘ Prod.fst) pair * f pair
          ∂(historyLaw ⊗ₘ posterior) :=
      (Measure.lintegral_compProd ((hdensity.comp measurable_fst).mul hf)).symm
    _ = ∫⁻ pair, f pair
          ∂((historyLaw ⊗ₘ posterior).withDensity
            (density ∘ Prod.fst)) :=
      (MeasureTheory.lintegral_withDensity_eq_lintegral_mul _
        (hdensity.comp measurable_fst) hf).symm

/--
Composing a kernel weighted by a density independent of its input is the same
as weighting the composed output measure.
-/
theorem comp_withDensity_history
    {Env : Type u} {History : Type v}
    [MeasurableSpace Env] [MeasurableSpace History]
    (envLaw : Measure Env)
    (historyKernel : ProbabilityTheory.Kernel Env History)
    [ProbabilityTheory.IsSFiniteKernel historyKernel]
    (density : History -> ENNReal) (hdensity : Measurable density) :
    (historyKernel.withDensity (fun _ history => density history)) ∘ₘ envLaw =
      (historyKernel ∘ₘ envLaw).withDensity density := by
  ext historyEvent hhistoryEvent
  rw [Measure.bind_apply hhistoryEvent (ProbabilityTheory.Kernel.aemeasurable _)]
  simp_rw [ProbabilityTheory.Kernel.withDensity_apply' historyKernel
    (show Measurable
        (Function.uncurry (fun _ : Env => fun history => density history)) from
      hdensity.comp measurable_snd)]
  rw [MeasureTheory.withDensity_apply density hhistoryEvent]
  rw [← MeasureTheory.lintegral_indicator hhistoryEvent]
  rw [Measure.lintegral_bind historyKernel.aemeasurable
    ((hdensity.indicator hhistoryEvent).aemeasurable)]
  congr 1
  funext environment
  rw [MeasureTheory.lintegral_indicator hhistoryEvent]

/--
Swapping a joint law weighted by its second coordinate moves the density to
the first coordinate of the swapped law.
-/
theorem map_swap_withDensity_snd
    {Env : Type u} {History : Type v}
    [MeasurableSpace Env] [MeasurableSpace History]
    (joint : Measure (Env × History))
    (density : History -> ENNReal) (hdensity : Measurable density) :
    (joint.withDensity (density ∘ Prod.snd)).map Prod.swap =
      (joint.map Prod.swap).withDensity (density ∘ Prod.fst) := by
  ext event hevent
  rw [Measure.map_apply measurable_swap hevent]
  rw [MeasureTheory.withDensity_apply _ (measurable_swap hevent)]
  rw [MeasureTheory.withDensity_apply _ hevent]
  rw [MeasureTheory.setLIntegral_map hevent
    (hdensity.comp measurable_fst) measurable_swap]
  rfl

/--
Composition products transport an a.e. output-only kernel density directly,
without requiring an `IsSFiniteKernel` instance for the weighted kernel.
-/
theorem compProd_eq_compProd_withDensity_snd_of_ae_eq
    {Env : Type u} {History : Type v}
    [MeasurableSpace Env] [MeasurableSpace History]
    (envLaw : Measure Env) [SFinite envLaw]
    (actualHistoryKernel referenceHistoryKernel :
      ProbabilityTheory.Kernel Env History)
    [ProbabilityTheory.IsSFiniteKernel actualHistoryKernel]
    [ProbabilityTheory.IsSFiniteKernel referenceHistoryKernel]
    (density : History -> ENNReal) (hdensity : Measurable density)
    (hkernel : actualHistoryKernel =ᵐ[envLaw]
      referenceHistoryKernel.withDensity
        (fun _ history => density history)) :
    envLaw ⊗ₘ actualHistoryKernel =
      (envLaw ⊗ₘ referenceHistoryKernel).withDensity
        (density ∘ Prod.snd) := by
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  calc
    ∫⁻ pair, f pair ∂(envLaw ⊗ₘ actualHistoryKernel) =
        ∫⁻ environment, ∫⁻ history, f (environment, history)
          ∂actualHistoryKernel environment ∂envLaw :=
      Measure.lintegral_compProd hf
    _ = ∫⁻ environment, ∫⁻ history, f (environment, history)
          ∂(referenceHistoryKernel environment).withDensity density
          ∂envLaw := by
      apply lintegral_congr_ae
      filter_upwards [hkernel] with environment h_environment
      rw [h_environment, ProbabilityTheory.Kernel.withDensity_apply _
        (show Measurable
            (Function.uncurry
              (fun _ : Env => fun history => density history)) from
          hdensity.comp measurable_snd)]
    _ = ∫⁻ environment, ∫⁻ history,
          density history * f (environment, history)
          ∂referenceHistoryKernel environment ∂envLaw := by
      apply lintegral_congr
      intro environment
      exact MeasureTheory.lintegral_withDensity_eq_lintegral_mul _ hdensity
        (hf.comp (measurable_const.prodMk measurable_id))
    _ = ∫⁻ pair, (density ∘ Prod.snd) pair * f pair
          ∂(envLaw ⊗ₘ referenceHistoryKernel) :=
      (Measure.lintegral_compProd ((hdensity.comp measurable_snd).mul hf)).symm
    _ = ∫⁻ pair, f pair
          ∂((envLaw ⊗ₘ referenceHistoryKernel).withDensity
            (density ∘ Prod.snd)) :=
      (MeasureTheory.lintegral_withDensity_eq_lintegral_mul _
        (hdensity.comp measurable_snd) hf).symm

/--
The exact law interface produced by an algorithm-density/change-of-algorithm
argument.  Both the history marginal and the history/environment joint law are
weighted by the same measurable density depending only on history.
-/
structure AlgorithmDensityPosteriorSource
    {Omega : Type u} {OmegaRef : Type v}
    {History : Type w} {Env : Type x}
    [MeasurableSpace Omega] [MeasurableSpace OmegaRef]
    [MeasurableSpace History] [MeasurableSpace Env]
    (mu : Measure Omega)
    (env : Omega -> Env) (history : Omega -> History)
    (referenceMu : Measure OmegaRef)
    (referenceEnv : OmegaRef -> Env)
    (referenceHistory : OmegaRef -> History) where
  density : History -> ENNReal
  density_measurable : Measurable density
  history_map_eq_withDensity :
    mu.map history = (referenceMu.map referenceHistory).withDensity density
  historyEnv_map_eq_withDensity :
    mu.map (fun omega => (history omega, env omega)) =
      (referenceMu.map
        (fun omega => (referenceHistory omega, referenceEnv omega))).withDensity
          (density ∘ Prod.fst)

/--
Construct the two algorithm-density pushforward laws from a closer-to-process
interface: the actual and reference environment marginals agree, and the
actual conditional history kernel is the reference conditional history kernel
weighted by one history-only density.
-/
noncomputable def algorithmDensityPosteriorSource_of_condDistrib_history_withDensity
    {Omega : Type u} {OmegaRef : Type v}
    {History : Type w} {Env : Type x}
    [MeasurableSpace Omega] [MeasurableSpace OmegaRef]
    [MeasurableSpace History] [StandardBorelSpace History] [Nonempty History]
    [MeasurableSpace Env]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (env : Omega -> Env) (history : Omega -> History)
    (henv : Measurable env) (hhistory : Measurable history)
    (referenceMu : Measure OmegaRef) [IsFiniteMeasure referenceMu]
    (referenceEnv : OmegaRef -> Env)
    (referenceHistory : OmegaRef -> History)
    (hreferenceEnv : Measurable referenceEnv)
    (hreferenceHistory : Measurable referenceHistory)
    (density : History -> ENNReal) (hdensity : Measurable density)
    (henvLaw : mu.map env = referenceMu.map referenceEnv)
    (hcond :
      ProbabilityTheory.condDistrib history env mu =ᵐ[mu.map env]
        (ProbabilityTheory.condDistrib
          referenceHistory referenceEnv referenceMu).withDensity
            (fun _ history => density history)) :
    AlgorithmDensityPosteriorSource mu env history
      referenceMu referenceEnv referenceHistory := by
  let actualHistoryKernel := ProbabilityTheory.condDistrib history env mu
  let referenceHistoryKernel := ProbabilityTheory.condDistrib
    referenceHistory referenceEnv referenceMu
  let weightedReferenceHistoryKernel := referenceHistoryKernel.withDensity
    (fun _ history => density history)
  have hhistoryLaw :
      mu.map history =
        (referenceMu.map referenceHistory).withDensity density := by
    calc
      mu.map history = actualHistoryKernel ∘ₘ mu.map env := by
        simpa only [actualHistoryKernel] using
          (ProbabilityTheory.condDistrib_comp_map
            henv.aemeasurable hhistory.aemeasurable).symm
      _ = weightedReferenceHistoryKernel ∘ₘ mu.map env := by
        exact Measure.comp_congr hcond
      _ = weightedReferenceHistoryKernel ∘ₘ
          referenceMu.map referenceEnv := by rw [henvLaw]
      _ = (referenceHistoryKernel ∘ₘ
          referenceMu.map referenceEnv).withDensity density := by
        exact comp_withDensity_history
          (referenceMu.map referenceEnv) referenceHistoryKernel density hdensity
      _ = (referenceMu.map referenceHistory).withDensity density := by
        rw [ProbabilityTheory.condDistrib_comp_map
          hreferenceEnv.aemeasurable hreferenceHistory.aemeasurable]
  have hactualEnvHistory :
      mu.map (fun omega => (env omega, history omega)) =
        (referenceMu.map
          (fun omega => (referenceEnv omega, referenceHistory omega))).withDensity
            (density ∘ Prod.snd) := by
    calc
      mu.map (fun omega => (env omega, history omega)) =
          mu.map env ⊗ₘ actualHistoryKernel := by
        simpa only [actualHistoryKernel] using
          (ProbabilityTheory.compProd_map_condDistrib
            (μ := mu) (X := env) (Y := history) hhistory.aemeasurable).symm
      _ = (mu.map env ⊗ₘ referenceHistoryKernel).withDensity
          (density ∘ Prod.snd) :=
        compProd_eq_compProd_withDensity_snd_of_ae_eq
          (mu.map env) actualHistoryKernel referenceHistoryKernel
          density hdensity hcond
      _ = (referenceMu.map referenceEnv ⊗ₘ
          referenceHistoryKernel).withDensity (density ∘ Prod.snd) := by
        rw [henvLaw]
      _ = (referenceMu.map
          (fun omega => (referenceEnv omega, referenceHistory omega))).withDensity
            (density ∘ Prod.snd) := by
        rw [ProbabilityTheory.compProd_map_condDistrib
          (μ := referenceMu) (X := referenceEnv) (Y := referenceHistory)
          hreferenceHistory.aemeasurable]
  have hhistoryEnvLaw :
      mu.map (fun omega => (history omega, env omega)) =
        (referenceMu.map
          (fun omega => (referenceHistory omega, referenceEnv omega))).withDensity
            (density ∘ Prod.fst) := by
    calc
      mu.map (fun omega => (history omega, env omega)) =
          (mu.map (fun omega => (env omega, history omega))).map Prod.swap := by
        rw [Measure.map_map measurable_swap (henv.prodMk hhistory)]
        rfl
      _ = ((referenceMu.map
          (fun omega => (referenceEnv omega, referenceHistory omega))).withDensity
            (density ∘ Prod.snd)).map Prod.swap := by
        rw [hactualEnvHistory]
      _ = ((referenceMu.map
          (fun omega => (referenceEnv omega, referenceHistory omega))).map
            Prod.swap).withDensity (density ∘ Prod.fst) :=
        map_swap_withDensity_snd _ density hdensity
      _ = (referenceMu.map
          (fun omega => (referenceHistory omega, referenceEnv omega))).withDensity
            (density ∘ Prod.fst) := by
        rw [Measure.map_map measurable_swap
          (hreferenceEnv.prodMk hreferenceHistory)]
        rfl
  exact
    { density := density
      density_measurable := hdensity
      history_map_eq_withDensity := hhistoryLaw
      historyEnv_map_eq_withDensity := hhistoryEnvLaw }

/--
The reference environment posterior equals the actual posterior whenever the
two algorithm-density pushforward laws use the same history density.
-/
theorem referencePosterior_ae_eq_condDistrib_of_algorithmDensitySource
    {Omega : Type u} {OmegaRef : Type v}
    {History : Type w} {Env : Type x}
    [MeasurableSpace Omega] [MeasurableSpace OmegaRef]
    [MeasurableSpace History]
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (env : Omega -> Env) (history : Omega -> History)
    (henv : Measurable env)
    (referenceMu : Measure OmegaRef) [IsFiniteMeasure referenceMu]
    (referenceEnv : OmegaRef -> Env)
    (referenceHistory : OmegaRef -> History)
    (hreferenceEnv : Measurable referenceEnv)
    (hreferenceHistory : Measurable referenceHistory)
    (source : AlgorithmDensityPosteriorSource mu env history
      referenceMu referenceEnv referenceHistory) :
    (referencePosterior referenceMu referenceEnv referenceHistory
      hreferenceEnv hreferenceHistory).kernel =ᵐ[mu.map history]
      ProbabilityTheory.condDistrib env history mu := by
  let referenceHistoryLaw := referenceMu.map referenceHistory
  let posterior := ProbabilityTheory.condDistrib
    referenceEnv referenceHistory referenceMu
  have hreferenceJoint :
      referenceMu.map
          (fun omega => (referenceHistory omega, referenceEnv omega)) =
        referenceHistoryLaw ⊗ₘ posterior := by
    simpa only [referenceHistoryLaw, posterior] using
      (ProbabilityTheory.compProd_map_condDistrib
        (μ := referenceMu) (X := referenceHistory) (Y := referenceEnv)
        hreferenceEnv.aemeasurable).symm
  letI : IsFiniteMeasure
      (referenceHistoryLaw.withDensity source.density) :=
    ⟨by
      rw [← source.history_map_eq_withDensity]
      exact measure_lt_top (mu.map history) Set.univ⟩
  have hactualJoint :
      mu.map (fun omega => (history omega, env omega)) =
        mu.map history ⊗ₘ posterior := by
    calc
      _ = (referenceMu.map
            (fun omega => (referenceHistory omega, referenceEnv omega))).withDensity
            (source.density ∘ Prod.fst) :=
          source.historyEnv_map_eq_withDensity
      _ = (referenceHistoryLaw ⊗ₘ posterior).withDensity
            (source.density ∘ Prod.fst) := by rw [hreferenceJoint]
      _ = referenceHistoryLaw.withDensity source.density ⊗ₘ posterior :=
          (compProd_withDensity_left referenceHistoryLaw posterior
            source.density source.density_measurable).symm
      _ = mu.map history ⊗ₘ posterior := by
          rw [← source.history_map_eq_withDensity]
  have hactualPosterior :
      ProbabilityTheory.condDistrib env history mu =ᵐ[mu.map history]
        posterior :=
    ProbabilityTheory.condDistrib_ae_eq_of_measure_eq_compProd
      history henv.aemeasurable hactualJoint
  simpa only [referencePosterior_kernel, posterior] using hactualPosterior.symm

/--
Reference-policy Thompson probability matching with algorithm-density laws as
the only process-level input.
-/
theorem referencePolicySampler_condDistrib_action_ae_eq_bestAction_of_algorithmDensitySource
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
    (source : AlgorithmDensityPosteriorSource mu env history
      referenceMu referenceEnv referenceHistory) :
    let policy := referenceActionKernel referenceMu referenceEnv referenceHistory
      hreferenceEnv hreferenceHistory bestAction hbestAction
    let sampler := policySamplerMeasure mu history hhistory policy
    ProbabilityTheory.condDistrib policySamplerAction
        (policySamplerHistory history) sampler =ᵐ[
      sampler.map (policySamplerHistory history)]
      ProbabilityTheory.condDistrib (bestAction ∘ policySamplerEnv env)
        (policySamplerHistory history) sampler := by
  exact
    referencePolicySampler_condDistrib_action_ae_eq_bestAction_of_posterior_invariance
      mu env history henv hhistory referenceMu referenceEnv referenceHistory
      hreferenceEnv hreferenceHistory bestAction hbestAction
      (referencePosterior_ae_eq_condDistrib_of_algorithmDensitySource
        mu env history henv referenceMu referenceEnv referenceHistory
        hreferenceEnv hreferenceHistory source)

/--
Reference-policy Thompson probability matching from an equal environment
marginal and a conditional-history density law, without separately assuming
the two algorithm-density pushforward laws.
-/
theorem referencePolicySampler_condDistrib_action_ae_eq_bestAction_of_condDistrib_history_withDensity
    {Omega : Type u} {OmegaRef : Type v}
    {History : Type w} {Env : Type x} {Action : Type y}
    [MeasurableSpace Omega] [MeasurableSpace OmegaRef]
    [MeasurableSpace History] [StandardBorelSpace History] [Nonempty History]
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
    (density : History -> ENNReal) (hdensity : Measurable density)
    (henvLaw : mu.map env = referenceMu.map referenceEnv)
    (hcond :
      ProbabilityTheory.condDistrib history env mu =ᵐ[mu.map env]
        (ProbabilityTheory.condDistrib
          referenceHistory referenceEnv referenceMu).withDensity
            (fun _ history => density history))
    (bestAction : Env -> Action) (hbestAction : Measurable bestAction) :
    let policy := referenceActionKernel referenceMu referenceEnv referenceHistory
      hreferenceEnv hreferenceHistory bestAction hbestAction
    let sampler := policySamplerMeasure mu history hhistory policy
    ProbabilityTheory.condDistrib policySamplerAction
        (policySamplerHistory history) sampler =ᵐ[
      sampler.map (policySamplerHistory history)]
      ProbabilityTheory.condDistrib (bestAction ∘ policySamplerEnv env)
        (policySamplerHistory history) sampler := by
  let source :=
    algorithmDensityPosteriorSource_of_condDistrib_history_withDensity
      mu env history henv hhistory
      referenceMu referenceEnv referenceHistory hreferenceEnv hreferenceHistory
      density hdensity henvLaw hcond
  exact
    referencePolicySampler_condDistrib_action_ae_eq_bestAction_of_algorithmDensitySource
      mu env history henv hhistory
      referenceMu referenceEnv referenceHistory hreferenceEnv hreferenceHistory
      bestAction hbestAction source

/--
Finite action/reward-prefix Thompson probability matching from a packaged pair
of algorithm-density laws.
-/
theorem finitePairReferencePolicySampler_condDistrib_action_ae_eq_bestAction_of_algorithmDensitySource
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
    (source : AlgorithmDensityPosteriorSource mu env
      (fun omega => History.finitePairHistoryOfTrace
        (action omega) (reward omega) n)
      referenceMu referenceEnv
      (fun omega => History.finitePairHistoryOfTrace
        (referenceAction omega) (referenceReward omega) n)) :
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
  have hresult :=
    referencePolicySampler_condDistrib_action_ae_eq_bestAction_of_algorithmDensitySource
      mu env actualHistory henv hactualHistory
      referenceMu referenceEnv referenceHistory hreferenceEnv hreferenceHistory
      bestAction hbestAction source
  simpa only [actualHistory, referenceHistory] using hresult

/--
Finite action/reward-prefix Thompson probability matching from an equal
environment marginal and a conditional finite-history density law.
-/
theorem finitePairReferencePolicySampler_condDistrib_action_ae_eq_bestAction_of_condDistrib_history_withDensity
    {Omega : Type u} {OmegaRef : Type v}
    {Env : Type w} {Action : Type x} {Reward : Type y}
    [MeasurableSpace Omega] [MeasurableSpace OmegaRef]
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [StandardBorelSpace Action] [Nonempty Action]
    [MeasurableSpace Reward] [StandardBorelSpace Reward] [Nonempty Reward]
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
    (density : History.FinitePairHistory Action Reward n -> ENNReal)
    (hdensity : Measurable density)
    (henvLaw : mu.map env = referenceMu.map referenceEnv)
    (hcond :
      ProbabilityTheory.condDistrib
          (fun omega => History.finitePairHistoryOfTrace
            (action omega) (reward omega) n) env mu =ᵐ[mu.map env]
        (ProbabilityTheory.condDistrib
          (fun omega => History.finitePairHistoryOfTrace
            (referenceAction omega) (referenceReward omega) n)
          referenceEnv referenceMu).withDensity
            (fun _ history => density history))
    (bestAction : Env -> Action) (hbestAction : Measurable bestAction) :
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
  have hresult :=
    referencePolicySampler_condDistrib_action_ae_eq_bestAction_of_condDistrib_history_withDensity
      mu env actualHistory henv hactualHistory
      referenceMu referenceEnv referenceHistory hreferenceEnv hreferenceHistory
      density hdensity henvLaw hcond bestAction hbestAction
  simpa only [actualHistory, referenceHistory] using hresult

end Thompson
end BanditRLProof
