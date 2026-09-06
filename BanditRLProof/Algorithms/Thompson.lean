import BanditRLProof.Regret
import BanditRLProof.PosteriorKernel
import Mathlib.Probability.Kernel.CondDistrib

/-!
# Thompson sampling and Bayesian regret surfaces
-/

open MeasureTheory

universe u v w

namespace BanditRLProof
namespace Thompson

/-- A lightweight descriptor for a Bayesian bandit parameter space. -/
structure PriorSketch where
  parameterName : String
  priorName : String
  rewardKernelName : String
deriving Repr

/-- The proof-DAG leaves usually needed for Thompson sampling regret. -/
def obligationNames : List String :=
  [ "posterior_action_identity_ledger"
  , "posterior_best_action_distribution"
  , "canonical_posterior_pair_law"
  , "thompson_next_action_conditional_law"
  , "canonical_thompson_sampler_law"
  , "reference_posterior_policy_sampler"
  , "algorithm_density_posterior_invariance"
  , "recursive_algorithm_density_laws"
  , "recursive_thompson_trace"
  , "bayes_regret_decomposition"
  , "clipped_ucb_bridge"
  , "bounded_mean_and_subgaussian_contract"
  , "bayesian_regret_bound"
  ]

/--
Source contract for the Thompson probability-matching identity.

The ledger records the exact law expected from a Thompson action sampler: its
action kernel at a history agrees on every measurable action event with the
posterior distribution pushed forward by the environment-to-best-action map.
It is a contract surface, not a Bayes-rule proof or posterior-sampler
construction.
-/
structure PosteriorActionIdentityLedger
    (History : Type u) (Env : Type v) (Action : Type w)
    [MeasurableSpace History] [MeasurableSpace Env] [MeasurableSpace Action]
    where
  posterior : PosteriorKernel.MarkovPosteriorKernel History Env
  actionKernel : ProbabilityTheory.Kernel History Action
  actionKernel_isMarkov : ProbabilityTheory.IsMarkovKernel actionKernel
  bestAction : Env -> Action
  bestAction_measurable : Measurable bestAction
  actionKernel_eq_posteriorBest :
    forall (history : History) {event : Set Action},
      MeasurableSet event ->
        actionKernel history event =
          Measure.map bestAction (posterior.kernel history) event

/--
Any best-action selector out of a countable singleton-measurable environment
space is measurable.

This is the regularity wrapper needed by finite or countable posterior model
spaces before constructing a Thompson posterior-action identity ledger.
-/
theorem bestAction_measurable_of_countable_env
    {Env : Type v} {Action : Type w}
    [MeasurableSpace Env] [MeasurableSingletonClass Env] [Countable Env]
    [MeasurableSpace Action]
    (bestAction : Env -> Action) :
    Measurable bestAction :=
  measurable_of_countable bestAction

namespace PosteriorActionIdentityLedger

variable {History : Type u} {Env : Type v} {Action : Type w}
    [MeasurableSpace History] [MeasurableSpace Env] [MeasurableSpace Action]

instance instActionKernelIsMarkovKernel
    (ledger : PosteriorActionIdentityLedger History Env Action) :
    ProbabilityTheory.IsMarkovKernel ledger.actionKernel :=
  ledger.actionKernel_isMarkov

/--
Build a posterior-action identity ledger over a countable environment space
without separately supplying best-action measurability.
-/
def ofCountableEnv
    [MeasurableSingletonClass Env] [Countable Env]
    (posterior : PosteriorKernel.MarkovPosteriorKernel History Env)
    (actionKernel : ProbabilityTheory.Kernel History Action)
    (hactionKernel : ProbabilityTheory.IsMarkovKernel actionKernel)
    (bestAction : Env -> Action)
    (hmatch :
      forall (history : History) {event : Set Action},
        MeasurableSet event ->
          actionKernel history event =
            Measure.map bestAction (posterior.kernel history) event) :
    PosteriorActionIdentityLedger History Env Action where
  posterior := posterior
  actionKernel := actionKernel
  actionKernel_isMarkov := hactionKernel
  bestAction := bestAction
  bestAction_measurable := bestAction_measurable_of_countable_env bestAction
  actionKernel_eq_posteriorBest := hmatch

/--
Build the Thompson action ledger directly by mapping a posterior kernel through
a measurable best-action selector.
-/
noncomputable def ofPosteriorMap
    (posterior : PosteriorKernel.MarkovPosteriorKernel History Env)
    (bestAction : Env -> Action) (hbestAction : Measurable bestAction) :
    PosteriorActionIdentityLedger History Env Action where
  posterior := posterior
  actionKernel := posterior.kernel.map bestAction
  actionKernel_isMarkov :=
    ProbabilityTheory.Kernel.IsMarkovKernel.map posterior.kernel hbestAction
  bestAction := bestAction
  bestAction_measurable := hbestAction
  actionKernel_eq_posteriorBest := by
    intro history event hevent
    rw [ProbabilityTheory.Kernel.map_apply _ hbestAction]

/-- The event-level ledger identity is equality of the two Markov kernels. -/
theorem actionKernel_eq_posterior_map
    (ledger : PosteriorActionIdentityLedger History Env Action) :
    ledger.actionKernel = ledger.posterior.kernel.map ledger.bestAction := by
  ext history event hevent
  rw [ProbabilityTheory.Kernel.map_apply _ ledger.bestAction_measurable]
  exact ledger.actionKernel_eq_posteriorBest history hevent

/--
Event-level Thompson probability matching from the packaged ledger.
-/
theorem actionKernel_apply_eq_posteriorBest_map
    (ledger : PosteriorActionIdentityLedger History Env Action)
    (history : History) {event : Set Action}
    (hevent : MeasurableSet event) :
    ledger.actionKernel history event =
      Measure.map ledger.bestAction (ledger.posterior.kernel history) event :=
  ledger.actionKernel_eq_posteriorBest history hevent

/--
Singleton form of the posterior action identity.

For discrete or singleton-measurable action spaces, the Thompson probability of
choosing `action` is the posterior probability that `action` is the best action.
-/
theorem actionKernel_apply_singleton_eq_posteriorBest_preimage
    [MeasurableSingletonClass Action]
    (ledger : PosteriorActionIdentityLedger History Env Action)
    (history : History) (action : Action) :
    ledger.actionKernel history ({action} : Set Action) =
      ledger.posterior.kernel history {env : Env | ledger.bestAction env = action} := by
  rw [actionKernel_apply_eq_posteriorBest_map ledger history
    (MeasurableSet.singleton action)]
  rw [Measure.map_apply ledger.bestAction_measurable
    (MeasurableSet.singleton action)]
  rfl

end PosteriorActionIdentityLedger

/--
Source fields needed for the Thompson posterior-action conditional-law theorem.

The first law says the process samples its next action from the ledger action
kernel. The second identifies the ledger posterior with the conditional law of
the latent environment given the observed history. These are the two law
surfaces used by the pinned LML proof.
-/
structure BayesianPosteriorActionSource
    {Omega : Type u} (History : Type v) (Env : Type w) (Action : Type*)
    [MeasurableSpace Omega] [MeasurableSpace History]
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [StandardBorelSpace Action] [Nonempty Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (env : Omega -> Env) (history : Omega -> History)
    (nextAction : Omega -> Action)
    (ledger : PosteriorActionIdentityLedger History Env Action) : Prop where
  measurable_env : Measurable env
  measurable_history : Measurable history
  measurable_nextAction : Measurable nextAction
  hasCondDistrib_actionKernel :
    ProbabilityTheory.condDistrib nextAction history mu =ᵐ[mu.map history]
      ledger.actionKernel
  posterior_eq_condDistrib_env :
    ledger.posterior.kernel =ᵐ[mu.map history]
      ProbabilityTheory.condDistrib env history mu

/--
Thompson probability matching in Mathlib `condDistrib` form.

Mapping the posterior-kernel equality through `bestAction` identifies the
ledger action kernel with the mapped environment conditional law. Mathlib's
`condDistrib_comp` then identifies that map with the conditional law of the
random best action itself.
-/
theorem condDistrib_action_ae_eq_bestAction_of_bayesianPosteriorActionSource
    {Omega : Type u} {History : Type v} {Env : Type w} {Action : Type*}
    [MeasurableSpace Omega] [MeasurableSpace History]
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [StandardBorelSpace Action] [Nonempty Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (env : Omega -> Env) (history : Omega -> History)
    (nextAction : Omega -> Action)
    (ledger : PosteriorActionIdentityLedger History Env Action)
    (source : BayesianPosteriorActionSource
      History Env Action mu env history nextAction ledger) :
    ProbabilityTheory.condDistrib nextAction history mu =ᵐ[mu.map history]
      ProbabilityTheory.condDistrib (ledger.bestAction ∘ env) history mu := by
  have haction :
      ProbabilityTheory.condDistrib nextAction history mu =ᵐ[mu.map history]
        ledger.posterior.kernel.map ledger.bestAction := by
    simpa only [ledger.actionKernel_eq_posterior_map] using
      source.hasCondDistrib_actionKernel
  have hposteriorMap :
      ledger.posterior.kernel.map ledger.bestAction =ᵐ[mu.map history]
        (ProbabilityTheory.condDistrib env history mu).map ledger.bestAction := by
    filter_upwards [source.posterior_eq_condDistrib_env] with observed hposterior
    rw [ProbabilityTheory.Kernel.map_apply _ ledger.bestAction_measurable,
      ProbabilityTheory.Kernel.map_apply _ ledger.bestAction_measurable]
    exact congrArg (Measure.map ledger.bestAction) hposterior
  exact haction.trans <| hposteriorMap.trans <|
    (ProbabilityTheory.condDistrib_comp
      history source.measurable_env.aemeasurable
      ledger.bestAction_measurable).symm

/--
Direct posterior-map form of Thompson probability matching.

This is the local Mathlib-facing counterpart of pinned LML
`Bandits.TS.hasCondDistrib_action`: it avoids a local `HasCondDistrib` wrapper
and states the resulting regular conditional-kernel equality directly.
-/
theorem condDistrib_action_ae_eq_bestAction_of_posteriorMap
    {Omega : Type u} {History : Type v} {Env : Type w} {Action : Type*}
    [MeasurableSpace Omega] [MeasurableSpace History]
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [StandardBorelSpace Action] [Nonempty Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (env : Omega -> Env) (history : Omega -> History)
    (nextAction : Omega -> Action)
    (posterior : PosteriorKernel.MarkovPosteriorKernel History Env)
    (bestAction : Env -> Action) (hbestAction : Measurable bestAction)
    (henv : Measurable env) (hhistory : Measurable history)
    (hnextAction : Measurable nextAction)
    (haction :
      ProbabilityTheory.condDistrib nextAction history mu =ᵐ[mu.map history]
        posterior.kernel.map bestAction)
    (hposterior :
      posterior.kernel =ᵐ[mu.map history]
        ProbabilityTheory.condDistrib env history mu) :
    ProbabilityTheory.condDistrib nextAction history mu =ᵐ[mu.map history]
      ProbabilityTheory.condDistrib (bestAction ∘ env) history mu := by
  let ledger := PosteriorActionIdentityLedger.ofPosteriorMap
    posterior bestAction hbestAction
  let source : BayesianPosteriorActionSource
      History Env Action mu env history nextAction ledger :=
    { measurable_env := henv
      measurable_history := hhistory
      measurable_nextAction := hnextAction
      hasCondDistrib_actionKernel := by
        simpa only [ledger, PosteriorActionIdentityLedger.ofPosteriorMap] using haction
      posterior_eq_condDistrib_env := by
        simpa only [ledger, PosteriorActionIdentityLedger.ofPosteriorMap] using hposterior }
  simpa only [ledger, PosteriorActionIdentityLedger.ofPosteriorMap] using
    condDistrib_action_ae_eq_bestAction_of_bayesianPosteriorActionSource
      mu env history nextAction ledger source

/--
Thompson probability matching from a Bayesian environment/history pair law.

Unlike `condDistrib_action_ae_eq_bestAction_of_posteriorMap`, this theorem does
not assume the posterior/environment conditional-law equality.  It constructs
that equality from the source pair law using Mathlib's canonical posterior.
-/
theorem condDistrib_action_ae_eq_bestAction_of_bayesianPairMap
    {Omega : Type u} {History : Type v} {Env : Type w} {Action : Type*}
    [MeasurableSpace Omega] [MeasurableSpace History]
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [StandardBorelSpace Action] [Nonempty Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (env : Omega -> Env) (history : Omega -> History)
    (nextAction : Omega -> Action)
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (likelihood : ProbabilityTheory.Kernel Env History)
    [ProbabilityTheory.IsMarkovKernel likelihood]
    (bestAction : Env -> Action) (hbestAction : Measurable bestAction)
    (henv : Measurable env) (hhistory : Measurable history)
    (hnextAction : Measurable nextAction)
    (hpair :
      mu.map (fun omega => (env omega, history omega)) =
        PosteriorKernel.canonicalJointMeasure prior likelihood)
    (haction :
      ProbabilityTheory.condDistrib nextAction history mu =ᵐ[mu.map history]
        (PosteriorKernel.canonicalPosterior prior likelihood).kernel.map
          bestAction) :
    ProbabilityTheory.condDistrib nextAction history mu =ᵐ[mu.map history]
      ProbabilityTheory.condDistrib (bestAction ∘ env) history mu := by
  exact condDistrib_action_ae_eq_bestAction_of_posteriorMap
    mu env history nextAction
    (PosteriorKernel.canonicalPosterior prior likelihood)
    bestAction hbestAction henv hhistory hnextAction haction
    (PosteriorKernel.canonicalPosterior_kernel_ae_eq_condDistrib_of_pair_map_eq
      mu env history henv hhistory prior likelihood hpair)

/--
Canonical-product specialization of the Thompson posterior-action law.

The source space is `Env × History` with law `prior ⊗ₘ likelihood`, so the
posterior conditional-law premise is discharged entirely by the canonical
Bayesian construction.  The remaining law premise is exactly the Thompson
action sampler's conditional law.
-/
theorem condDistrib_action_ae_eq_bestAction_of_canonicalPriorLikelihood
    {History : Type u} {Env : Type v} {Action : Type w}
    [MeasurableSpace History]
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [StandardBorelSpace Action] [Nonempty Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (likelihood : ProbabilityTheory.Kernel Env History)
    [ProbabilityTheory.IsMarkovKernel likelihood]
    (nextAction : Env × History -> Action)
    (bestAction : Env -> Action) (hbestAction : Measurable bestAction)
    (hnextAction : Measurable nextAction)
    (haction :
      ProbabilityTheory.condDistrib nextAction Prod.snd
          (PosteriorKernel.canonicalJointMeasure prior likelihood) =ᵐ[
        (PosteriorKernel.canonicalJointMeasure prior likelihood).map Prod.snd]
          (PosteriorKernel.canonicalPosterior prior likelihood).kernel.map
            bestAction) :
    ProbabilityTheory.condDistrib nextAction Prod.snd
        (PosteriorKernel.canonicalJointMeasure prior likelihood) =ᵐ[
      (PosteriorKernel.canonicalJointMeasure prior likelihood).map Prod.snd]
        ProbabilityTheory.condDistrib (bestAction ∘ Prod.fst) Prod.snd
          (PosteriorKernel.canonicalJointMeasure prior likelihood) := by
  apply condDistrib_action_ae_eq_bestAction_of_bayesianPairMap
    (PosteriorKernel.canonicalJointMeasure prior likelihood)
    Prod.fst Prod.snd nextAction prior likelihood bestAction hbestAction
    measurable_fst measurable_snd hnextAction
  · simp [PosteriorKernel.canonicalJointMeasure]
  · exact haction

end Thompson
end BanditRLProof
