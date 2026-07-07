import BanditRLProof.Regret
import BanditRLProof.PosteriorKernel

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

namespace PosteriorActionIdentityLedger

variable {History : Type u} {Env : Type v} {Action : Type w}
    [MeasurableSpace History] [MeasurableSpace Env] [MeasurableSpace Action]

instance instActionKernelIsMarkovKernel
    (ledger : PosteriorActionIdentityLedger History Env Action) :
    ProbabilityTheory.IsMarkovKernel ledger.actionKernel :=
  ledger.actionKernel_isMarkov

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

end Thompson
end BanditRLProof
