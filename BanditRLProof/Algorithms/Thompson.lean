import BanditRLProof.Regret

/-!
# Thompson sampling and Bayesian regret surfaces
-/

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
  [ "posterior_best_action_distribution"
  , "bayes_regret_decomposition"
  , "clipped_ucb_bridge"
  , "bounded_mean_and_subgaussian_contract"
  , "bayesian_regret_bound"
  ]

end Thompson
end BanditRLProof
