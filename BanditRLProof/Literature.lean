import BanditRLProof.Algorithms.ETC
import BanditRLProof.Algorithms.UCB
import BanditRLProof.Algorithms.Thompson

/-!
# Literature and upstream theorem registry
-/

namespace BanditRLProof

/-- Public upstream source used by the memory layer. -/
structure UpstreamRef where
  key : String
  title : String
  url : String
  revision : String
  license : String
  useInProject : String
deriving Repr

/-- Main upstream Lean library for bandit formalization. -/
def lmlRef : UpstreamRef where
  key := "LML"
  title := "Lean Machine Learning"
  url := "https://github.com/LeanMachineLearning/LML"
  revision := "19dc3ab132c2a7539f5944503d1114eac4c5bb74"
  license := "Apache-2.0"
  useInProject := "Bandit theorem-card source and optional future dependency."

/-- Selected LML declarations that seed the retrieval memory. -/
def lmlBanditDeclarationCards : List RegretBoundCard :=
  [ { theoremName := "Bandits.regret_eq_sum_gap"
      algorithm := "generic finite stochastic bandit"
      modelClass := "finite actions with mean reward kernel"
      statement := "Regret equals the sum of action gaps over the played trace."
      leanStatus := CertificateStatus.insight
      proofDependencies := ["gap", "regret"] }
  , { theoremName := "Bandits.ETC.regret_le"
      algorithm := "Explore-Then-Commit"
      modelClass := "finite sub-Gaussian stochastic bandit"
      statement := "Expected regret is bounded by exploration cost plus wrong-commit probability terms."
      leanStatus := CertificateStatus.insight
      proofDependencies := ETC.obligationNames }
  , { theoremName := "Bandits.UCB.regret_le"
      algorithm := "UCB"
      modelClass := "finite sub-Gaussian stochastic bandit"
      statement := "Expected regret is controlled by logarithmic pull-count bounds for suboptimal arms."
      leanStatus := CertificateStatus.insight
      proofDependencies := UCB.obligationNames }
  , { theoremName := "Bandits.TS.hasCondDistrib_action"
      algorithm := "Thompson sampling"
      modelClass := "Bayesian stochastic bandit"
      statement := "The next action distribution matches the posterior distribution of the best action."
      leanStatus := CertificateStatus.insight
      proofDependencies := Thompson.obligationNames }
  ]

end BanditRLProof
