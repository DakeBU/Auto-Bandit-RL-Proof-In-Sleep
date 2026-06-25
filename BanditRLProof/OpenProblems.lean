import BanditRLProof.Automation

/-!
# Open problem registry
-/

namespace BanditRLProof

inductive ProblemArea where
  | concentration
  | stochasticBandit
  | bayesianBandit
  | contextualBandit
  | adversarialBandit
  | reinforcementLearning
  | leanInfrastructure
deriving Repr, DecidableEq

structure OpenProblem where
  id : String
  area : ProblemArea
  title : String
  target : String
  acceptanceGate : String
  status : CertificateStatus
deriving Repr

def seedOpenProblems : List OpenProblem :=
  [ { id := "BRL-OP-UCB-MATHLIB-001"
      area := ProblemArea.stochasticBandit
      title := "Port the LML UCB regret theorem into local theorem-card memory and optional Lean dependency."
      target := "Bandits.UCB.regret_le-compatible statement"
      acceptanceGate := "lake build && lake build Tests"
      status := CertificateStatus.proofObligation }
  , { id := "BRL-OP-TS-BAYES-001"
      area := ProblemArea.bayesianBandit
      title := "Maintain a Thompson sampling posterior-action proof route."
      target := "Bayesian regret decomposition and clipped-UCB bridge"
      acceptanceGate := "compiled theorem or explicitly blocked cited-result ledger"
      status := CertificateStatus.proofObligation }
  , { id := "BRL-OP-RL-BELLMAN-001"
      area := ProblemArea.reinforcementLearning
      title := "Define a reusable Bellman/regret interface for finite-horizon RL."
      target := "finite MDP value, policy, occupancy, and regret surfaces"
      acceptanceGate := "compiled definitions plus conversion window"
      status := CertificateStatus.typedContract }
  ]

end BanditRLProof
