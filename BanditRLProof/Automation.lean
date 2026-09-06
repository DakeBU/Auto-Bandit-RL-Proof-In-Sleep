import BanditRLProof.Literature

/-!
# Automation contracts

This file makes the harness roles and artifacts part of the compiled Lean
project.  It does not run agents; it records the protocol that external agents
must satisfy.
-/

namespace BanditRLProof

inductive HarnessProfile where
  | hierarchical
deriving Repr, DecidableEq

inductive AgentRole where
  | upper
  | middle
  | lower
  | reviewer
deriving Repr, DecidableEq

inductive TaskKind where
  | literaturePort
  | theoremFormalization
  | proofRepair
  | openProblemProposal
  | naturalLanguageExport
deriving Repr, DecidableEq

inductive TaskStatus where
  | planned
  | active
  | blocked
  | leanCompiles
  | exported
deriving Repr, DecidableEq

structure ArtifactSpec where
  path : String
  purpose : String
  mustCompile : Bool
deriving Repr, DecidableEq

structure AcceptanceGate where
  name : String
  command : String
  required : Bool
  note : String
deriving Repr, DecidableEq

structure HarnessTask where
  id : String
  title : String
  kind : TaskKind
  status : TaskStatus
  targetLean : String
  artifacts : List ArtifactSpec
  gates : List AcceptanceGate
deriving Repr

def defaultLeanGate : AcceptanceGate where
  name := "Lean build"
  command := "lake build && lake build Tests"
  required := true
  note := "Only compiled Lean declarations can enter certified memory."

def defaultHarnessProfile : HarnessProfile := HarnessProfile.hierarchical

end BanditRLProof
