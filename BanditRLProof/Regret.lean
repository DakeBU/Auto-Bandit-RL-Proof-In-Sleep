import BanditRLProof.Core

/-!
# Regret surfaces

The first layer records pseudo-regret as an executable recursive object over
finite arms and rational means.  Later Mathlib-heavy files can connect this to
expectations, conditional distributions, martingales, or concentration.
-/

namespace BanditRLProof

open FiniteBanditModel

/-- Pseudo-regret accumulated from the model gaps along an action trace. -/
noncomputable def pseudoRegret (model : FiniteBanditModel K)
    (action : Nat → Fin K) : Nat → Rat
  | 0 => 0
  | t + 1 => pseudoRegret model action t + model.gap (action t)

@[simp] theorem pseudoRegret_zero (model : FiniteBanditModel K)
    (action : Nat → Fin K) :
    pseudoRegret model action 0 = 0 := rfl

@[simp] theorem pseudoRegret_succ (model : FiniteBanditModel K)
    (action : Nat → Fin K) (t : Nat) :
    pseudoRegret model action (t + 1) =
      pseudoRegret model action t + model.gap (action t) := rfl

/-- A reusable record for theorem-card style regret bounds. -/
structure RegretBoundCard where
  theoremName : String
  algorithm : String
  modelClass : String
  statement : String
  leanStatus : CertificateStatus
  proofDependencies : List String
deriving Repr

/-- A proof obligation attached to a regret theorem. -/
structure RegretObligation where
  id : String
  target : String
  ownerRole : String
  dependencies : List String
  leanDeclaration : String
  status : CertificateStatus
deriving Repr

end BanditRLProof
