import BanditRLProof.OnlineConvexExtended

noncomputable section
open Set
namespace BanditRL.OnlineConvex

theorem finite_add_indicator_iff {E : Type*} (f : E → EReal) (V : Set E) (x : E) :
    (∃ r : ℝ, f x + extendedIndicator V x = (r : EReal)) ↔
      x ∈ V ∧ ∃ r : ℝ, f x = (r : EReal) := by

theorem effectiveDomain_add_indicator {E : Type*} (f : E → EReal)
    (hbot : ∀ x, f x ≠ ⊥) (V : Set E) :
    effectiveDomain (fun x => f x + extendedIndicator V x) = effectiveDomain f ∩ V := by

end BanditRL.OnlineConvex
