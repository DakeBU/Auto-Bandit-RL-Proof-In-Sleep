import BanditRLProof.OnlineClosedProper
import Mathlib.Analysis.Convex.Strong

noncomputable section
open Set
namespace BanditRL.OnlineConvex

def stronglyConvex_minimum_growth_typeprobe {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → EReal) (V : Set E) (lam : ℝ)
    (hf : SourceProper f) (hV : Convex ℝ V)
    (hdom : V ⊆ effectiveDomain f) (hlam : 0 ≤ lam)
    (hstrong : ∀ x ∈ V, ∀ y ∈ V, ∀ a : ℝ, 0 < a → a < 1 →
      f (a • x + (1 - a) • y) ≤
        (a : EReal) * f x + ((1 - a : ℝ) : EReal) * f y -
          (((lam / 2) * a * (1 - a) * ‖x - y‖ ^ 2 : ℝ) : EReal))
    (p : E) (hp : p ∈ V) (hmin : IsMinOn f V p)
    (q : E) (hq : q ∈ V) : Prop :=
    (f p).toReal + (lam / 2) * ‖q - p‖ ^ 2 ≤ (f q).toReal

#check stronglyConvex_minimum_growth_typeprobe
#print stronglyConvex_minimum_growth_typeprobe
#check SourceProper
#print SourceProper
#print effectiveDomain
#print StrongConvexOn
#print UniformConvexOn
#check IsMinOn
#check EReal.coe_toReal
#check EReal.toReal_le_toReal

end BanditRL.OnlineConvex
