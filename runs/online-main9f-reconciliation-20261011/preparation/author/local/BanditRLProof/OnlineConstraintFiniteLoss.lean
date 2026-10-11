/-
Source: Orabona, Online Learning, arXiv:1912.13213v10, Section 2.1.1,
printed pp.9-10 / PDF pp.21-22, unnumbered finite-loss constraint sentence.
The source necessity is refined to an exact finite-real-witness iff; membership
alone is insufficient when the original loss is infinite. Arbitrary carriers
generalize the source Euclidean setting for this pointwise algebra.
Both results use ordinary EReal addition. The finite criterion permits bottom;
the separate below-top effective-domain identity retains global noBottom.
No convexity, topology, or nonempty-set hypothesis is needed here.
-/
import BanditRLProof.OnlineConvexExtended

noncomputable section
open Set
namespace BanditRL.OnlineConvex

/-- Exact finite-real locus of adding the constraint indicator. -/
theorem finite_add_indicator_iff {E : Type*} (f : E → EReal) (V : Set E) (x : E) :
    (∃ r : ℝ, f x + extendedIndicator V x = (r : EReal)) ↔
      x ∈ V ∧ ∃ r : ℝ, f x = (r : EReal) := by
  classical
  by_cases hx : x ∈ V
  · simp [extendedIndicator, hx]
  · constructor
    · rintro ⟨r, hr⟩
      cases hfx : f x <;> simp [extendedIndicator, hx, hfx] at hr
    · rintro ⟨h, _⟩
      exact (hx h).elim

/-- Below-top domain intersection for ordinary addition, excluding bottom globally. -/
theorem effectiveDomain_add_indicator {E : Type*} (f : E → EReal)
    (hbot : ∀ x, f x ≠ ⊥) (V : Set E) :
    effectiveDomain (fun x => f x + extendedIndicator V x) = effectiveDomain f ∩ V := by
  classical
  ext x
  by_cases hx : x ∈ V
  · simp [effectiveDomain, extendedIndicator, hx]
  · simp [effectiveDomain, extendedIndicator, hx, EReal.add_top_of_ne_bot (hbot x)]

end BanditRL.OnlineConvex
