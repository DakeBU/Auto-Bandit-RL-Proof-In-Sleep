import BanditRLProof.OnlineNonsmoothExamples
open scoped InnerProductSpace
example (c : ℝ) :
    ConvexOn ℝ Set.univ (fun x : ℝ => |x - c|) ∧
      ∀ x : ℝ, DifferentiableAt ℝ (fun w : ℝ => |w - c|) x ↔ x ≠ c :=
  BanditRL.OnlineConvex.shifted_absolute_convex_differentiable_iff c
#print axioms BanditRL.OnlineConvex.shifted_absolute_convex_differentiable_iff
