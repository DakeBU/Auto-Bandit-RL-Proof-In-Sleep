import BanditRLProof.OnlineNonsmoothExamples
open scoped InnerProductSpace
example {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (a : E) :
    ConvexOn ℝ Set.univ (fun x : E => max (1 - inner ℝ a x) 0) ∧
      ∀ x : E, DifferentiableAt ℝ (fun w : E => max (1 - inner ℝ a w) 0) x ↔
        inner ℝ a x ≠ 1 :=
  BanditRL.OnlineConvex.hinge_convex_differentiable_iff a

#print axioms BanditRL.OnlineConvex.hinge_convex_differentiable_iff
