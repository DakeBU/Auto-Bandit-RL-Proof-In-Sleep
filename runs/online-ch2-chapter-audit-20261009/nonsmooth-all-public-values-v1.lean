import BanditRLProof.OnlineNonsmoothExamples
open scoped InnerProductSpace

example (c : ℝ) :
    ConvexOn ℝ Set.univ (fun x : ℝ => |x - c|) ∧
      ∀ x : ℝ, DifferentiableAt ℝ (fun w : ℝ => |w - c|) x ↔ x ≠ c :=
  BanditRL.OnlineConvex.shifted_absolute_convex_differentiable_iff c

#check @BanditRL.OnlineConvex.shifted_absolute_convex_differentiable_iff
#print axioms BanditRL.OnlineConvex.shifted_absolute_convex_differentiable_iff

example {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (a : E) :
    ConvexOn ℝ Set.univ (fun x : E => max (1 - inner ℝ a x) 0) ∧
      ∀ x : E, DifferentiableAt ℝ (fun w : E => max (1 - inner ℝ a w) 0) x ↔
        inner ℝ a x ≠ 1 :=
  BanditRL.OnlineConvex.hinge_convex_differentiable_iff a

#check @BanditRL.OnlineConvex.hinge_convex_differentiable_iff
#print axioms BanditRL.OnlineConvex.hinge_convex_differentiable_iff

example {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (y : ℝ) (z : E) :
    ConvexOn ℝ Set.univ (fun x : E => max (1 - y * inner ℝ z x) 0) ∧
      (∀ x : E, DifferentiableAt ℝ (fun w : E => max (1 - y * inner ℝ z w) 0) x ↔
        y * inner ℝ z x ≠ 1) ∧
      (Differentiable ℝ (fun w : E => max (1 - y * inner ℝ z w) 0) ↔ y • z = 0) :=
  BanditRL.OnlineConvex.labelled_hinge_convex_differentiable_iff y z

#check @BanditRL.OnlineConvex.labelled_hinge_convex_differentiable_iff
#print axioms BanditRL.OnlineConvex.labelled_hinge_convex_differentiable_iff
