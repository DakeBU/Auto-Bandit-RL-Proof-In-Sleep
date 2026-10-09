import Mathlib.Analysis.Calculus.Deriv.Abs
import BanditRLProof.OnlineHinge
import BanditRLProof.OnlineSubgradientDifferentiability

noncomputable section
open scoped InnerProductSpace

#check (∀ (c : ℝ),
    ConvexOn ℝ Set.univ (fun x : ℝ => |x - c|) ∧
      ∀ x : ℝ, DifferentiableAt ℝ (fun w : ℝ => |w - c|) x ↔ x ≠ c)

#check (∀ {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (a : E),
    ConvexOn ℝ Set.univ (fun x : E => max (1 - inner ℝ a x) 0) ∧
      ∀ x : E, DifferentiableAt ℝ (fun w : E => max (1 - inner ℝ a w) 0) x ↔
        inner ℝ a x ≠ 1)

#check (∀ {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (y : ℝ) (z : E),
    ConvexOn ℝ Set.univ (fun x : E => max (1 - y * inner ℝ z x) 0) ∧
      (∀ x : E, DifferentiableAt ℝ (fun w : E => max (1 - y * inner ℝ z w) 0) x ↔
        y * inner ℝ z x ≠ 1) ∧
      (Differentiable ℝ (fun w : E => max (1 - y * inner ℝ z w) 0) ↔ y • z = 0))

#check ConvexOn.sup
#check ConvexOn.comp_affineMap
#check convexOn_univ_norm
#check convexOn_const
#check AffineMap.const
#check not_differentiableAt_abs_zero
#check DifferentiableAt.abs
#check real_inner_smul_left
#check real_inner_smul_right
#check inner_self_ne_zero
#check BanditRL.OnlineConvex.example_2_27
#check BanditRL.OnlineConvex.theorem_2_22
#check BanditRL.OnlineConvex.sourceDifferentiableAt_regular
