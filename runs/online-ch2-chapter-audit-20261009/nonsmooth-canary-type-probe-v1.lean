import BanditRLProof.OnlineNonsmoothExamples
import Tests.OnlineGradientDescentSourceCanary
open scoped InnerProductSpace
open Tests.OnlineGradientDescentSource

#check (    ConvexOn ℝ Set.univ (fun w : ℝ => |w - 10|) ∧
      ¬ DifferentiableAt ℝ (fun w : ℝ => |w - 10|) 10 ∧
      DifferentiableAt ℝ (fun w : ℝ => |w - 10|) 9 ∧
      DifferentiableAt ℝ (fun w : ℝ => |w - 10|) 11)

#check (    ConvexOn ℝ Set.univ (fun w : ℝ => max (1 - 2 * inner ℝ (3 : ℝ) w) 0) ∧
      ConvexOn ℝ Set.univ (fun w : ℝ => max (1 - (-2) * inner ℝ (3 : ℝ) w) 0) ∧
      ¬ DifferentiableAt ℝ (fun w : ℝ => max (1 - 2 * inner ℝ (3 : ℝ) w) 0) (1 / 6) ∧
      ¬ DifferentiableAt ℝ (fun w : ℝ => max (1 - (-2) * inner ℝ (3 : ℝ) w) 0) (-1 / 6) ∧
      DifferentiableAt ℝ (fun w : ℝ => max (1 - 2 * inner ℝ (3 : ℝ) w) 0) 0 ∧
      DifferentiableAt ℝ (fun w : ℝ => max (1 - (-2) * inner ℝ (3 : ℝ) w) 0) 0 ∧
      ¬ Differentiable ℝ (fun w : ℝ => max (1 - 2 * inner ℝ (3 : ℝ) w) 0) ∧
      ¬ Differentiable ℝ (fun w : ℝ => max (1 - (-2) * inner ℝ (3 : ℝ) w) 0))

#check (∀ (y z : ℝ),
    Differentiable ℝ (fun w : ℝ => max (1 - 0 * inner ℝ z w) 0) ∧
      Differentiable ℝ (fun w : ℝ => max (1 - y * inner ℝ (0 : ℝ) w) 0) ∧
      ∀ w : ℝ, max (1 - 0 * inner ℝ z w) 0 = 1 ∧
        max (1 - y * inner ℝ (0 : ℝ) w) 0 = 1)

#check (    ¬ DifferentiableAt ℝ (fun w : Plane => max (1 - inner ℝ e0 w) 0)
        (e0 + (3 : ℝ) • e1) ∧
      DifferentiableAt ℝ (fun w : Plane => max (1 - inner ℝ e0 w) 0) e1 ∧
      DifferentiableAt ℝ (fun t : ℝ => max (1 - inner ℝ e0 (e0 + t • e1)) 0) 0)

#check (∀ (y : ℝ) (z : EuclideanSpace ℝ (Fin 0)),
    Differentiable ℝ
        (fun w : EuclideanSpace ℝ (Fin 0) => max (1 - y * inner ℝ z w) 0) ∧
      ∀ w : EuclideanSpace ℝ (Fin 0), max (1 - y * inner ℝ z w) 0 = 1)
