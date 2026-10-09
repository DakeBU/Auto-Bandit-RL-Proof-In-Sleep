# Neutral statement-only reconstruction packet

Read only this packet and context; do not search repository/source/history, infer source identity, or prove/check anything. Reconstruct each exact terminal in natural language and LaTeX, all seven semantic slots, degenerate cases and distinction between local-point and global differentiability. Source identity and prior verdict deliberately absent.

Notation: real normed inner-product finite-dimensional E; inner is real inner product; ConvexOn on Set.univ is ambient global convexity; DifferentiableAt is ordinary ambient real Fréchet differentiability at the specified point; Differentiable means at every ambient point; y•z is real scalar multiplication. No hidden section variables.

```lean
open scoped InnerProductSpace
theorem Terminal1 (c : ℝ) :
    ConvexOn ℝ Set.univ (fun x : ℝ => |x - c|) ∧
      ∀ x : ℝ, DifferentiableAt ℝ (fun w : ℝ => |w - c|) x ↔ x ≠ c

theorem Terminal2 {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (a : E) :
    ConvexOn ℝ Set.univ (fun x : E => max (1 - inner ℝ a x) 0) ∧
      ∀ x : E, DifferentiableAt ℝ (fun w : E => max (1 - inner ℝ a w) 0) x ↔
        inner ℝ a x ≠ 1

theorem Terminal3 {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (y : ℝ) (z : E) :
    ConvexOn ℝ Set.univ (fun x : E => max (1 - y * inner ℝ z x) 0) ∧
      (∀ x : E, DifferentiableAt ℝ (fun w : E => max (1 - y * inner ℝ z w) 0) x ↔
        y * inner ℝ z x ≠ 1) ∧
      (Differentiable ℝ (fun w : E => max (1 - y * inner ℝ z w) 0) ↔ y • z = 0)
```
