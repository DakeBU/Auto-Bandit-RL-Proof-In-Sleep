# Neutral concrete-proposition reconstruction packet

Only read this packet and the accompanying input JSON. No source/history/repository search, proof or compilation. Reconstruct every complete terminal in prose/LaTeX/seven slots, distinguishing pointwise/global/ambient/tangential derivatives and the degenerate tests. Role history reused, not absolute blindness.

Notation: inner is the real inner product. DifferentiableAt is ordinary real ambient Fréchet differentiability at the specified point; Differentiable is at every ambient point. ConvexOn on univ is global convexity. These neutral aliases are exact mathematical values:

```lean
abbrev Plane := EuclideanSpace ℝ (Fin 2)
def e0 : Plane := EuclideanSpace.single 0 1
def e1 : Plane := EuclideanSpace.single 1 1
open scoped InnerProductSpace
```

No additional section variables or hypotheses.

```lean
theorem TerminalC001 :
    ConvexOn ℝ Set.univ (fun w : ℝ => |w - 10|) ∧
      ¬ DifferentiableAt ℝ (fun w : ℝ => |w - 10|) 10 ∧
      DifferentiableAt ℝ (fun w : ℝ => |w - 10|) 9 ∧
      DifferentiableAt ℝ (fun w : ℝ => |w - 10|) 11

theorem TerminalC002 :
    ConvexOn ℝ Set.univ (fun w : ℝ => max (1 - 2 * inner ℝ (3 : ℝ) w) 0) ∧
      ConvexOn ℝ Set.univ (fun w : ℝ => max (1 - (-2) * inner ℝ (3 : ℝ) w) 0) ∧
      ¬ DifferentiableAt ℝ (fun w : ℝ => max (1 - 2 * inner ℝ (3 : ℝ) w) 0) (1 / 6) ∧
      ¬ DifferentiableAt ℝ (fun w : ℝ => max (1 - (-2) * inner ℝ (3 : ℝ) w) 0) (-1 / 6) ∧
      DifferentiableAt ℝ (fun w : ℝ => max (1 - 2 * inner ℝ (3 : ℝ) w) 0) 0 ∧
      DifferentiableAt ℝ (fun w : ℝ => max (1 - (-2) * inner ℝ (3 : ℝ) w) 0) 0 ∧
      ¬ Differentiable ℝ (fun w : ℝ => max (1 - 2 * inner ℝ (3 : ℝ) w) 0) ∧
      ¬ Differentiable ℝ (fun w : ℝ => max (1 - (-2) * inner ℝ (3 : ℝ) w) 0)

theorem TerminalC003 (y z : ℝ) :
    Differentiable ℝ (fun w : ℝ => max (1 - 0 * inner ℝ z w) 0) ∧
      Differentiable ℝ (fun w : ℝ => max (1 - y * inner ℝ (0 : ℝ) w) 0) ∧
      ∀ w : ℝ, max (1 - 0 * inner ℝ z w) 0 = 1 ∧
        max (1 - y * inner ℝ (0 : ℝ) w) 0 = 1

theorem TerminalC004 :
    ¬ DifferentiableAt ℝ (fun w : Plane => max (1 - inner ℝ e0 w) 0)
        (e0 + (3 : ℝ) • e1) ∧
      DifferentiableAt ℝ (fun w : Plane => max (1 - inner ℝ e0 w) 0) e1 ∧
      DifferentiableAt ℝ (fun t : ℝ => max (1 - inner ℝ e0 (e0 + (3 + t) • e1)) 0) 0

theorem TerminalC005 (y : ℝ) (z : EuclideanSpace ℝ (Fin 0)) :
    Differentiable ℝ
        (fun w : EuclideanSpace ℝ (Fin 0) => max (1 - y * inner ℝ z w) 0) ∧
      ∀ w : EuclideanSpace ℝ (Fin 0), max (1 - y * inner ℝ z w) 0 = 1

```
