Restricted neutral packet. RequestedGPT6Astra/medium. Read ONLY this packet; no repository/source/history/proof/prior verdict. Decode definition Q and THREE prospective propositions P1/P2/P3 separately in natural language/LaTeX with all seven semantic slots. These are fully elaborated target PROPOSITIONS and actual definition, not already proved theorem bodies. Write ONLY blind-reconstruction-v1.md and blind-receipt-v1.json adjacent to packet, exact raw packet/report SHA, actor/requested settings, no runtime attestation/source acceptance.

```lean
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Normed.Module.Convex
def Q (x : EuclideanSpace ℝ (Fin 2)) : ℝ := |x 0|
-- P1
ConvexOn ℝ Set.univ Q
-- P2
∀ x : EuclideanSpace ℝ (Fin 2), x 0 = 0 → ¬ DifferentiableAt ℝ Q x
-- P3
ConvexOn ℝ Set.univ Q ∧
∀ x ∈ segment ℝ (0 : EuclideanSpace ℝ (Fin 2)) (PiLp.single 2 1 1),
  ¬ DifferentiableAt ℝ Q x
```

EuclideanSpace real Fin2 is the actual L2-normed two-dimensional real space. First coordinate has Lean index0, second index1. PiLp.single2 index1 1 is (0,1). segment is CLOSED: {z | existsa,b:real,0<=a and0<=b anda+b=1 anda*x+b*y=z}. DifferentiableAt real is AMBIENT Frechet differentiability on real2, not DifferentiableWithinAt and not differentiability of Q restricted to that segment. P2 quantifies all second coordinates with no interval premise. Q is everywhere actual real-valued, no EReal.toReal. No stochastic/algorithm/feedback/regret claim. Do not infer a source or source completion.

Actual target-proposition/definition elaboration output (neutral names):
```text
ConvexOn ℝ Set.univ Q : Prop
∀ (x : EuclideanSpace ℝ (Fin 2)), x.ofLp 0 = 0 → ¬DifferentiableAt ℝ Q x : Prop
ConvexOn ℝ Set.univ Q ∧
  ∀ x ∈ segment ℝ 0 (PiLp.single 2 1 1), ¬DifferentiableAt ℝ Q x : Prop
def Q : EuclideanSpace ℝ (Fin 2) → ℝ :=
fun x => |x.ofLp 0|

```
