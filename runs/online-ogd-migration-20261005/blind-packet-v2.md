Fresh restricted pass: read only this packet. Reconstruct twelve unproved headers M01-M12 in seven semantic slots, with all quantifiers, regularity, conclusion/constants/indexing/information order and excluded regimes. No source/provenance/name map/proofs/logs/reviews. No acceptance claim.

Scoped context:
```lean
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic



noncomputable section
open Set Finset
open scoped InnerProductSpace

namespace NeutralRepair

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]


structure Q0 (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  carrier : Set E
  nonempty : carrier.Nonempty
  closed : IsClosed carrier
  convex : Convex ℝ carrier


def Q1 (V : Q0 E) (z : E) : E :=
  Classical.choose (exists_norm_eq_iInf_of_complete_convex V.nonempty
    V.closed.isComplete V.convex z)


def Q2 (V : Q0 E) (f : E → ℝ) : Prop :=
  ∃ U : Set E, IsOpen U ∧ V.carrier ⊆ U ∧ ConvexOn ℝ U f ∧ DifferentiableOn ℝ f U


def Q3 (V : Q0 E) (η : ℝ) (f : E → ℝ) (x : E) : E :=
  Q1 V (x - η • gradient f x)


def Q4 (V : Q0 E) (η : ℝ) (loss : ℕ → E → ℝ) (x₁ : E) : ℕ → E
  | 0 => x₁
  | t + 1 => Q3 V η (loss t) (Q4 V η loss x₁ t)


def Q5 (V : Q0 E) (η : ℝ) (loss : ℕ → E → ℝ) (x₁ u : E) (T : ℕ) : ℝ :=
  ∑ t ∈ range T, (loss t (Q4 V η loss x₁ t) - loss t u)



def Q6 (V : Q0 E) (η : ℕ → ℝ) (loss : ℕ → E → ℝ) (x₁ : E) : ℕ → E
  | 0 => x₁
  | t + 1 => Q3 V (η t) (loss t) (Q6 V η loss x₁ t)


def Q7 (V : Q0 E) (η : ℕ → ℝ) (loss : ℕ → E → ℝ)
    (x₁ u : E) (T : ℕ) : ℝ :=
  ∑ t ∈ range T, (loss t (Q6 V η loss x₁ t) - loss t u)



def Q8 (V : Q0 E) (f : E → ℝ) : Prop :=
  ConvexOn ℝ V.carrier f ∧ ∀ x ∈ V.carrier, DifferentiableAt ℝ f x

def Q9 (V : Q0 E) (f : E → ℝ) : Prop :=
  ∃ U : Set E, IsOpen U ∧ V.carrier ⊆ U ∧
    ConvexOn ℝ V.carrier f ∧ DifferentiableOn ℝ f U

```

Unproved headers:
```lean
theorem M01 (V : Q0 E) (f : E → ℝ) (hf : Q9 V f) : Q8 V f

theorem M02 (V : Q0 E) (f : E → ℝ) (hf : Q2 V f) : Q8 V f

theorem M03 (V : Q0 E) (g : E) : Q2 V (fun z => inner ℝ g z)

theorem M04 (g x : E) : gradient (fun z => inner ℝ g z) x = g

theorem M05 (V : Q0 E) (f : E → ℝ) (hf : Q8 V f) (x u : E) (hx : x ∈ V.carrier) (hu : u ∈ V.carrier) : f x - f u ≤ inner ℝ (gradient f x) (x - u)

theorem M06 (V : Q0 E) (f : E → ℝ) (hf : Q8 V f) (η : ℝ) (hη : 0 < η) (x u : E) (hx : x ∈ V.carrier) (hu : u ∈ V.carrier) : η * (f x - f u) ≤ η * inner ℝ (gradient f x) (x - u) ∧ η * inner ℝ (gradient f x) (x - u) ≤ ‖x - u‖ ^ 2 / 2 - ‖Q3 V η f x - u‖ ^ 2 / 2 + η ^ 2 / 2 * ‖gradient f x‖ ^ 2

theorem M07 (V : Q0 E) (η : ℝ) (hη : 0 < η) (loss : ℕ → E → ℝ) (x₁ : E) (hx₁ : x₁ ∈ V.carrier) (T : ℕ) (hloss : ∀ t < T, Q8 V (loss t)) (u : E) (hu : u ∈ V.carrier) : Q5 V η loss x₁ u T ≤ ‖x₁ - u‖ ^ 2 / (2 * η) + η / 2 * (∑ t ∈ range T, ‖gradient (loss t) (Q4 V η loss x₁ t)‖ ^ 2) - ‖Q4 V η loss x₁ T - u‖ ^ 2 / (2 * η)

theorem M08 (V : Q0 E) (η : ℕ → ℝ) (loss : ℕ → E → ℝ) (x₁ : E) (hx₁ : x₁ ∈ V.carrier) (t : ℕ) (hη : 0 < η t) (hloss : Q8 V (loss t)) (u : E) (hu : u ∈ V.carrier) : loss t (Q6 V η loss x₁ t) - loss t u ≤ (‖Q6 V η loss x₁ t - u‖ ^ 2 - ‖Q6 V η loss x₁ (t + 1) - u‖ ^ 2) / (2 * η t) + η t / 2 * ‖gradient (loss t) (Q6 V η loss x₁ t)‖ ^ 2

theorem M09 (V : Q0 E) (η : ℕ → ℝ) (loss : ℕ → E → ℝ) (x₁ : E) (hx₁ : x₁ ∈ V.carrier) (T : ℕ) (hT : 0 < T) (hη : ∀ t < T, 0 < η t) (hmono : ∀ t, t + 1 < T → η (t + 1) ≤ η t) (hloss : ∀ t < T, Q8 V (loss t)) (D : ℝ) (hdiam : ∀ x ∈ V.carrier, ∀ y ∈ V.carrier, ‖x - y‖ ≤ D) (u : E) (hu : u ∈ V.carrier) : Q7 V η loss x₁ u T ≤ D ^ 2 / (2 * η (T - 1)) + (∑ t ∈ range T, η t / 2 * ‖gradient (loss t) (Q6 V η loss x₁ t)‖ ^ 2) - ‖Q6 V η loss x₁ T - u‖ ^ 2 / (2 * η (T - 1))

theorem M10 (V : Q0 E) (hV : Bornology.IsBounded V.carrier) (η : ℕ → ℝ) (loss : ℕ → E → ℝ) (x₁ : E) (hx₁ : x₁ ∈ V.carrier) (T : ℕ) (hT : 0 < T) (hη : ∀ t < T, 0 < η t) (hmono : ∀ t, t + 1 < T → η (t + 1) ≤ η t) (hloss : ∀ t < T, Q8 V (loss t)) (u : E) (hu : u ∈ V.carrier) : Q7 V η loss x₁ u T ≤ (Metric.diam V.carrier) ^ 2 / (2 * η (T - 1)) + (∑ t ∈ range T, η t / 2 * ‖gradient (loss t) (Q6 V η loss x₁ t)‖ ^ 2) - ‖Q6 V η loss x₁ T - u‖ ^ 2 / (2 * η (T - 1))

theorem M11 (V : Q0 E) (loss : ℕ → E → ℝ) (x₁ : E) (hx₁ : x₁ ∈ V.carrier) (T : ℕ) (hT : 0 < T) (D G : ℝ) (hD : 0 < D) (hG : 0 < G) (hloss : ∀ t < T, Q8 V (loss t)) (u : E) (hu : u ∈ V.carrier) (hdist : ‖x₁ - u‖ ≤ D) (hgrad : ∀ t < T, ‖gradient (loss t) (Q4 V (D / (G * Real.sqrt T)) loss x₁ t)‖ ≤ G) : Q5 V (D / (G * Real.sqrt T)) loss x₁ u T ≤ D * G * Real.sqrt T

theorem M12 (V : Q0 E) (loss : ℕ → E → ℝ) (x₁ : E) (hx₁ : x₁ ∈ V.carrier) (T : ℕ) (hT : 0 < T) (D G : ℝ) (hD : 0 < D) (hG : 0 < G) (hdiam : ∀ x ∈ V.carrier, ∀ y ∈ V.carrier, ‖x - y‖ ≤ D) (hloss : ∀ t < T, Q8 V (loss t)) (hgrad : ∀ t < T, ‖gradient (loss t) (Q4 V (D / (G * Real.sqrt T)) loss x₁ t)‖ ≤ G) : ∀ u ∈ V.carrier, Q5 V (D / (G * Real.sqrt T)) loss x₁ u T ≤ D * G * Real.sqrt T
end NeutralRepair
```
