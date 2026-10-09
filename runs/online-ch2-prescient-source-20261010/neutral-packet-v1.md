# Neutral statement reconstruction packet

Reconstruct exactly the six statements below across seven semantic slots. Definitions, exact typed headers, and required scoped contexts only; no source attribution or theorem proof bodies. Imports supply canonical definitions. Do not seek source identities or prior review verdicts. Disclose related conversation history limits; this is source-withheld staged reconstruction, not absolute blindness. Requested actor effort medium.

## Canonical definitions (verbatim declarations, comments excluded)

```lean
def effectiveDomain (f : E → EReal) : Set E := {x | f x < ⊤}
```

```lean
def extendedIndicator (V : Set E) (x : E) : EReal := by
  classical
  exact if x ∈ V then 0 else ⊤
```

```lean
def SourceClosed (f : E → EReal) : Prop :=
  ∀ r : ℝ, IsClosed {x | f x ≤ (r : EReal)}
```

```lean
def SourceProper (f : E → EReal) : Prop :=
  (∀ x, f x ≠ ⊥) ∧ ∃ x, ∃ r : ℝ, f x = (r : EReal)
```

```lean
def SourceSubdifferential (f : E → EReal) (x : E) : Set E :=
  {g | ∀ y, f x + (inner ℝ g (y - x) : EReal) ≤ f y}
```

```lean
def divergence (ψ : E → ℝ) (x y : E) : ℝ :=
  ψ x - ψ y - fderiv ℝ ψ y (x - y)
```

```lean
def advance (V : Set E) (ψ : E → ℝ) (η : ℝ) (f : E → EReal) (x : E) : Option E := by
  classical
  exact if h : ∃ p, p ∈ V ∧
      IsMinOn (fun z => f z + ((η⁻¹ * divergence ψ z x : ℝ) : EReal)) V p
    then some (Classical.choose h) else none
```

```lean
def iterate (V : Set E) (ψ : E → ℝ) (η : ℕ → ℝ)
    (loss : ℕ → E → EReal) (x0 : E) : ℕ → Option E
  | 0 => some x0
  | t + 1 => (iterate V ψ η loss x0 t).bind (advance V ψ (η t) (loss t))
```

## Imports and exact scoped headers

```lean
import BanditRLProof.OnlinePrescientBregmanRegret
noncomputable section
open Set Finset
open BanditRL.OnlineBregman
```

```lean
namespace BanditRL.OnlineConvex
variable {E : Type*}
theorem sourceProper_of_domain (f : E → EReal) (V : Set E)
    (hV : V.Nonempty) (hbot : ∀ z, f z ≠ ⊥)
    (hdom : V ⊆ effectiveDomain f) :
    SourceProper f
end
```

```lean
namespace BanditRL.OnlinePrescientBregman
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
theorem penalized_strictConvex (V X : Set E) (hV : Convex ℝ V) (hVX : V ⊆ X)
    (ψ : E → ℝ) (hψ : StrictConvexOn ℝ X ψ)
    (f : E → EReal) (hf : BanditRL.OnlineConvex.SourceProper f)
    (hs : ∀ z ∈ V, (BanditRL.OnlineConvex.SourceSubdifferential f z).Nonempty)
    (η : ℝ) (hη : 0 < η) (x : E) :
    StrictConvexOn ℝ V (fun z => (f z).toReal + η⁻¹ * divergence ψ z x)
end
```

```lean
namespace BanditRL.OnlinePrescientBregman
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
theorem advance_eq_some_of_minimizer (V X : Set E) (hV : Convex ℝ V)
    (hVX : V ⊆ X) (ψ : E → ℝ) (hψ : StrictConvexOn ℝ X ψ)
    (f : E → EReal) (hf : BanditRL.OnlineConvex.SourceProper f)
    (hs : ∀ z ∈ V, (BanditRL.OnlineConvex.SourceSubdifferential f z).Nonempty)
    (η : ℝ) (hη : 0 < η) (x p : E) (hp : p ∈ V)
    (hmin : IsMinOn (fun z => f z + ((η⁻¹ * divergence ψ z x : ℝ) : EReal)) V p) :
    advance V ψ η f x = some p
end
```

```lean
namespace BanditRL.OnlinePrescientBregman
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
theorem iterate_eq_of_source_updates (V X : Set E) (hV : Convex ℝ V)
    (hVX : V ⊆ X) (ψ : E → ℝ) (hψ : StrictConvexOn ℝ X ψ)
    (η : ℕ → ℝ) (loss : ℕ → E → EReal) (x0 : E) (x : ℕ → E) (T : ℕ)
    (hinit : x 0 = x0) (hη : ∀ t < T, 0 < η t)
    (hf : ∀ t < T, BanditRL.OnlineConvex.SourceProper (loss t))
    (hs : ∀ t < T, ∀ z ∈ V,
      (BanditRL.OnlineConvex.SourceSubdifferential (loss t) z).Nonempty)
    (hmin : ∀ t < T, x (t + 1) ∈ V ∧
      IsMinOn (fun z => loss t z + (((η t)⁻¹ * divergence ψ z (x t) : ℝ) : EReal))
        V (x (t + 1))) :
    ∀ t ≤ T, iterate V ψ η loss x0 t = some (x t)
end
```

```lean
namespace BanditRL.OnlinePrescientBregman
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
theorem source_fixed_regret (V X : Set E) (hV : Convex ℝ V)
    (hVn : V.Nonempty) (_hVc : IsClosed V) (hVX : V ⊆ X)
    (ψ : E → ℝ) (hψ : StrictConvexOn ℝ X ψ)
    (_hψc : BanditRL.OnlineConvex.SourceClosed (fun z =>
      (ψ z : EReal) + BanditRL.OnlineConvex.extendedIndicator X z))
    (hd : DifferentiableOn ℝ ψ (interior X))
    (η : ℝ) (hη : 0 < η) (loss : ℕ → E → EReal)
    (x0 : E) (x : ℕ → E) (T : ℕ) (hinit : x 0 = x0)
    (hinterior : ∀ t ≤ T, x t ∈ interior X)
    (hbot : ∀ t < T, ∀ z, loss t z ≠ ⊥)
    (hdom : ∀ t < T, V ⊆ BanditRL.OnlineConvex.effectiveDomain (loss t))
    (hs : ∀ t < T, ∀ z ∈ V,
      (BanditRL.OnlineConvex.SourceSubdifferential (loss t) z).Nonempty)
    (hmin : ∀ t < T, x (t + 1) ∈ V ∧
      IsMinOn (fun z => loss t z + ((η⁻¹ * divergence ψ z (x t) : ℝ) : EReal))
        V (x (t + 1))) (u : E) (hu : u ∈ V) :
    (∑ t ∈ range T, ((loss t (x (t + 1))).toReal - (loss t u).toReal)) ≤
      divergence ψ u x0 / η - (∑ t ∈ range T, divergence ψ (x (t + 1)) (x t)) / η
end
```

```lean
namespace BanditRL.OnlinePrescientBregman
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
theorem source_variable_regret (V X : Set E) (hV : Convex ℝ V)
    (hVn : V.Nonempty) (_hVc : IsClosed V) (hVX : V ⊆ X)
    (ψ : E → ℝ) (hψ : StrictConvexOn ℝ X ψ)
    (_hψc : BanditRL.OnlineConvex.SourceClosed (fun z =>
      (ψ z : EReal) + BanditRL.OnlineConvex.extendedIndicator X z))
    (hd : DifferentiableOn ℝ ψ (interior X))
    (η : ℕ → ℝ)
    (loss : ℕ → E → EReal) (x0 : E) (x : ℕ → E) (T : ℕ) (hT : 0 < T)
    (hη : ∀ t < T, 0 < η t)
    (hinit : x 0 = x0) (hinterior : ∀ t ≤ T, x t ∈ interior X)
    (hmono : ∀ t, t + 1 < T → η (t + 1) ≤ η t)
    (hbot : ∀ t < T, ∀ z, loss t z ≠ ⊥)
    (hdom : ∀ t < T, V ⊆ BanditRL.OnlineConvex.effectiveDomain (loss t))
    (hs : ∀ t < T, ∀ z ∈ V,
      (BanditRL.OnlineConvex.SourceSubdifferential (loss t) z).Nonempty)
    (hmin : ∀ t < T, x (t + 1) ∈ V ∧
      IsMinOn (fun z => loss t z + (((η t)⁻¹ * divergence ψ z (x t) : ℝ) : EReal))
        V (x (t + 1))) (u : E) (hu : u ∈ V) :
    (∑ t ∈ range T, ((loss t (x (t + 1))).toReal - (loss t u).toReal)) ≤
      ((range T).sup' (nonempty_range_iff.mpr (Nat.ne_of_gt hT))
        (fun t => divergence ψ u (x t))) / η (T - 1) -
      ∑ t ∈ range T, divergence ψ (x (t + 1)) (x t) / η t
end
```
