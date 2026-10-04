Decode only these definitions and 21 Prop declarations. Do not read source identity, proof, previous verdict or other runs. Reconstruct each of seven semantic slots. Carefully distinguish optional universal oracle law from played-trajectory feedback, same-run schedule, and information order. Header bodies intentionally absent; no proof/acceptance claim.

```lean
import BanditRLProof.OnlineSubgradientDescent
noncomputable section
open Set Finset BanditRL.OnlineConvex
namespace BanditRL.OnlineSubgradientPolicy
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
abbrev Domain := BanditRL.OnlineGradientDescent.Domain E
abbrev SupportPolicy := (t : ℕ) → (Fin t → E → EReal) → (Fin (t + 1) → E) → (E → EReal) → E
/-- Only finite past losses/outputs and the currently observed loss are inputs. -/
def history (V : Domain (E := E)) (η : ℕ → ℝ) (loss : ℕ → E → EReal)
    (x₁ : E) (p : SupportPolicy (E := E)) : (t : ℕ) → Fin (t + 1) → E :=
  Nat.rec (motive := fun t => Fin (t + 1) → E) (fun _ => x₁)
    (fun t h => Fin.snoc h
      (BanditRL.OnlineGradientDescent.project V
        (h (Fin.last t) - η t • p t (fun i => loss i.val) h (loss t))))
def output (V : Domain (E := E)) (η : ℕ → ℝ) (loss : ℕ → E → EReal)
    (x₁ : E) (p : SupportPolicy (E := E)) (t : ℕ) : E :=
  history V η loss x₁ p t (Fin.last t)
def selected (V : Domain (E := E)) (η : ℕ → ℝ) (loss : ℕ → E → EReal)
    (x₁ : E) (p : SupportPolicy (E := E)) (t : ℕ) : E :=
  p t (fun i => loss i.val) (history V η loss x₁ p t) (loss t)
def OracleLaw (V : Domain (E := E)) (p : SupportPolicy (E := E)) : Prop :=
  ∀ t past h f, BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V f →
    h (Fin.last t) ∈ V.carrier → p t past h f ∈ SourceSubdifferential f (h (Fin.last t))
def canonicalPolicy : SupportPolicy (E := E) := fun t _ h f =>
  BanditRL.OnlineSubgradientDescent.currentSubgradient f (h (Fin.last t))
/-- Legality is imposed only at the actual played points, not at off-path histories. -/
def LegalFeedback (V : Domain (E := E)) (η : ℕ → ℝ) (loss : ℕ → E → EReal)
    (x₁ : E) (p : SupportPolicy (E := E)) (T : ℕ) : Prop :=
  ∀ t < T, selected V η loss x₁ p t ∈ SourceSubdifferential (loss t) (output V η loss x₁ p t)
def regret (V : Domain (E := E)) (η : ℕ → ℝ) (loss : ℕ → E → EReal)
    (x₁ : E) (p : SupportPolicy (E := E)) (u : E) (T : ℕ) : ℝ :=
  ∑ t ∈ range T, ((loss t (output V η loss x₁ p t)).toReal - (loss t u).toReal)
theorem result_1 (V : Domain (E := E)) (η : ℕ → ℝ) (loss : ℕ → E → EReal)
    (x₁ : E) (p : SupportPolicy (E := E)) :
    history V η loss x₁ p 0 = fun _ => x₁

theorem result_2 (V : Domain (E := E)) (η : ℕ → ℝ) (loss : ℕ → E → EReal)
    (x₁ : E) (p : SupportPolicy (E := E)) (t : ℕ) :
    history V η loss x₁ p (t + 1) =
      Fin.snoc (history V η loss x₁ p t)
        (BanditRL.OnlineGradientDescent.project V
          (output V η loss x₁ p t - η t • selected V η loss x₁ p t))

theorem result_3 (V : Domain (E := E)) (η : ℕ → ℝ) (loss : ℕ → E → EReal)
    (x₁ : E) (p : SupportPolicy (E := E)) :
    output V η loss x₁ p 0 = x₁

theorem result_4 (V : Domain (E := E)) (η : ℕ → ℝ) (loss : ℕ → E → EReal)
    (x₁ : E) (p : SupportPolicy (E := E)) (t : ℕ) :
    output V η loss x₁ p (t + 1) =
      BanditRL.OnlineGradientDescent.project V
        (output V η loss x₁ p t - η t • selected V η loss x₁ p t)

theorem result_5 (V : Domain (E := E)) (η : ℕ → ℝ) (loss : ℕ → E → EReal)
    (x₁ : E) (p : SupportPolicy (E := E)) (hx₁ : x₁ ∈ V.carrier) (t : ℕ) (i : Fin (t + 1)) :
    history V η loss x₁ p t i ∈ V.carrier

theorem result_6 (V : Domain (E := E)) (η : ℕ → ℝ) (loss : ℕ → E → EReal)
    (x₁ : E) (p : SupportPolicy (E := E)) (hx₁ : x₁ ∈ V.carrier) (t : ℕ) :
    output V η loss x₁ p t ∈ V.carrier

theorem result_7 (V : Domain (E := E)) (η η' : ℕ → ℝ)
    (loss loss' : ℕ → E → EReal) (x₁ : E) (p : SupportPolicy (E := E)) (t : ℕ)
    (hη : ∀ s < t, η s = η' s) (hloss : ∀ s < t, loss s = loss' s) :
    history V η loss x₁ p t = history V η' loss' x₁ p t

theorem result_8 (V : Domain (E := E)) (η η' : ℕ → ℝ)
    (loss loss' : ℕ → E → EReal) (x₁ : E) (p : SupportPolicy (E := E)) (t : ℕ)
    (hη : ∀ s < t, η s = η' s) (hloss : ∀ s < t, loss s = loss' s) :
    output V η loss x₁ p t = output V η' loss' x₁ p t

theorem result_9 (V : Domain (E := E)) (η : ℕ → ℝ) (loss : ℕ → E → EReal)
    (x₁ : E) (p : SupportPolicy (E := E)) (hx₁ : x₁ ∈ V.carrier) (T : ℕ)
    (hp : OracleLaw V p)
    (hloss : ∀ t < T, BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V (loss t)) :
    LegalFeedback V η loss x₁ p T

theorem result_10 (V : Domain (E := E)) (η : ℕ → ℝ) (loss : ℕ → E → EReal)
    (x₁ : E) (p : SupportPolicy (E := E)) (hx₁ : x₁ ∈ V.carrier) (t : ℕ)
    (hloss : BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V (loss t))
    (u : E) (hu : u ∈ V.carrier) :
    loss t (output V η loss x₁ p t) = ((loss t (output V η loss x₁ p t)).toReal : EReal) ∧
    loss t u = ((loss t u).toReal : EReal)

theorem result_11 (V : Domain (E := E)) (η : ℕ → ℝ) (loss : ℕ → E → EReal)
    (x₁ : E) (p : SupportPolicy (E := E)) (t : ℕ) (hη : 0 < η t)
    (hloss : BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V (loss t))
    (hg : selected V η loss x₁ p t ∈ SourceSubdifferential (loss t) (output V η loss x₁ p t))
    (u : E) (hu : u ∈ V.carrier) :
    η t * ((loss t (output V η loss x₁ p t)).toReal - (loss t u).toReal) ≤
      η t * inner ℝ (selected V η loss x₁ p t) (output V η loss x₁ p t - u) ∧
    η t * inner ℝ (selected V η loss x₁ p t) (output V η loss x₁ p t - u) ≤
      ‖output V η loss x₁ p t - u‖ ^ 2 / 2 -
      ‖output V η loss x₁ p (t + 1) - u‖ ^ 2 / 2 +
      (η t) ^ 2 / 2 * ‖selected V η loss x₁ p t‖ ^ 2

theorem result_12 (V : Domain (E := E)) (η : ℕ → ℝ) (loss : ℕ → E → EReal)
    (x₁ : E) (p : SupportPolicy (E := E)) (t : ℕ) (hη : 0 < η t)
    (hloss : BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V (loss t))
    (hg : selected V η loss x₁ p t ∈ SourceSubdifferential (loss t) (output V η loss x₁ p t))
    (u : E) (hu : u ∈ V.carrier) :
    (loss t (output V η loss x₁ p t)).toReal - (loss t u).toReal ≤
      (‖output V η loss x₁ p t - u‖ ^ 2 -
        ‖output V η loss x₁ p (t + 1) - u‖ ^ 2) / (2 * η t) +
      η t / 2 * ‖selected V η loss x₁ p t‖ ^ 2

theorem result_13 (V : Domain (E := E)) (η : ℝ) (hη : 0 < η)
    (loss : ℕ → E → EReal) (x₁ : E) (p : SupportPolicy (E := E))
    (hx₁ : x₁ ∈ V.carrier) (T : ℕ)
    (hloss : ∀ t < T, BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V (loss t))
    (hlegal : LegalFeedback V (fun _ => η) loss x₁ p T) (u : E) (hu : u ∈ V.carrier) :
    regret V (fun _ => η) loss x₁ p u T ≤ ‖x₁ - u‖ ^ 2 / (2 * η) +
      η / 2 * (∑ t ∈ range T, ‖selected V (fun _ => η) loss x₁ p t‖ ^ 2) -
      ‖output V (fun _ => η) loss x₁ p T - u‖ ^ 2 / (2 * η)

theorem result_14 (V : Domain (E := E)) (η : ℝ) (hη : 0 < η)
    (loss : ℕ → E → EReal) (x₁ : E) (p : SupportPolicy (E := E))
    (hx₁ : x₁ ∈ V.carrier) (T : ℕ)
    (hloss : ∀ t < T, BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V (loss t))
    (hlegal : LegalFeedback V (fun _ => η) loss x₁ p T) (u : E) (hu : u ∈ V.carrier) :
    regret V (fun _ => η) loss x₁ p u T ≤ ‖x₁ - u‖ ^ 2 / (2 * η) +
      η / 2 * (∑ t ∈ range T, ‖selected V (fun _ => η) loss x₁ p t‖ ^ 2)

theorem result_15 (V : Domain (E := E)) (η : ℕ → ℝ) (loss : ℕ → E → EReal)
    (x₁ : E) (p : SupportPolicy (E := E)) (hx₁ : x₁ ∈ V.carrier) (T : ℕ) (hT : 0 < T)
    (hη : ∀ t < T, 0 < η t) (hmono : ∀ t, t + 1 < T → η (t + 1) ≤ η t)
    (hloss : ∀ t < T, BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V (loss t))
    (hlegal : LegalFeedback V η loss x₁ p T) (D : ℝ)
    (hdiam : ∀ x ∈ V.carrier, ∀ y ∈ V.carrier, ‖x - y‖ ≤ D)
    (u : E) (hu : u ∈ V.carrier) :
    regret V η loss x₁ p u T ≤ D ^ 2 / (2 * η (T - 1)) +
      (∑ t ∈ range T, η t / 2 * ‖selected V η loss x₁ p t‖ ^ 2) -
      ‖output V η loss x₁ p T - u‖ ^ 2 / (2 * η (T - 1))

theorem result_16 (V : Domain (E := E)) (η : ℕ → ℝ) (loss : ℕ → E → EReal)
    (x₁ : E) (p : SupportPolicy (E := E)) (hx₁ : x₁ ∈ V.carrier) (T : ℕ) (hT : 0 < T)
    (hη : ∀ t < T, 0 < η t) (hmono : ∀ t, t + 1 < T → η (t + 1) ≤ η t)
    (hloss : ∀ t < T, BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V (loss t))
    (hlegal : LegalFeedback V η loss x₁ p T) (hV : Bornology.IsBounded V.carrier) (u : E) (hu : u ∈ V.carrier) :
    regret V η loss x₁ p u T ≤ (Metric.diam V.carrier) ^ 2 / (2 * η (T - 1)) +
      (∑ t ∈ range T, η t / 2 * ‖selected V η loss x₁ p t‖ ^ 2) -
      ‖output V η loss x₁ p T - u‖ ^ 2 / (2 * η (T - 1))

theorem result_17 (V : Domain (E := E)) (loss : ℕ → E → EReal)
    (x₁ : E) (p : SupportPolicy (E := E)) (hx₁ : x₁ ∈ V.carrier)
    (T : ℕ) (hT : 0 < T) (D G : ℝ) (hD : 0 < D) (hG : 0 < G)
    (hloss : ∀ t < T, BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V (loss t))
    (hlegal : LegalFeedback V (fun _ => D / (G * Real.sqrt T)) loss x₁ p T) (u : E) (hu : u ∈ V.carrier)
    (hdist : ‖x₁ - u‖ ≤ D)
    (hgrad : ∀ t < T, ‖selected V (fun _ => D / (G * Real.sqrt T)) loss x₁ p t‖ ≤ G) :
    regret V (fun _ => D / (G * Real.sqrt T)) loss x₁ p u T ≤ D * G * Real.sqrt T

theorem result_18 (V : Domain (E := E)) (loss : ℕ → E → EReal)
    (x₁ : E) (p : SupportPolicy (E := E)) (hx₁ : x₁ ∈ V.carrier)
    (T : ℕ) (hT : 0 < T) (D G : ℝ) (hD : 0 < D) (hG : 0 < G)
    (hloss : ∀ t < T, BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V (loss t))
    (hlegal : LegalFeedback V (fun _ => D / (G * Real.sqrt T)) loss x₁ p T)
    (hdiam : ∀ x ∈ V.carrier, ∀ y ∈ V.carrier, ‖x - y‖ ≤ D)
    (hgrad : ∀ t < T, ‖selected V (fun _ => D / (G * Real.sqrt T)) loss x₁ p t‖ ≤ G) :
    ∀ u ∈ V.carrier,
      regret V (fun _ => D / (G * Real.sqrt T)) loss x₁ p u T ≤ D * G * Real.sqrt T

theorem result_19 (V : Domain (E := E)) :
    OracleLaw V (canonicalPolicy (E := E))

theorem result_20 (V : Domain (E := E)) (η : ℕ → ℝ) (loss : ℕ → E → EReal)
    (x₁ : E) (t : ℕ) :
    output V η loss x₁ canonicalPolicy t =
      BanditRL.OnlineSubgradientDescent.iterate V η loss x₁ t

theorem result_21 (V : Domain (E := E)) (η : ℕ → ℝ) (loss : ℕ → E → EReal)
    (x₁ : E) (t : ℕ) :
    selected V η loss x₁ canonicalPolicy t =
      BanditRL.OnlineSubgradientDescent.currentSubgradient (loss t)
        (BanditRL.OnlineSubgradientDescent.iterate V η loss x₁ t)
end BanditRL.OnlineSubgradientPolicy
```


Imported mathematical context supplement. Definitions have exact declaration boundaries; only two existing theorem HEADERS are provided, without any theorem body. Target21headers and scopedcontext unchanged. EReal.toReal maps both infinities to zero; finite-value production is required. Metric boundedness-to-finite-ediam equivalence is explicit. No source identity, prior verdict, target proof or upstream theorem proof.

Imported exact structure Domain (local scoped variables as in module; theorem proof omitted):
```lean
structure Domain (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  carrier : Set E
  nonempty : carrier.Nonempty
  closed : IsClosed carrier
  convex : Convex ℝ carrier
```

Imported exact def project (local scoped variables as in module; theorem proof omitted):
```lean
def project (V : Domain E) (z : E) : E :=
  Classical.choose (exists_norm_eq_iInf_of_complete_convex V.nonempty
    V.closed.isComplete V.convex z)
```

Imported exact theorem project_spec (local scoped variables as in module; theorem proof omitted):
```lean
theorem project_spec (V : Domain E) (z : E) :
    project V z ∈ V.carrier ∧ ‖z - project V z‖ = ⨅ w : V.carrier, ‖z - w‖
```

Imported exact def SourceProper (local scoped variables as in module; theorem proof omitted):
```lean
def SourceProper (f : E → EReal) : Prop :=
  (∀ x, f x ≠ ⊥) ∧ ∃ x, ∃ r : ℝ, f x = (r : EReal)
```

Imported exact def SourceSubdifferential (local scoped variables as in module; theorem proof omitted):
```lean
def SourceSubdifferential (f : E → EReal) (x : E) : Set E :=
  {g | ∀ y, f x + (inner ℝ g (y - x) : EReal) ≤ f y}
```

Imported exact def SubdifferentiableOn (local scoped variables as in module; theorem proof omitted):
```lean
def SubdifferentiableOn (V : Domain (E := E)) (f : E → EReal) : Prop :=
  SourceProper f ∧ ∀ x ∈ V.carrier, (SourceSubdifferential f x).Nonempty
```

Imported exact def currentSubgradient (local scoped variables as in module; theorem proof omitted):
```lean
def currentSubgradient (f : E → EReal) (x : E) : E :=
  by
    classical
    exact if h : (SourceSubdifferential f x).Nonempty then Classical.choose h else 0
```

Imported exact def step (local scoped variables as in module; theorem proof omitted):
```lean
def step (V : Domain (E := E)) (η : ℝ) (f : E → EReal) (x : E) : E :=
  BanditRL.OnlineGradientDescent.project V (x - η • currentSubgradient f x)
```

Imported exact def iterate (local scoped variables as in module; theorem proof omitted):
```lean
def iterate (V : Domain (E := E)) (η : ℕ → ℝ) (loss : ℕ → E → EReal) (x₁ : E) : ℕ → E
  | 0 => x₁
  | t + 1 => step V (η t) (loss t) (iterate V η loss x₁ t)
```

Imported exact def toReal (local scoped variables as in module; theorem proof omitted):
```lean
def toReal : EReal → ℝ
  | ⊥ => 0
  | ⊤ => 0
  | (x : ℝ) => x

@[simp]
```

Imported exact def ediam (local scoped variables as in module; theorem proof omitted):
```lean
noncomputable def ediam (s : Set X) :=
  ⨆ (x ∈ s) (y ∈ s), edist x y
```

Imported exact def diam (local scoped variables as in module; theorem proof omitted):
```lean
noncomputable def diam (s : Set α) : ℝ :=
  ENNReal.toReal (ediam s)
```

Imported exact theorem isBounded_iff_ediam_ne_top (local scoped variables as in module; theorem proof omitted):
```lean
theorem isBounded_iff_ediam_ne_top : IsBounded s ↔ ediam s ≠ ⊤
```
