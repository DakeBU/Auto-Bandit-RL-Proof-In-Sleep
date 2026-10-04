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
