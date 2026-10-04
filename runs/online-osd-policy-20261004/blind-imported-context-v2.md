Imported mathematical context supplement. No targetheader/contextdefinition changed. This text provides existing definitions and one alreadyavailable projection specification for interpretation, not source citation or proof of the 21 proposed targets. EReal has two infinite endpoints; toReal maps them to zero, so a properness/finite-value producer matters. Metric boundedness equivalence with finite ediam is supplied explicitly.

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
/-- Current function/point only; no comparator, horizon or future losses. -/
def currentSubgradient (f : E → EReal) (x : E) : E :=
  by
    classical
    exact if h : (SourceSubdifferential f x).Nonempty then Classical.choose h else 0
def step (V : Domain (E := E)) (η : ℝ) (f : E → EReal) (x : E) : E :=
  BanditRL.OnlineGradientDescent.project V (x - η • currentSubgradient f x)
def iterate (V : Domain (E := E)) (η : ℕ → ℝ) (loss : ℕ → E → EReal) (x₁ : E) : ℕ → E
  | 0 => x₁
  | t + 1 => step V (η t) (loss t) (iterate V η loss x₁ t)
def regret (V : Domain (E := E)) (η : ℕ → ℝ) (loss : ℕ → E → EReal) (x₁ u : E) (T : ℕ) : ℝ :=
  ∑ t ∈ range T, ((loss t (iterate V η loss x₁ t)).toReal - (loss t u).toReal)
theorem lemma_2_31 (V : Domain (E := E)) (f : E → EReal) (hf : SubdifferentiableOn V f)
    (η : ℝ) (hη : 0 < η) (x u : E) (hu : u ∈ V.carrier)
    (g : E) (hg : g ∈ SourceSubdifferential f x) :
    η * ((f x).toReal - (f u).toReal) ≤ η * inner ℝ g (x - u) ∧
    η * inner ℝ g (x - u) ≤
      ‖x - u‖ ^ 2 / 2 -
      ‖BanditRL.OnlineGradientDescent.project V (x - η • g) - u‖ ^ 2 / 2 +
      η ^ 2 / 2 * ‖g‖ ^ 2 := by
  have hxdom : x ∈ effectiveDomain f := subgradient_point_finite f hf.1 x g hg
  obtain ⟨gu, hgu⟩ := hf.2 u hu
  have hudom : u ∈ effectiveDomain f := subgradient_point_finite f hf.1 u gu hgu
  have hxv := EReal.coe_toReal (ne_of_lt hxdom) (hf.1.1 x)
  have huv := EReal.coe_toReal (ne_of_lt hudom) (hf.1.1 u)
  have hsupport := hg u
  rw [← hxv, ← huv, ← EReal.coe_add] at hsupport
  have hsupportR := EReal.coe_le_coe_iff.mp hsupport
  rw [show u - x = -(x - u) by abel, inner_neg_right] at hsupportR
  have hgap : (f x).toReal - (f u).toReal ≤ inner ℝ g (x - u) := by linarith
  refine ⟨mul_le_mul_of_nonneg_left hgap hη.le, ?_⟩
  have hp := BanditRL.OnlineGradientDescent.proposition_2_11 V (x - η • g) u hu
  have he : ‖x - η • g - u‖ ^ 2 = ‖x - u‖ ^ 2 -
      2 * η * inner ℝ g (x - u) + η ^ 2 * ‖g‖ ^ 2 := by
    rw [show x - η • g - u = (x - u) - η • g by abel,
      norm_sub_sq_real, inner_smul_right, real_inner_comm (x - u), norm_smul,
      Real.norm_eq_abs, abs_of_pos hη]
    ring
  have hs : ‖BanditRL.OnlineGradientDescent.project V (x - η • g) - u‖ ^ 2 ≤
      ‖x - η • g - u‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hp 2
  nlinarith
```

Imported exact def currentSubgradient (local scoped variables as in module; theorem proof omitted):
```lean
def currentSubgradient (f : E → EReal) (x : E) : E :=
  by
    classical
    exact if h : (SourceSubdifferential f x).Nonempty then Classical.choose h else 0
def step (V : Domain (E := E)) (η : ℝ) (f : E → EReal) (x : E) : E :=
  BanditRL.OnlineGradientDescent.project V (x - η • currentSubgradient f x)
def iterate (V : Domain (E := E)) (η : ℕ → ℝ) (loss : ℕ → E → EReal) (x₁ : E) : ℕ → E
  | 0 => x₁
  | t + 1 => step V (η t) (loss t) (iterate V η loss x₁ t)
def regret (V : Domain (E := E)) (η : ℕ → ℝ) (loss : ℕ → E → EReal) (x₁ u : E) (T : ℕ) : ℝ :=
  ∑ t ∈ range T, ((loss t (iterate V η loss x₁ t)).toReal - (loss t u).toReal)
theorem lemma_2_31 (V : Domain (E := E)) (f : E → EReal) (hf : SubdifferentiableOn V f)
    (η : ℝ) (hη : 0 < η) (x u : E) (hu : u ∈ V.carrier)
    (g : E) (hg : g ∈ SourceSubdifferential f x) :
    η * ((f x).toReal - (f u).toReal) ≤ η * inner ℝ g (x - u) ∧
    η * inner ℝ g (x - u) ≤
      ‖x - u‖ ^ 2 / 2 -
      ‖BanditRL.OnlineGradientDescent.project V (x - η • g) - u‖ ^ 2 / 2 +
      η ^ 2 / 2 * ‖g‖ ^ 2 := by
  have hxdom : x ∈ effectiveDomain f := subgradient_point_finite f hf.1 x g hg
  obtain ⟨gu, hgu⟩ := hf.2 u hu
  have hudom : u ∈ effectiveDomain f := subgradient_point_finite f hf.1 u gu hgu
  have hxv := EReal.coe_toReal (ne_of_lt hxdom) (hf.1.1 x)
  have huv := EReal.coe_toReal (ne_of_lt hudom) (hf.1.1 u)
  have hsupport := hg u
  rw [← hxv, ← huv, ← EReal.coe_add] at hsupport
  have hsupportR := EReal.coe_le_coe_iff.mp hsupport
  rw [show u - x = -(x - u) by abel, inner_neg_right] at hsupportR
  have hgap : (f x).toReal - (f u).toReal ≤ inner ℝ g (x - u) := by linarith
  refine ⟨mul_le_mul_of_nonneg_left hgap hη.le, ?_⟩
  have hp := BanditRL.OnlineGradientDescent.proposition_2_11 V (x - η • g) u hu
  have he : ‖x - η • g - u‖ ^ 2 = ‖x - u‖ ^ 2 -
      2 * η * inner ℝ g (x - u) + η ^ 2 * ‖g‖ ^ 2 := by
    rw [show x - η • g - u = (x - u) - η • g by abel,
      norm_sub_sq_real, inner_smul_right, real_inner_comm (x - u), norm_smul,
      Real.norm_eq_abs, abs_of_pos hη]
    ring
  have hs : ‖BanditRL.OnlineGradientDescent.project V (x - η • g) - u‖ ^ 2 ≤
      ‖x - η • g - u‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hp 2
  nlinarith
```

Imported exact def step (local scoped variables as in module; theorem proof omitted):
```lean
def step (V : Domain (E := E)) (η : ℝ) (f : E → EReal) (x : E) : E :=
  BanditRL.OnlineGradientDescent.project V (x - η • currentSubgradient f x)
def iterate (V : Domain (E := E)) (η : ℕ → ℝ) (loss : ℕ → E → EReal) (x₁ : E) : ℕ → E
  | 0 => x₁
  | t + 1 => step V (η t) (loss t) (iterate V η loss x₁ t)
def regret (V : Domain (E := E)) (η : ℕ → ℝ) (loss : ℕ → E → EReal) (x₁ u : E) (T : ℕ) : ℝ :=
  ∑ t ∈ range T, ((loss t (iterate V η loss x₁ t)).toReal - (loss t u).toReal)
theorem lemma_2_31 (V : Domain (E := E)) (f : E → EReal) (hf : SubdifferentiableOn V f)
    (η : ℝ) (hη : 0 < η) (x u : E) (hu : u ∈ V.carrier)
    (g : E) (hg : g ∈ SourceSubdifferential f x) :
    η * ((f x).toReal - (f u).toReal) ≤ η * inner ℝ g (x - u) ∧
    η * inner ℝ g (x - u) ≤
      ‖x - u‖ ^ 2 / 2 -
      ‖BanditRL.OnlineGradientDescent.project V (x - η • g) - u‖ ^ 2 / 2 +
      η ^ 2 / 2 * ‖g‖ ^ 2 := by
  have hxdom : x ∈ effectiveDomain f := subgradient_point_finite f hf.1 x g hg
  obtain ⟨gu, hgu⟩ := hf.2 u hu
  have hudom : u ∈ effectiveDomain f := subgradient_point_finite f hf.1 u gu hgu
  have hxv := EReal.coe_toReal (ne_of_lt hxdom) (hf.1.1 x)
  have huv := EReal.coe_toReal (ne_of_lt hudom) (hf.1.1 u)
  have hsupport := hg u
  rw [← hxv, ← huv, ← EReal.coe_add] at hsupport
  have hsupportR := EReal.coe_le_coe_iff.mp hsupport
  rw [show u - x = -(x - u) by abel, inner_neg_right] at hsupportR
  have hgap : (f x).toReal - (f u).toReal ≤ inner ℝ g (x - u) := by linarith
  refine ⟨mul_le_mul_of_nonneg_left hgap hη.le, ?_⟩
  have hp := BanditRL.OnlineGradientDescent.proposition_2_11 V (x - η • g) u hu
  have he : ‖x - η • g - u‖ ^ 2 = ‖x - u‖ ^ 2 -
      2 * η * inner ℝ g (x - u) + η ^ 2 * ‖g‖ ^ 2 := by
    rw [show x - η • g - u = (x - u) - η • g by abel,
      norm_sub_sq_real, inner_smul_right, real_inner_comm (x - u), norm_smul,
      Real.norm_eq_abs, abs_of_pos hη]
    ring
  have hs : ‖BanditRL.OnlineGradientDescent.project V (x - η • g) - u‖ ^ 2 ≤
      ‖x - η • g - u‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hp 2
  nlinarith
```

Imported exact def iterate (local scoped variables as in module; theorem proof omitted):
```lean
def iterate (V : Domain (E := E)) (η : ℕ → ℝ) (loss : ℕ → E → EReal) (x₁ : E) : ℕ → E
  | 0 => x₁
  | t + 1 => step V (η t) (loss t) (iterate V η loss x₁ t)
def regret (V : Domain (E := E)) (η : ℕ → ℝ) (loss : ℕ → E → EReal) (x₁ u : E) (T : ℕ) : ℝ :=
  ∑ t ∈ range T, ((loss t (iterate V η loss x₁ t)).toReal - (loss t u).toReal)
theorem lemma_2_31 (V : Domain (E := E)) (f : E → EReal) (hf : SubdifferentiableOn V f)
    (η : ℝ) (hη : 0 < η) (x u : E) (hu : u ∈ V.carrier)
    (g : E) (hg : g ∈ SourceSubdifferential f x) :
    η * ((f x).toReal - (f u).toReal) ≤ η * inner ℝ g (x - u) ∧
    η * inner ℝ g (x - u) ≤
      ‖x - u‖ ^ 2 / 2 -
      ‖BanditRL.OnlineGradientDescent.project V (x - η • g) - u‖ ^ 2 / 2 +
      η ^ 2 / 2 * ‖g‖ ^ 2 := by
  have hxdom : x ∈ effectiveDomain f := subgradient_point_finite f hf.1 x g hg
  obtain ⟨gu, hgu⟩ := hf.2 u hu
  have hudom : u ∈ effectiveDomain f := subgradient_point_finite f hf.1 u gu hgu
  have hxv := EReal.coe_toReal (ne_of_lt hxdom) (hf.1.1 x)
  have huv := EReal.coe_toReal (ne_of_lt hudom) (hf.1.1 u)
  have hsupport := hg u
  rw [← hxv, ← huv, ← EReal.coe_add] at hsupport
  have hsupportR := EReal.coe_le_coe_iff.mp hsupport
  rw [show u - x = -(x - u) by abel, inner_neg_right] at hsupportR
  have hgap : (f x).toReal - (f u).toReal ≤ inner ℝ g (x - u) := by linarith
  refine ⟨mul_le_mul_of_nonneg_left hgap hη.le, ?_⟩
  have hp := BanditRL.OnlineGradientDescent.proposition_2_11 V (x - η • g) u hu
  have he : ‖x - η • g - u‖ ^ 2 = ‖x - u‖ ^ 2 -
      2 * η * inner ℝ g (x - u) + η ^ 2 * ‖g‖ ^ 2 := by
    rw [show x - η • g - u = (x - u) - η • g by abel,
      norm_sub_sq_real, inner_smul_right, real_inner_comm (x - u), norm_smul,
      Real.norm_eq_abs, abs_of_pos hη]
    ring
  have hs : ‖BanditRL.OnlineGradientDescent.project V (x - η • g) - u‖ ^ 2 ≤
      ‖x - η • g - u‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hp 2
  nlinarith
```

Imported exact def toReal (local scoped variables as in module; theorem proof omitted):
```lean
def toReal : EReal → ℝ
  | ⊥ => 0
  | ⊤ => 0
  | (x : ℝ) => x
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
