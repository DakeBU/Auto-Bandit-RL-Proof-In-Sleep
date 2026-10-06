Restricted neutral reconstruction packet. Requested GPT-6 Astra / medium. Read ONLY this packet, no repository search, source identity, proof bodies, prior verdicts or other files. Write ONLY blind-reconstruction-v1.md and blind-receipt-v1.json next to this packet. Bind raw packet/report SHA and disclose exact input/history limits. Reconstruct EVERY target C01–C03 in natural language and LaTeX, seven semantic slots individually; separately reconstruct owned definition N and distinguish borrowed S/J. No source/package/chapter/Goal/external-human/runtime-model certification.

```lean
noncomputable section
open Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
def N (V : Set E) (x : E) : Set E :=
  {g | x ∈ V ∧ ∀ y ∈ V, inner ℝ g (y - x) ≤ 0}

def S (f : E → EReal) (x : E) : Set E :=
  {g | ∀ y, f x + (inner ℝ g (y - x) : EReal) ≤ f y}

def J (V : Set E) (x : E) : EReal := by
  classical
  exact if x ∈ V then 0 else ⊤
```

Exact three neutral headers:
```lean
theorem C01 [FiniteDimensional ℝ E] (V : Set E) (hVn : V.Nonempty) (hVc : Convex ℝ V) (x : E) : S (J V) x = N V x

theorem C02 [FiniteDimensional ℝ E] (V : Set E) (hVn : V.Nonempty) (hVc : Convex ℝ V) (x : E) (hx : x ∈ interior V) : N V x = {(0 : E)}

theorem C03 [FiniteDimensional ℝ E] (x : E) (hx : ‖x‖ = 1) : N {y : E | ‖y‖ ≤ 1} x = {g | ∃ α : ℝ, 0 ≤ α ∧ g = α • x}
```

Actual neutral compiled public types:
```text
@N : {E : Type u_1} →
  [inst : NormedAddCommGroup E] → [InnerProductSpace ℝ E] → Set E → E → Set E
@C01 : ∀ {E : Type u_1} [inst : NormedAddCommGroup E]
  [inst_1 : InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (V : Set E),
  V.Nonempty →
    Convex ℝ V →
      ∀ (x : E),
        S (J V) x =
          N V x
@C02 : ∀ {E : Type u_1} [inst : NormedAddCommGroup E]
  [inst_1 : InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (V : Set E),
  V.Nonempty → Convex ℝ V → ∀ x ∈ interior V, N V x = {0}
@C03 : ∀ {E : Type u_1} [inst : NormedAddCommGroup E]
  [inst_1 : InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (x : E),
  ‖x‖ = 1 → N {y | ‖y‖ ≤ 1} x = {g | ∃ α, 0 ≤ α ∧ g = α • x}

```

Use actual explicit/inferred binders and every universal quantifier. EReal has top/bottom; J takes only0/top, S is global and can accept arbitrary EReal functions. Norm/inner product are the real inner-product structure's compatible norm. Convex ℝ V uses real convex combinations; interior is ambient topological interior. The first two statements retain nonempty convexV explicitly. Definitions may have fewer class parameters than the theorems. The final statement's existential scalar is real, with0≤α, equality includes all elements. Distinguish equality from inclusion, actual set membership from a supplied characterization, outside-query meaning, zero multipliers, empty/thin sets, finite-dimensional theorem binders and the closed norm≤1 set. Do not infer an algorithm, regret, probability, closedness of arbitraryV, relative interior, positive dimension, a separate coordinate isometry certificate or computable/measurable vector selection.
