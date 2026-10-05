Required restricted reconstruction, requested GPT-6 Astra/medium. Read ONLY this file in this pass; no directory listing/source identity/prior verdict/proof bodies/other files/compilation. Three neutral actual header/type expressions and two full neutral definitions, with supplied imported notation. Write ONLY blind-reconstruction-v1.md and blind-receipt-v1.json here; input/report rawSHA, seven slots for eachN01–N03 and C/P. Honest prior-history limits, no human/external/runtime-model attestation or source/proof/Goal certification.

Supplied notation: EReal contains negative infinity, finite embedded reals and positive infinity. I(V)(x) is exactly0 for x∈V and positive infinity otherwise; it is supplied context, not independently inspected imported proof body. Standard set/topological/LowerSemicontinuous notation. No source identity.

Full neutral context/definition bodies:
```lean
open Set
variable {E : Type*} [TopologicalSpace E]
def C (f : E → EReal) : Prop := ∀ r : ℝ, IsClosed {x | f x ≤ (r : EReal)}
def P (f : E → EReal) : Prop := (∀ x, f x ≠ ⊥) ∧ ∃ x, ∃ r : ℝ, f x = (r : EReal)
```

Neutral actual headers, without proofs:
```lean
theorem N01 (f : E → EReal) : C f ↔ LowerSemicontinuous f

theorem N02 (V : Set E) : C (I V) ↔ IsClosed V

theorem N03 (V : Set E) : P (I V) ↔ V.Nonempty
```

Authoritative neutralized actual @constant types, including actual class binders and definition signatures:
```text
@N01 : ∀ {E : Type u_1} [inst : TopologicalSpace E]
  (f : E → EReal), C f ↔ LowerSemicontinuous f
@N02 : ∀ {E : Type u_1} [inst : TopologicalSpace E] (V : Set E),
  C (I V) ↔ IsClosed V
@N03 : ∀ {E : Type u_1} [TopologicalSpace E] (V : Set E),
  P (I V) ↔ V.Nonempty
@C : {E : Type u_1} → [TopologicalSpace E] → (E → EReal) → Prop
@P : {E : Type u_1} → (E → EReal) → Prop

```
