Restricted neutral reconstruction packet. Requested GPT-6 Astra/medium. Read ONLY this packet; no repository/source/history/search/proof body/prior verdict. Write ONLY blind-reconstruction-v1.md and blind-receipt-v1.json adjacent to packet; bind exact raw packet/report SHA, actor.task and requested settings without runtime attestation. Reconstruct ONE theorem L separately in natural language and LaTeX, seven slots spaces/objects, quantifier order, assumptions, conclusion, constants, information/probability, boundaries. S/P are TWO borrowed definition contexts, zero owned definitions. Do not infer cited source or acceptance.

```lean
noncomputable section
open Set
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
def S (f : E → EReal) (x : E) : Set E :=
  {g | ∀ y, f x + (inner ℝ g (y - x) : EReal) ≤ f y}

def P (f : E → EReal) : Prop :=
  (∀ x, f x ≠ ⊥) ∧ ∃ x, ∃ r : ℝ, f x = (r : EReal)

theorem L [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] (f : F → EReal) (hp : P f) (A : E →L[ℝ] F) (b : F) (x : E) : A.adjoint '' (S f (A x + b)) ⊆ S (fun y => f (A y + b)) x
```

Actual compiled theorem type:
```text
@L.{u_1,
    u_2} : ∀ {E : Type u_1} {F : Type u_2} [inst : NormedAddCommGroup.{u_1} E]
  [inst_1 : InnerProductSpace.{0, u_1} Real E] [inst_2 : NormedAddCommGroup.{u_2} F]
  [inst_3 : InnerProductSpace.{0, u_2} Real F] [inst_4 : FiniteDimensional.{0, u_1} Real E]
  [inst_5 : FiniteDimensional.{0, u_2} Real F] (f : F → EReal),
  P.{u_2} f →
    ∀ (A : ContinuousLinearMap.{0, 0, u_1, u_2} (RingHom.id.{0} Real) E F) (b : F) (x : E),
      Subset.{u_1}
        (Set.image.{u_2, u_1} (⇑(ContinuousLinearMap.adjoint.{0, u_1, u_2} A))
          (S.{u_2} f (HAdd.hAdd.{u_2, u_2, u_2} (A x) b)))
        (S.{u_1} (fun y => f (HAdd.hAdd.{u_2, u_2, u_2} (A y) b)) x)

```

Actual compiled TWO borrowed definition binder types:
```text
def S.{u_1} : {E : Type u_1} →
  [inst : NormedAddCommGroup.{u_1} E] → [InnerProductSpace.{0, u_1} Real E] → (E → EReal) → E → Set.{u_1} E

def P.{u_1} : {E : Type u_1} → (E → EReal) → Prop
```

EReal has top/bottom and canonical real embeddings; S tests every ambient y and P forbids bottom globally plus supplies one finite witness. Only use the displayed compiled binders. Actual ContinuousLinearMap.adjoint is Mathlib Hilbert adjoint, with completeness supplied by finite-dimensional real inner structure in L. Set.image is full image, subset is one direction. Do not infer convexity/continuity/closedness of f, properness of composite, rank conditions, finite query, support nonemptiness, equality, algorithm/regret/probability/selection or coordinate conversion certificates. Keep any limits/generic improper-context conventions explicit without seeing proof/source.
