Restricted neutral reconstruction packet. Requested GPT-6 Astra/medium. Read ONLY this packet; no repository/source/history/search/proof body/prior verdict. Write ONLY blind-reconstruction-v1.md and blind-receipt-v1.json adjacent to packet, bind exact raw packet/report SHA and actor.task/requested settings, no runtime attestation. Reconstruct ONE owned definition B and ONE theorem L separately in natural language/LaTeX and seven semantic slots (objects, quantifier order, assumptions, conclusion, constants, information/probability, boundaries). Five other definition contexts S/P/D/Q/C are borrowed and not newly owned. Use actual compiled binder types, not blanket ambient assumptions.

```lean
noncomputable section
open Set
open scoped Topology NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
def S (f : E → EReal) (x : E) : Set E :=
  {g | ∀ y, f x + (inner ℝ g (y - x) : EReal) ≤ f y}

def P (f : E → EReal) : Prop :=
  (∀ x, f x ≠ ⊥) ∧ ∃ x, ∃ r : ℝ, f x = (r : EReal)

def D (f : E → EReal) : Set E := {x | f x < ⊤}

def Q (f : E → EReal) : Set (E × ℝ) := {p | f p.1 ≤ (p.2 : EReal)}

def C (f : E → EReal) : Prop := Convex ℝ (Q f)

def B (f : E → EReal) (V : Set E) (L : ℝ≥0) : Prop :=
  (∀ x ∈ V, ∃ a : ℝ, f x = (a : EReal)) ∧
    ∀ x ∈ V, ∀ y ∈ V, |(f x).toReal - (f y).toReal| ≤ (L : ℝ) * ‖x - y‖

theorem L [FiniteDimensional ℝ E] (f : E → EReal) (hp : P f) (hc : C f) (L : ℝ≥0) : B f (interior (D f)) L ↔ ∀ x ∈ interior (D f), ∀ g ∈ S f x, ‖g‖ ≤ (L : ℝ)
```

Actual compiled primary types:
```text
@B.{u_1} : {E : Type u_1} →
  [NormedAddCommGroup.{u_1} E] → (E → EReal) → Set.{u_1} E → NNReal → Prop
@L.{u_1} : ∀ {E : Type u_1} [inst : NormedAddCommGroup.{u_1} E]
  [inst_1 : InnerProductSpace.{0, u_1} Real E] [FiniteDimensional.{0, u_1} Real E] (f : E → EReal),
  P.{u_1} f →
    C.{u_1} f →
      ∀ (L : NNReal),
        Iff
          (B.{u_1} f
            (interior.{u_1} (D.{u_1} f)) L)
          (∀ (x : E),
            Membership.mem.{u_1, u_1} (interior.{u_1} (D.{u_1} f)) x →
              ∀ (g : E),
                Membership.mem.{u_1, u_1} (S.{u_1} f x) g →
                  LE.le.{0} (norm.{u_1} g) ↑L)

```

Actual compiled SIX definition binder types:
```text
def B.{u_1} : {E : Type u_1} →
  [NormedAddCommGroup.{u_1} E] → (E → EReal) → Set.{u_1} E → NNReal → Prop

def S.{u_1} : {E : Type u_1} →
  [inst : NormedAddCommGroup.{u_1} E] → [InnerProductSpace.{0, u_1} Real E] → (E → EReal) → E → Set.{u_1} E

def P.{u_1} : {E : Type u_1} → (E → EReal) → Prop

def D.{u_1} : {E : Type u_1} → (E → EReal) → Set.{u_1} E

def Q.{u_1} : {E : Type u_1} → (E → EReal) → Set.{u_1} (Prod.{u_1, 0} E Real)

def C.{u_1} : {E : Type u_1} →
  [inst : AddCommGroup.{u_1} E] → [Module.{0, u_1} Real E] → (E → EReal) → Prop
```

EReal has top/bottom and real embeddings; B requires genuine finite real witnesses on V before its toReal difference. NNReal is the nonnegative reals INCLUDING0. D tests strict inequality belowtop; P forbids bottom globally with a finite witness; S uses all ambient support tests; Q is a real-height epigraph and C its convexity. Theorem uses AMBIENT interior, not relative interior or closure/boundary/all of D. Norm is the inherited inner-product norm in L; B's own actual inferred binders determine its broader scope. No closedness, differentiability, boundedness, positive constant/positive dimension/nonempty interior or supplied support-existence premise. No source all-real-constant claim, selected-gradient-only conclusion, future algorithm/oracle/regret/probability/feedback/selection certificate. Do not infer cited source or acceptance from this packet.
