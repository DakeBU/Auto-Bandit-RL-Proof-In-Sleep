Restricted neutral reconstruction packet; requested GPT-6 Astra/medium. Read ONLY this packet. No repository/source/history/search, proof bodies or prior verdict. Write ONLY blind-reconstruction-v1.md and blind-receipt-v1.json adjacent to this packet, binding raw packet/report SHA and actor.task. Reconstruct all THIRTEEN proof targets L01-L13 separately in natural language and LaTeX, comparing seven slots: spaces/objects, quantifiers/order, assumptions/regularity, conclusion, constants/normalization, probability/information, boundary. Separate TWO owned definitions H/B from SEVEN borrowed contexts S/P/D/Q/C/M/U. Do not infer numbered source identity, source acceptance, whole-program completion, human/external review or runtime attestation.

Exact definitions and required scoped context:
```lean
noncomputable section
open Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
def S (f : E → EReal) (x : E) : Set E :=
  {g | ∀ y, f x + (inner ℝ g (y - x) : EReal) ≤ f y}

def P (f : E → EReal) : Prop :=
  (∀ x, f x ≠ ⊥) ∧ ∃ x, ∃ r : ℝ, f x = (r : EReal)

def D (f : E → EReal) : Set E := {x | f x < ⊤}

def Q (f : E → EReal) : Set (E × ℝ) := {p | f p.1 ≤ (p.2 : EReal)}

def C (f : E → EReal) : Prop := Convex ℝ (Q f)

def M {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → E → EReal) (x : E) : EReal := by
  classical
  exact Finset.univ.sup' Finset.univ_nonempty (fun i => f i x)

def U {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → E → EReal) (x : E) : Set E :=
  {g | ∃ i, f i x = M f x ∧ g ∈ S (f i) x}

def H (z x : E) : EReal := ((max (1 - inner ℝ z x) 0 : ℝ) : EReal)

def B (z : E) (i : Bool) (y : E) : EReal :=
  ((inner ℝ (if i then -z else 0) y + (if i then 1 else 0) : ℝ) : EReal)
```

Exact neutral proof headers:
```lean
theorem L01 (a : E) (b : ℝ) (x : E) : S (fun y => ((inner ℝ a y + b : ℝ) : EReal)) x = {a}

theorem L02 (a : E) (b : ℝ) : P (fun y => ((inner ℝ a y + b : ℝ) : EReal))

theorem L03 (a : E) (b : ℝ) : C (fun y => ((inner ℝ a y + b : ℝ) : EReal))

theorem L04 (a : E) (b : ℝ) (x : E) : ContinuousAt (fun y => ((inner ℝ a y + b : ℝ) : EReal)) x

theorem L05 (z : E) : M (B z) = H z

theorem L06 [FiniteDimensional ℝ E] (z x : E) : S (H z) x = convexHull ℝ (U (B z) x)

theorem L07 (z : E) (i : Bool) (x : E) : S (B z i) x = {if i then -z else 0}

theorem L08 (z x : E) : B z false x = ((0 : ℝ) : EReal)

theorem L09 (z x : E) : B z true x = ((1 - inner ℝ z x : ℝ) : EReal)

theorem L10 (z x : E) (h : 1 - inner ℝ z x < 0) : U (B z) x = {(0 : E)}

theorem L11 (z x : E) (h : 0 < 1 - inner ℝ z x) : U (B z) x = {-z}

theorem L12 (z x : E) (h : 1 - inner ℝ z x = 0) : U (B z) x = {(0 : E), -z}

theorem L13 [FiniteDimensional ℝ E] (z x : E) : S (H z) x = if 1 - inner ℝ z x < 0 then {0} else if 1 - inner ℝ z x = 0 then {g | ∃ α ∈ Icc (0 : ℝ) 1, g = -(α • z)} else {-z}
```

Actual compiled public types:
```text
@H.{u_1} : {E : Type u_1} →
  [inst : NormedAddCommGroup.{u_1} E] → [InnerProductSpace.{0, u_1} Real E] → E → E → EReal
@L01.{u_1} : ∀ {E : Type u_1} [inst : NormedAddCommGroup.{u_1} E]
  [inst_1 : InnerProductSpace.{0, u_1} Real E] (a : E) (b : Real) (x : E),
  Eq.{u_1 + 1}
    (S.{u_1} (fun y => ↑(HAdd.hAdd.{0, 0, 0} (inner.{0, u_1} Real a y) b)) x)
    (singleton.{u_1, u_1} a)
@B.{u_1} : {E : Type u_1} →
  [inst : NormedAddCommGroup.{u_1} E] → [InnerProductSpace.{0, u_1} Real E] → E → Bool → E → EReal
@L02.{u_1} : ∀ {E : Type u_1} [inst : NormedAddCommGroup.{u_1} E]
  [inst_1 : InnerProductSpace.{0, u_1} Real E] (a : E) (b : Real),
  P.{u_1} fun y => ↑(HAdd.hAdd.{0, 0, 0} (inner.{0, u_1} Real a y) b)
@L03.{u_1} : ∀ {E : Type u_1} [inst : NormedAddCommGroup.{u_1} E]
  [inst_1 : InnerProductSpace.{0, u_1} Real E] (a : E) (b : Real),
  C.{u_1} fun y => ↑(HAdd.hAdd.{0, 0, 0} (inner.{0, u_1} Real a y) b)
@L04.{u_1} : ∀ {E : Type u_1} [inst : NormedAddCommGroup.{u_1} E]
  [inst_1 : InnerProductSpace.{0, u_1} Real E] (a : E) (b : Real) (x : E),
  ContinuousAt.{u_1, 0} (fun y => ↑(HAdd.hAdd.{0, 0, 0} (inner.{0, u_1} Real a y) b)) x
@L05.{u_1} : ∀ {E : Type u_1} [inst : NormedAddCommGroup.{u_1} E]
  [inst_1 : InnerProductSpace.{0, u_1} Real E] (z : E),
  Eq.{u_1 + 1} (M.{u_1, 0} (B.{u_1} z))
    (H.{u_1} z)
@L06.{u_1} : ∀ {E : Type u_1} [inst : NormedAddCommGroup.{u_1} E]
  [inst_1 : InnerProductSpace.{0, u_1} Real E] [FiniteDimensional.{0, u_1} Real E] (z x : E),
  Eq.{u_1 + 1} (S.{u_1} (H.{u_1} z) x)
    ((convexHull.{0, u_1} Real)
      (U.{u_1, 0} (B.{u_1} z) x))
@L07.{u_1} : ∀ {E : Type u_1} [inst : NormedAddCommGroup.{u_1} E]
  [inst_1 : InnerProductSpace.{0, u_1} Real E] (z : E) (i : Bool) (x : E),
  Eq.{u_1 + 1} (S.{u_1} (B.{u_1} z i) x)
    (singleton.{u_1, u_1} (ite.{u_1 + 1} (Eq.{1} i true) (Neg.neg.{u_1} z) 0))
@L08.{u_1} : ∀ {E : Type u_1} [inst : NormedAddCommGroup.{u_1} E]
  [inst_1 : InnerProductSpace.{0, u_1} Real E] (z x : E), Eq.{1} (B.{u_1} z false x) ↑0
@L09.{u_1} : ∀ {E : Type u_1} [inst : NormedAddCommGroup.{u_1} E]
  [inst_1 : InnerProductSpace.{0, u_1} Real E] (z x : E),
  Eq.{1} (B.{u_1} z true x) ↑(HSub.hSub.{0, 0, 0} 1 (inner.{0, u_1} Real z x))
@L10.{u_1} : ∀ {E : Type u_1} [inst : NormedAddCommGroup.{u_1} E]
  [inst_1 : InnerProductSpace.{0, u_1} Real E] (z x : E),
  LT.lt.{0} (HSub.hSub.{0, 0, 0} 1 (inner.{0, u_1} Real z x)) 0 →
    Eq.{u_1 + 1}
      (U.{u_1, 0} (B.{u_1} z) x)
      (singleton.{u_1, u_1} 0)
@L11.{u_1} : ∀ {E : Type u_1} [inst : NormedAddCommGroup.{u_1} E]
  [inst_1 : InnerProductSpace.{0, u_1} Real E] (z x : E),
  LT.lt.{0} 0 (HSub.hSub.{0, 0, 0} 1 (inner.{0, u_1} Real z x)) →
    Eq.{u_1 + 1}
      (U.{u_1, 0} (B.{u_1} z) x)
      (singleton.{u_1, u_1} (Neg.neg.{u_1} z))
@L12.{u_1} : ∀ {E : Type u_1} [inst : NormedAddCommGroup.{u_1} E]
  [inst_1 : InnerProductSpace.{0, u_1} Real E] (z x : E),
  Eq.{1} (HSub.hSub.{0, 0, 0} 1 (inner.{0, u_1} Real z x)) 0 →
    Eq.{u_1 + 1}
      (U.{u_1, 0} (B.{u_1} z) x)
      (insert.{u_1, u_1} 0 (singleton.{u_1, u_1} (Neg.neg.{u_1} z)))
@L13.{u_1} : ∀ {E : Type u_1} [inst : NormedAddCommGroup.{u_1} E]
  [inst_1 : InnerProductSpace.{0, u_1} Real E] [FiniteDimensional.{0, u_1} Real E] (z x : E),
  Eq.{u_1 + 1} (S.{u_1} (H.{u_1} z) x)
    (ite.{u_1 + 1} (LT.lt.{0} (HSub.hSub.{0, 0, 0} 1 (inner.{0, u_1} Real z x)) 0) (singleton.{u_1, u_1} 0)
      (ite.{u_1 + 1} (Eq.{1} (HSub.hSub.{0, 0, 0} 1 (inner.{0, u_1} Real z x)) 0)
        (setOf.{u_1} fun g =>
          ∃ α,
            And (Membership.mem.{0, 0} (Set.Icc.{0} 0 1) α)
              (Eq.{u_1 + 1} g (Neg.neg.{u_1} (HSMul.hSMul.{0, u_1, u_1} α z))))
        (singleton.{u_1, u_1} (Neg.neg.{u_1} z))))

```

Actual compiled types of ALL nine definition contexts (bodies omitted from compiler print):
```text
def H.{u_1} : {E : Type u_1} →
  [inst : NormedAddCommGroup.{u_1} E] → [InnerProductSpace.{0, u_1} Real E] → E → E → EReal

def B.{u_1} : {E : Type u_1} →
  [inst : NormedAddCommGroup.{u_1} E] → [InnerProductSpace.{0, u_1} Real E] → E → Bool → E → EReal

def S.{u_1} : {E : Type u_1} →
  [inst : NormedAddCommGroup.{u_1} E] → [InnerProductSpace.{0, u_1} Real E] → (E → EReal) → E → Set.{u_1} E

def P.{u_1} : {E : Type u_1} → (E → EReal) → Prop

def D.{u_1} : {E : Type u_1} → (E → EReal) → Set.{u_1} E

def Q.{u_1} : {E : Type u_1} → (E → EReal) → Set.{u_1} (Prod.{u_1, 0} E Real)

def C.{u_1} : {E : Type u_1} →
  [inst : AddCommGroup.{u_1} E] → [Module.{0, u_1} Real E] → (E → EReal) → Prop

def M.{u_1, u_2} : {E : Type u_1} →
  {ι : Type u_2} → [Fintype.{u_2} ι] → [Nonempty.{u_2 + 1} ι] → (ι → E → EReal) → E → EReal

def U.{u_1, u_2} : {E : Type u_1} →
  [inst : NormedAddCommGroup.{u_1} E] →
    [InnerProductSpace.{0, u_1} Real E] →
      {ι : Type u_2} → [Fintype.{u_2} ι] → [Nonempty.{u_2 + 1} ι] → (ι → E → EReal) → E → Set.{u_1} E
```

EReal includes top/bottom; real values are embedded canonically. S tests EVERY ambient y, P is global no-bottom plus a finite witness, D is value<top, C is real epigraph convexity. M is the actual nonempty finite maximum and U the union of every full support set of actual attaining components. Use actual compiled binders rather than imposing all section parameters on every borrowed definition. No claim about proof construction, algorithms, feedback, probability, regret, positive dimension, computable/measurable choice or coordinate conversions follows from this packet.
