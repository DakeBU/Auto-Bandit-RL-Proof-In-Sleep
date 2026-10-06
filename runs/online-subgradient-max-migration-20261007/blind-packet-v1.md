Restricted neutral reconstruction packet; requested GPT-6 Astra/medium. Read ONLY this packet. No repository/source lookup, proof bodies, source identity, prior verdict or inherited history. Write ONLY blind-reconstruction-v1.md and blind-receipt-v1.json adjacent to this packet; bind exact raw packet/report SHA and actor.task. Reconstruct all SEVENTEEN proof targets C01-C17 separately in natural language and LaTeX with seven semantic slots (objects/spaces; quantifiers; assumptions; conclusions; constants; information/probability; boundaries). Separate two owned definitions M/U from five borrowed contexts S/P/D/Q/C. Do not guess numbered source identity, count supporting lemmas as separate source results, or certify source acceptance, whole chapter/Goal, external-human review/runtime model.

```lean
noncomputable section
open Set Filter Topology
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
```

Exact neutral headers:
```lean
theorem C01 {ι : Type*} [Fintype ι] [Nonempty ι] (f : ι → E → EReal) (x : E) : U f x ⊆ S (M f) x

theorem C02 {ι : Type*} [Fintype ι] [Nonempty ι] (f : ι → E → EReal) (x : E) : ∃ i, M f x = f i x

theorem C03 {ι : Type*} [Fintype ι] [Nonempty ι] (f : ι → E → EReal) (hp : ∀ i, P (f i)) (x : E) (hx : ∀ i, x ∈ D (f i)) : ∃ a : ℝ, M f x = (a : EReal)

theorem C04 (f : E → EReal) (hbot : ∀ y, f y ≠ ⊥) (x : E) (hx : x ∈ D f) (g : E) : g ∈ S f x ↔ ∀ y, f y ≠ ⊤ → (f x).toReal + inner ℝ g (y - x) ≤ (f y).toReal

theorem C05 (f : E → EReal) (hbot : ∀ y, f y ≠ ⊥) (x : E) (hx : x ∈ D f) : Convex ℝ (S f x)

theorem C06 (f : E → EReal) (x : E) (hx : x ∈ D f) (hc : ContinuousAt f x) : x ∈ interior (D f)

theorem C07 {ι : Type*} [Fintype ι] [Nonempty ι] (f : ι → E → EReal) (hp : ∀ i, P (f i)) (y : E) : M f y ≠ ⊥

theorem C08 {ι : Type*} [Fintype ι] [Nonempty ι] (f : ι → E → EReal) (hp : ∀ i, P (f i)) (x : E) (hx : ∀ i, x ∈ D (f i)) : convexHull ℝ (U f x) ⊆ S (M f) x

theorem C09 (f : E → EReal) (hbot : ∀ y, f y ≠ ⊥) (x : E) (hx : x ∈ D f) : IsClosed (S f x)

theorem C10 [FiniteDimensional ℝ E] (f : E → EReal) (hp : P f) (hf : C f) (x : E) (hx : x ∈ interior (D f)) : IsCompact (S f x)

theorem C11 (s t : Set E) (hs : IsCompact s) (ht : IsCompact t) : IsCompact (convexJoin ℝ s t)

theorem C12 {ι : Type*} (s : ι → Set E) (F : Finset ι) (hc : ∀ i ∈ F, Convex ℝ (s i)) (hk : ∀ i ∈ F, IsCompact (s i)) : IsCompact (convexHull ℝ (⋃ i ∈ F, s i))

theorem C13 [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι] [Nonempty ι] (f : ι → E → EReal) (hp : ∀ i, P (f i)) (hc : ∀ i, C (f i)) (x : E) (hx : ∀ i, x ∈ D (f i)) (hcont : ∀ i, ContinuousAt (f i) x) : IsCompact (convexHull ℝ (U f x))

theorem C14 (f : E → EReal) (x : E) (ht : f x ≠ ⊤) (hb : f x ≠ ⊥) (hc : ContinuousAt f x) : ContinuousAt (fun y => (f y).toReal) x

theorem C15 {ι : Type*} [Fintype ι] [Nonempty ι] (f : ι → E → EReal) (hp : ∀ i, P (f i)) (x : E) (hx : ∀ i, x ∈ D (f i)) (y : E) (i : ι) (hy : y ∈ D (f i)) (hi : M f y = f i y) (g k : E) (hg : g ∈ S (M f) x) (hk : k ∈ S (f i) y) : inner ℝ g (y - x) ≤ inner ℝ k (y - x)

theorem C16 [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι] [Nonempty ι] (f : ι → E → EReal) (hp : ∀ i, P (f i)) (hc : ∀ i, C (f i)) (x : E) (hx : ∀ i, x ∈ D (f i)) (hcont : ∀ i, ContinuousAt (f i) x) (g d : E) (hg : g ∈ S (M f) x) : ∃ k ∈ U f x, inner ℝ g d ≤ inner ℝ k d

theorem C17 [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι] [Nonempty ι] (f : ι → E → EReal) (hp : ∀ i, P (f i)) (hc : ∀ i, C (f i)) (x : E) (hx : ∀ i, x ∈ D (f i)) (hcont : ∀ i, ContinuousAt (f i) x) : S (M f) x = convexHull ℝ (U f x)
```

Actual compiled neutral public types:
```text
@M.{u_1,
    u_2} : {E : Type u_1} → {ι : Type u_2} → [Fintype.{u_2} ι] → [Nonempty.{u_2 + 1} ι] → (ι → E → EReal) → E → EReal
@U.{u_1,
    u_2} : {E : Type u_1} →
  [inst : NormedAddCommGroup.{u_1} E] →
    [InnerProductSpace.{0, u_1} Real E] →
      {ι : Type u_2} → [Fintype.{u_2} ι] → [Nonempty.{u_2 + 1} ι] → (ι → E → EReal) → E → Set.{u_1} E
@C01.{u_1,
    u_2} : ∀ {E : Type u_1} [inst : NormedAddCommGroup.{u_1} E] [inst_1 : InnerProductSpace.{0, u_1} Real E]
  {ι : Type u_2} [inst_2 : Fintype.{u_2} ι] [inst_3 : Nonempty.{u_2 + 1} ι] (f : ι → E → EReal) (x : E),
  Subset.{u_1} (U.{u_1, u_2} f x)
    (S.{u_1} (M.{u_1, u_2} f) x)
@C02.{u_1,
    u_2} : ∀ {E : Type u_1} [inst : NormedAddCommGroup.{u_1} E] [InnerProductSpace.{0, u_1} Real E] {ι : Type u_2}
  [inst : Fintype.{u_2} ι] [inst_1 : Nonempty.{u_2 + 1} ι] (f : ι → E → EReal) (x : E),
  ∃ i, Eq.{1} (M.{u_1, u_2} f x) (f i x)
@C03.{u_1,
    u_2} : ∀ {E : Type u_1} [inst : NormedAddCommGroup.{u_1} E] [InnerProductSpace.{0, u_1} Real E] {ι : Type u_2}
  [inst : Fintype.{u_2} ι] [inst_1 : Nonempty.{u_2 + 1} ι] (f : ι → E → EReal),
  (∀ (i : ι), P.{u_1} (f i)) →
    ∀ (x : E),
      (∀ (i : ι), Membership.mem.{u_1, u_1} (D.{u_1} (f i)) x) →
        ∃ a, Eq.{1} (M.{u_1, u_2} f x) ↑a
@C04.{u_1} : ∀ {E : Type u_1} [inst : NormedAddCommGroup.{u_1} E]
  [inst_1 : InnerProductSpace.{0, u_1} Real E] (f : E → EReal),
  (∀ (y : E), Ne.{1} (f y) Bot.bot.{0}) →
    ∀ (x : E),
      Membership.mem.{u_1, u_1} (D.{u_1} f) x →
        ∀ (g : E),
          Iff (Membership.mem.{u_1, u_1} (S.{u_1} f x) g)
            (∀ (y : E),
              Ne.{1} (f y) Top.top.{0} →
                LE.le.{0}
                  (HAdd.hAdd.{0, 0, 0} (EReal.toReal (f x)) (inner.{0, u_1} Real g (HSub.hSub.{u_1, u_1, u_1} y x)))
                  (EReal.toReal (f y)))
@C05.{u_1} : ∀ {E : Type u_1} [inst : NormedAddCommGroup.{u_1} E]
  [inst_1 : InnerProductSpace.{0, u_1} Real E] (f : E → EReal),
  (∀ (y : E), Ne.{1} (f y) Bot.bot.{0}) →
    ∀ (x : E),
      Membership.mem.{u_1, u_1} (D.{u_1} f) x →
        Convex.{0, u_1} Real (S.{u_1} f x)
@C06.{u_1} : ∀ {E : Type u_1} [inst : NormedAddCommGroup.{u_1} E]
  [InnerProductSpace.{0, u_1} Real E] (f : E → EReal) (x : E),
  Membership.mem.{u_1, u_1} (D.{u_1} f) x →
    ContinuousAt.{u_1, 0} f x →
      Membership.mem.{u_1, u_1} (interior.{u_1} (D.{u_1} f)) x
@C07.{u_1,
    u_2} : ∀ {E : Type u_1} [inst : NormedAddCommGroup.{u_1} E] [InnerProductSpace.{0, u_1} Real E] {ι : Type u_2}
  [inst : Fintype.{u_2} ι] [inst_1 : Nonempty.{u_2 + 1} ι] (f : ι → E → EReal),
  (∀ (i : ι), P.{u_1} (f i)) →
    ∀ (y : E), Ne.{1} (M.{u_1, u_2} f y) Bot.bot.{0}
@C08.{u_1,
    u_2} : ∀ {E : Type u_1} [inst : NormedAddCommGroup.{u_1} E] [inst_1 : InnerProductSpace.{0, u_1} Real E]
  {ι : Type u_2} [inst_2 : Fintype.{u_2} ι] [inst_3 : Nonempty.{u_2 + 1} ι] (f : ι → E → EReal),
  (∀ (i : ι), P.{u_1} (f i)) →
    ∀ (x : E),
      (∀ (i : ι), Membership.mem.{u_1, u_1} (D.{u_1} (f i)) x) →
        Subset.{u_1} ((convexHull.{0, u_1} Real) (U.{u_1, u_2} f x))
          (S.{u_1} (M.{u_1, u_2} f) x)
@C09.{u_1} : ∀ {E : Type u_1} [inst : NormedAddCommGroup.{u_1} E]
  [inst_1 : InnerProductSpace.{0, u_1} Real E] (f : E → EReal),
  (∀ (y : E), Ne.{1} (f y) Bot.bot.{0}) →
    ∀ (x : E),
      Membership.mem.{u_1, u_1} (D.{u_1} f) x →
        IsClosed.{u_1} (S.{u_1} f x)
@C10.{u_1} : ∀ {E : Type u_1} [inst : NormedAddCommGroup.{u_1} E]
  [inst_1 : InnerProductSpace.{0, u_1} Real E] [FiniteDimensional.{0, u_1} Real E] (f : E → EReal),
  P.{u_1} f →
    C.{u_1} f →
      ∀ (x : E),
        Membership.mem.{u_1, u_1} (interior.{u_1} (D.{u_1} f)) x →
          IsCompact.{u_1} (S.{u_1} f x)
@C11.{u_1} : ∀ {E : Type u_1} [inst : NormedAddCommGroup.{u_1} E]
  [inst_1 : InnerProductSpace.{0, u_1} Real E] (s t : Set.{u_1} E),
  IsCompact.{u_1} s → IsCompact.{u_1} t → IsCompact.{u_1} (convexJoin.{0, u_1} Real s t)
@C12.{u_1,
    u_2} : ∀ {E : Type u_1} [inst : NormedAddCommGroup.{u_1} E] [inst_1 : InnerProductSpace.{0, u_1} Real E]
  {ι : Type u_2} (s : ι → Set.{u_1} E) (F : Finset.{u_2} ι),
  (∀ (i : ι), Membership.mem.{u_2, u_2} F i → Convex.{0, u_1} Real (s i)) →
    (∀ (i : ι), Membership.mem.{u_2, u_2} F i → IsCompact.{u_1} (s i)) →
      IsCompact.{u_1} ((convexHull.{0, u_1} Real) (⋃ i, ⋃ (_ : Membership.mem.{u_2, u_2} F i), s i))
@C13.{u_1,
    u_2} : ∀ {E : Type u_1} [inst : NormedAddCommGroup.{u_1} E] [inst_1 : InnerProductSpace.{0, u_1} Real E]
  [FiniteDimensional.{0, u_1} Real E] {ι : Type u_2} [inst_3 : Fintype.{u_2} ι] [inst_4 : Nonempty.{u_2 + 1} ι]
  (f : ι → E → EReal),
  (∀ (i : ι), P.{u_1} (f i)) →
    (∀ (i : ι), C.{u_1} (f i)) →
      ∀ (x : E),
        (∀ (i : ι), Membership.mem.{u_1, u_1} (D.{u_1} (f i)) x) →
          (∀ (i : ι), ContinuousAt.{u_1, 0} (f i) x) →
            IsCompact.{u_1}
              ((convexHull.{0, u_1} Real) (U.{u_1, u_2} f x))
@C14.{u_1} : ∀ {E : Type u_1} [inst : NormedAddCommGroup.{u_1} E]
  [InnerProductSpace.{0, u_1} Real E] (f : E → EReal) (x : E),
  Ne.{1} (f x) Top.top.{0} →
    Ne.{1} (f x) Bot.bot.{0} → ContinuousAt.{u_1, 0} f x → ContinuousAt.{u_1, 0} (fun y => EReal.toReal (f y)) x
@C15.{u_1,
    u_2} : ∀ {E : Type u_1} [inst : NormedAddCommGroup.{u_1} E] [inst_1 : InnerProductSpace.{0, u_1} Real E]
  {ι : Type u_2} [inst_2 : Fintype.{u_2} ι] [inst_3 : Nonempty.{u_2 + 1} ι] (f : ι → E → EReal),
  (∀ (i : ι), P.{u_1} (f i)) →
    ∀ (x : E),
      (∀ (i : ι), Membership.mem.{u_1, u_1} (D.{u_1} (f i)) x) →
        ∀ (y : E) (i : ι),
          Membership.mem.{u_1, u_1} (D.{u_1} (f i)) y →
            Eq.{1} (M.{u_1, u_2} f y) (f i y) →
              ∀ (g k : E),
                Membership.mem.{u_1, u_1}
                    (S.{u_1}
                      (M.{u_1, u_2} f) x)
                    g →
                  Membership.mem.{u_1, u_1} (S.{u_1} (f i) y) k →
                    LE.le.{0} (inner.{0, u_1} Real g (HSub.hSub.{u_1, u_1, u_1} y x))
                      (inner.{0, u_1} Real k (HSub.hSub.{u_1, u_1, u_1} y x))
@C16.{u_1,
    u_2} : ∀ {E : Type u_1} [inst : NormedAddCommGroup.{u_1} E] [inst_1 : InnerProductSpace.{0, u_1} Real E]
  [FiniteDimensional.{0, u_1} Real E] {ι : Type u_2} [inst_3 : Fintype.{u_2} ι] [inst_4 : Nonempty.{u_2 + 1} ι]
  (f : ι → E → EReal),
  (∀ (i : ι), P.{u_1} (f i)) →
    (∀ (i : ι), C.{u_1} (f i)) →
      ∀ (x : E),
        (∀ (i : ι), Membership.mem.{u_1, u_1} (D.{u_1} (f i)) x) →
          (∀ (i : ι), ContinuousAt.{u_1, 0} (f i) x) →
            ∀ (g d : E),
              Membership.mem.{u_1, u_1}
                  (S.{u_1}
                    (M.{u_1, u_2} f) x)
                  g →
                ∃ k,
                  And (Membership.mem.{u_1, u_1} (U.{u_1, u_2} f x) k)
                    (LE.le.{0} (inner.{0, u_1} Real g d) (inner.{0, u_1} Real k d))
@C17.{u_1,
    u_2} : ∀ {E : Type u_1} [inst : NormedAddCommGroup.{u_1} E] [inst_1 : InnerProductSpace.{0, u_1} Real E]
  [FiniteDimensional.{0, u_1} Real E] {ι : Type u_2} [inst_3 : Fintype.{u_2} ι] [inst_4 : Nonempty.{u_2 + 1} ι]
  (f : ι → E → EReal),
  (∀ (i : ι), P.{u_1} (f i)) →
    (∀ (i : ι), C.{u_1} (f i)) →
      ∀ (x : E),
        (∀ (i : ι), Membership.mem.{u_1, u_1} (D.{u_1} (f i)) x) →
          (∀ (i : ι), ContinuousAt.{u_1, 0} (f i) x) →
            Eq.{u_1 + 1}
              (S.{u_1} (M.{u_1, u_2} f) x)
              ((convexHull.{0, u_1} Real) (U.{u_1, u_2} f x))

```

EReal includes top and bottom. S universally tests EVERY ambient y. P prohibits bottom EVERYWHERE and requires an actual finite witness; D uses value<top. C is real epigraph convexity. M is actual nonempty finite maximum, U includes ALL supports of every actual attaining component. Use actual inferred binders: M is on arbitrary E, while U uses real inner-product structure; each proof may retain section classes and some add finite dimensionality explicitly. Norm is that compatible real inner-product norm. Full C17 uses finite-dimensional E; finite NONEMPTY index; every component proper/convex; common finite query; EVERY component AMBIENT EReal ContinuityAt at that query; full ordinary convexHull equality BOTH directions for ALL candidate vectors. No closed hull, merely one-way inclusion, supplied decomposition, assumed direction witness, relative-domain continuity, globally finite function, extra boundedness/closedness/positive dimension/computability/measurable selection/feedback/regret/probability guarantee. Distinguish stronger foundational premise scopes from C17. Reconstruct direction witness C16 from its actual universal g/d, existential active k, and inner-product inequality without seeing proof.
