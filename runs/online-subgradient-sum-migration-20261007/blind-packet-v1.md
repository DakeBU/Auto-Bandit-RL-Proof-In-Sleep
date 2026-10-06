Restricted distinct decoder requested GPT-6 Astra/medium. Read ONLY this packet, no searching/source identity/proof bodies/prior verdicts/compilation. Write ONLY blind-reconstruction-v1.md and blind-receipt-v1.json in this run. Seven semantic slots for ALL N01-N09 and COMPLETE M definition; main N08 inclusion and N09 equality both mandatory. Honest priorhistory limits/no human/external/runtime-model/source/bookGoal certification.

Neutral context: REAL field, EReal bothinfinities and realembedding; ordinary + is Mathlib bottom-dominant atmixedinfinities; U(a,b)=-(-a+-b), topdominant operation differs at mixed infinities. D(f)={x|fx<top}, includesbottom generically. P(f)=(forallx fxnebottom) AND existsx r:REAL fx=coer. Q(f)=forallr:REAL IsClosed{x|fx<=coer}. C(f) means convex REALheight epigraph {(x,t):E*REAL|fx<=coet}. S(f,x)={g|forallambienty fx+coe(innerREALg(y-x))<=fy}; accepts generic EReal f, not automaticallyproper. M is a genuine finite Minkowski set witnessed by actual component vectors and their sum. Ambient innerproduct E haszero/nonempty, dimension0possible. Six proofs N03,N04,N06,N07,N08,N09 actual finiteD realinner; scalarN01,N02,N05 noE classes; Mdefinition noFD. CompleteSpace derived not supplied. No algorithm/probability.

Complete neutral definition:
```lean
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
def M {ι : Type*} [Fintype ι]
    (f : ι → E → EReal) (x : E) : Set E :=
  {g | ∃ G : ι → E, (∀ i, G i ∈ S (f i) x) ∧ ∑ i, G i = g}
```

Neutral frozen actual headers without bodies:
```lean
theorem N01 (a b : EReal) (ha : a ≠ ⊥) (hb : b ≠ ⊥) : U a b = a + b

theorem N02 {ι : Type*} (s : Finset ι) (a : ι → EReal) (ha : ∀ i ∈ s, a i ≠ ⊥) : (∑ i ∈ s, a i) ≠ ⊥

theorem N03 {ι : Type*} (s : Finset ι) (f : ι → E → EReal) (hb : ∀ i ∈ s, ∀ y, f i y ≠ ⊥) (hc : ∀ i ∈ s, C (f i)) : C (fun y => ∑ i ∈ s, f i y)

theorem N04 {ι : Type*} [Fintype ι] (f : ι → E → EReal) (x : E) (hx : ∀ i, ∃ r : ℝ, f i x = (r : EReal)) : ∃ r : ℝ, (∑ i, f i x) = (r : EReal)

theorem N05 {ι : Type*} [Fintype ι] (a : ι → EReal) (hb : ∀ i, a i ≠ ⊥) (ht : (∑ i, a i) ≠ ⊤) : ∀ i, ∃ r : ℝ, a i = (r : EReal)

theorem N06 {ι : Type*} [Fintype ι] (f : ι → E → EReal) (hb : ∀ i y, f i y ≠ ⊥) (z : E) (hz : ∀ i, z ∈ interior (D (f i))) : z ∈ interior (D (fun y => ∑ i, f i y))

theorem N07 (f h : E → EReal) (hpf : P f) (hph : P h) (hcf : C f) (hch : C h) (x : E) (hfx : ∃ a : ℝ, f x = (a : EReal)) (hhx : ∃ b : ℝ, h x = (b : EReal)) (g : E) (hgs : g ∈ S (fun y => f y + h y) x) (hqual : ∃ z : E, z ∈ interior (D f) ∧ z ∈ D h) : ∃ p : E, p ∈ S f x ∧ g - p ∈ S h x

theorem N08 {ι : Type*} [Fintype ι] (f : ι → E → EReal) (hp : ∀ i, P (f i)) (x : E) : M f x ⊆ S (fun y => ∑ i, f i y) x

theorem N09 (n : ℕ) (f : Fin (n + 1) → E → EReal) (hp : ∀ i, P (f i)) (hc : ∀ i, C (f i)) (hclosed : ∀ i, Q (f i)) (hqual : ∃ z : E, z ∈ D (f (Fin.last n)) ∧ ∀ i : Fin (n + 1), i ≠ Fin.last n → z ∈ interior (D (f i))) (x : E) : S (fun y => ∑ i, f i y) x = M f x
```

Neutral actual @types:
```text
N01 : ∀ (a b : EReal),
  a ≠ ⊥ → b ≠ ⊥ → U a b = a + b
@N02 : ∀ {ι : Type u_1} (s : Finset ι) (a : ι → EReal),
  (∀ i ∈ s, a i ≠ ⊥) → ∑ i ∈ s, a i ≠ ⊥
@N03 : ∀ {E : Type u_1} [inst : NormedAddCommGroup E]
  [inst_1 : InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {ι : Type u_2} (s : Finset ι) (f : ι → E → EReal),
  (∀ i ∈ s, ∀ (y : E), f i y ≠ ⊥) →
    (∀ i ∈ s, C (f i)) →
      C fun y => ∑ i ∈ s, f i y
@N04 : ∀ {E : Type u_1} [inst : NormedAddCommGroup E]
  [inst_1 : InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {ι : Type u_2} [inst : Fintype ι] (f : ι → E → EReal)
  (x : E), (∀ (i : ι), ∃ r, f i x = ↑r) → ∃ r, ∑ i, f i x = ↑r
@N05 : ∀ {ι : Type u_1} [inst : Fintype ι] (a : ι → EReal),
  (∀ (i : ι), a i ≠ ⊥) → ∑ i, a i ≠ ⊤ → ∀ (i : ι), ∃ r, a i = ↑r
@N06 : ∀ {E : Type u_1} [inst : NormedAddCommGroup E]
  [inst_1 : InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {ι : Type u_2} [inst_3 : Fintype ι] (f : ι → E → EReal),
  (∀ (i : ι) (y : E), f i y ≠ ⊥) →
    ∀ (z : E),
      (∀ (i : ι), z ∈ interior (D (f i))) →
        z ∈ interior (D fun y => ∑ i, f i y)
@N07 : ∀ {E : Type u_1} [inst : NormedAddCommGroup E]
  [inst_1 : InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (f h : E → EReal),
  P f →
    P h →
      C f →
        C h →
          ∀ (x : E),
            (∃ a, f x = ↑a) →
              (∃ b, h x = ↑b) →
                ∀ g ∈ S (fun y => f y + h y) x,
                  (∃ z ∈ interior (D f),
                      z ∈ D h) →
                    ∃ p ∈ S f x,
                      g - p ∈ S h x
@N08 : ∀ {E : Type u_1} [inst : NormedAddCommGroup E]
  [inst_1 : InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {ι : Type u_2} [inst_3 : Fintype ι] (f : ι → E → EReal),
  (∀ (i : ι), P (f i)) →
    ∀ (x : E),
      M f x ⊆
        S (fun y => ∑ i, f i y) x
@N09 : ∀ {E : Type u_1} [inst : NormedAddCommGroup E]
  [inst_1 : InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (n : ℕ) (f : Fin (n + 1) → E → EReal),
  (∀ (i : Fin (n + 1)), P (f i)) →
    (∀ (i : Fin (n + 1)), C (f i)) →
      (∀ (i : Fin (n + 1)), Q (f i)) →
        (∃ z ∈ D (f (Fin.last n)),
            ∀ (i : Fin (n + 1)), i ≠ Fin.last n → z ∈ interior (D (f i))) →
          ∀ (x : E),
            S (fun y => ∑ i, f i y) x =
              M f x
@M : {E : Type u_1} →
  [inst : NormedAddCommGroup E] → [InnerProductSpace ℝ E] → {ι : Type u_2} → [Fintype ι] → (ι → E → EReal) → E → Set E

```

Reconstruct exact unconditional versus qualified conclusions. Does N08 require convexity/common finitepoint/queryfinite? Could the aggregate be identicallytop despite all components proper, and what would the generic S do there? In N09 is qualification at x or independent z? Must the LAST domain be interior? Are relative interiors substituted? Does equality allow empty family or only positive/singleton? Is Q retained even if a helper has weaker hypotheses? Are supplied queryfinite in N07 also supplied in N09, or absent there? M requires actual simultaneous witnesses, not sum-support membership alone. Keep all quantifier/regularity/degenerate/infinity/zero-dimensional boundaries. Do not identify source.
