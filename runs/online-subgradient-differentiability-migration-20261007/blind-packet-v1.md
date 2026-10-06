Requested distinct restricted decoder GPT-6 Astra/medium. Read ONLY this file; no filesystem search/source identity/proof bodies/verdicts/compilation. Write ONLY blind-reconstruction-v1.md and blind-receipt-v1.json in this run. Seven semantic slots for all eleven N01-N11 and complete R, emphasizing N09/N10/N11. State every hidden or derived regularity versus supplied premise; diagnose bare toReal versus genuine local real germ, ambient/domain-restricted derivative and every representative gradient. Honest prior-history limits; no human/external/runtime-model or source/Goal certification.

Supplied notation context: REAL field; EReal both infinities and real embedding; C(f) means convex REAL-height epigraph {(x,t):E×REAL |fx≤coet}; D(f)={x|fx<top}, bottom included generically. P(f) means nowherebottom plus exists a finite real value. S(f,x)={g |∀y in entire ambientE,fx+coe(innerREALg(y-x))≤fy}. I(A)(x)=0 ifx∈A/topotherwise. DifferentiableAt means ambient Frechet real differentiability. HasGradientAt is inner-product/Riesz derivative identity. All main N statements finite-dimensional real inner-product; actual R definition omits unused finiteD binder. Classes contain zero, ambient nonempty, dimensionzero possible. No probability/algorithm supplied.

Complete neutral definition, not short header only:
```lean
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
def R (f : E → EReal) (x : E) : Prop :=
  ∃ h : E → ℝ, (fun y => (h y : EReal)) =ᶠ[𝓝 x] f ∧ DifferentiableAt ℝ h x
```

Neutral actual headers without proof bodies:
```lean
theorem N01 (f : E → EReal) (x : E) (r : ℝ) (hr : 0 < r) (K : ℝ≥0) (hfinite : ∀ y ∈ Metric.ball x r, ∃ a : ℝ, f y = (a : EReal)) (hlip : LipschitzOnWith K (fun y => (f y).toReal) (Metric.ball x r)) (g : E) (hg : g ∈ S f x) : ‖g‖ ≤ (K : ℝ)

theorem N02 (f : E → EReal) (hbot : ∀ y, f y ≠ ⊥) (hf : C f) (x : E) (hx : x ∈ interior (D f)) : ∃ r : ℝ, 0 < r ∧ ∃ K : ℝ≥0, ∀ y ∈ Metric.ball x r, ∀ g ∈ S f y, ‖g‖ ≤ (K : ℝ)

theorem N03 {ι : Type*} (l : Filter ι) [NeBot l] (f : E → EReal) (hbot : ∀ y, f y ≠ ⊥) (x g : E) (hx : x ∈ interior (D f)) (hcont : ContinuousAt (fun y => (f y).toReal) x) (xs gs : ι → E) (hxs : Tendsto xs l (𝓝 x)) (hgs : Tendsto gs l (𝓝 g)) (hs : ∀ᶠ i in l, gs i ∈ S f (xs i)) : g ∈ S f x

theorem N04 {ι : Type*} (l : Filter ι) [NeBot l] (f : E → EReal) (hbot : ∀ y, f y ≠ ⊥) (hf : C f) (x g : E) (hx : x ∈ interior (D f)) (hg : S f x = {g}) (xs gs : ι → E) (hxs : Tendsto xs l (𝓝 x)) (hs : ∀ᶠ i in l, gs i ∈ S f (xs i)) : Tendsto gs l (𝓝 g)

theorem N05 (f : E → EReal) (hf : C f) (x : E) (hx : ∃ r : ℝ, f x = (r : EReal)) (g : E) (hg : S f x = {g}) : x ∈ interior (D f)

theorem N06 (f : E → EReal) (hf : C f) (x : E) (hx : ∃ r : ℝ, f x = (r : EReal)) (g : E) (hg : S f x = {g}) : HasGradientAt (fun y => (f y).toReal) g x

theorem N07 (f : E → EReal) (x : E) (hd : R f x) : (∀ᶠ y in 𝓝 x, ∃ r : ℝ, f y = (r : EReal)) ∧ x ∈ interior (D f) ∧ DifferentiableAt ℝ (fun y => (f y).toReal) x

theorem N08 (f : E → EReal) (hbot : ∀ z, f z ≠ ⊥) (x : E) (hx : x ∈ interior (D f)) (hd : DifferentiableAt ℝ (fun z => (f z).toReal) x) (g : E) (hg : g ∈ S f x) : g = gradient (fun z => (f z).toReal) x

theorem N09 (f : E → EReal) (hf : C f) (x : E) (hx : ∃ r : ℝ, f x = (r : EReal)) (h : E → ℝ) (he : (fun y => (h y : EReal)) =ᶠ[𝓝 x] f) (hd : DifferentiableAt ℝ h x) : S f x = {gradient h x}

theorem N10 (f : E → EReal) (hf : C f) (x : E) (hx : ∃ r : ℝ, f x = (r : EReal)) (hd : R f x) : ∃ g : E, S f x = {g}

theorem N11 (f : E → EReal) (hf : C f) (x : E) (hx : ∃ r : ℝ, f x = (r : EReal)) : R f x ↔ ∃ g : E, S f x = {g}
```

Neutral actual @types:
```text
@N01 : ∀ {E : Type u_1} [inst : NormedAddCommGroup E]
  [inst_1 : InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (f : E → EReal) (x : E) (r : ℝ),
  0 < r →
    ∀ (K : NNReal),
      (∀ y ∈ Metric.ball x r, ∃ a, f y = ↑a) →
        LipschitzOnWith K (fun y => (f y).toReal) (Metric.ball x r) →
          ∀ g ∈ S f x, ‖g‖ ≤ ↑K
@N02 : ∀ {E : Type u_1} [inst : NormedAddCommGroup E]
  [inst_1 : InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (f : E → EReal),
  (∀ (y : E), f y ≠ ⊥) →
    C f →
      ∀ x ∈ interior (D f),
        ∃ r, 0 < r ∧ ∃ K, ∀ y ∈ Metric.ball x r, ∀ g ∈ S f y, ‖g‖ ≤ ↑K
@N03 : ∀ {E : Type u_1} [inst : NormedAddCommGroup E]
  [inst_1 : InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {ι : Type u_2} (l : Filter ι) [l.NeBot] (f : E → EReal),
  (∀ (y : E), f y ≠ ⊥) →
    ∀ (x g : E),
      x ∈ interior (D f) →
        ContinuousAt (fun y => (f y).toReal) x →
          ∀ (xs gs : ι → E),
            Filter.Tendsto xs l (nhds x) →
              Filter.Tendsto gs l (nhds g) →
                (∀ᶠ (i : ι) in l, gs i ∈ S f (xs i)) →
                  g ∈ S f x
@N04 : ∀ {E : Type u_1} [inst : NormedAddCommGroup E]
  [inst_1 : InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {ι : Type u_2} (l : Filter ι) [l.NeBot] (f : E → EReal),
  (∀ (y : E), f y ≠ ⊥) →
    C f →
      ∀ (x g : E),
        x ∈ interior (D f) →
          S f x = {g} →
            ∀ (xs gs : ι → E),
              Filter.Tendsto xs l (nhds x) →
                (∀ᶠ (i : ι) in l, gs i ∈ S f (xs i)) →
                  Filter.Tendsto gs l (nhds g)
@N05 : ∀ {E : Type u_1} [inst : NormedAddCommGroup E]
  [inst_1 : InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (f : E → EReal),
  C f →
    ∀ (x : E),
      (∃ r, f x = ↑r) →
        ∀ (g : E),
          S f x = {g} → x ∈ interior (D f)
@N06 : ∀ {E : Type u_1} [inst : NormedAddCommGroup E]
  [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E] (f : E → EReal),
  C f →
    ∀ (x : E),
      (∃ r, f x = ↑r) →
        ∀ (g : E), S f x = {g} → HasGradientAt (fun y => (f y).toReal) g x
@N07 : ∀ {E : Type u_1} [inst : NormedAddCommGroup E]
  [inst_1 : InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (f : E → EReal) (x : E),
  R f x →
    (∀ᶠ (y : E) in nhds x, ∃ r, f y = ↑r) ∧
      x ∈ interior (D f) ∧ DifferentiableAt ℝ (fun y => (f y).toReal) x
@N08 : ∀ {E : Type u_1} [inst : NormedAddCommGroup E]
  [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E] (f : E → EReal),
  (∀ (z : E), f z ≠ ⊥) →
    ∀ x ∈ interior (D f),
      DifferentiableAt ℝ (fun z => (f z).toReal) x →
        ∀ g ∈ S f x, g = gradient (fun z => (f z).toReal) x
@N09 : ∀ {E : Type u_1} [inst : NormedAddCommGroup E]
  [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E] (f : E → EReal),
  C f →
    ∀ (x : E),
      (∃ r, f x = ↑r) →
        ∀ (h : E → ℝ),
          (fun y => ↑(h y)) =ᶠ[nhds x] f →
            DifferentiableAt ℝ h x → S f x = {gradient h x}
@N10 : ∀ {E : Type u_1} [inst : NormedAddCommGroup E]
  [inst_1 : InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (f : E → EReal),
  C f →
    ∀ (x : E),
      (∃ r, f x = ↑r) →
        R f x → ∃ g, S f x = {g}
@N11 : ∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (f : E → EReal),
  C f →
    ∀ (x : E),
      (∃ r, f x = ↑r) →
        (R f x ↔ ∃ g, S f x = {g})
@R : {E : Type u_1} →
  [inst : NormedAddCommGroup E] → [InnerProductSpace ℝ E] → (E → EReal) → E → Prop

```

Reconstruct logical terminal iff in N11 and singleton identity in N09. Does N11 assume globallyproper/interior/closed or only pointfinite? N04 filter is NeBot. Is R only differentiability of toReal or includes actual finite neighborhood? Could singleton indicator have smooth toReal and nevertheless fail R? Boundary and every-query support semantics explicit. Do not identify source.
