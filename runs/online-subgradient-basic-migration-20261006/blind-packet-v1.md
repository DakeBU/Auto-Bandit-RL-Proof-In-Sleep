Requested distinct restricted reconstruction GPT-6 Astra/medium. Read ONLYthis file, no other files/listings/sourceidentity/proof bodies/old verdict/compilation. Write ONLYblind-reconstruction-v1.md and blind-receipt-v1.json here, actor.task=/root/normal_blind/input-report rawSHA. Seven slots for N01,N02 and complete S definition. Honest prior-history limits; no humanexternal/runtimeattestation/source/proof/Goal certification.

Supplied imported notation/context only, not independently inspected proof: EReal has both infinities/embeddedREAL. P(f)=(forallx,fx!=bottom) AND existsx existsr:REAL,fx=coe r. D(f)={x |fx<top}, includesbottom generically. I(V)(x)=0 onV/topoutside. Convex and ConvexOn standard real linear meanings; actual class contexts below providezero, so E is nonempty, no Complete/finiteD requirement.

Full neutral definition:
```lean
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
def S (f : E → EReal) (x : E) : Set E :=
  {g | ∀ y, f x + (inner ℝ g (y - x) : EReal) ≤ f y}
```

Neutral headers without bodies:
```lean
theorem N01 (f : E → EReal) (hf : P f) (x g : E) (hg : g ∈ S f x) : x ∈ D f

theorem N02 (f : E → ℝ) (V : Set E) (hV : Convex ℝ V) (hsub : ∀ x ∈ V, (S (fun y => (f y : EReal)) x).Nonempty) : ConvexOn ℝ V f
```

Actual neutralized @types:
```text
@N01 : ∀ {E : Type u_1} [inst : NormedAddCommGroup E]
  [inst_1 : InnerProductSpace ℝ E] (f : E → EReal),
  P f →
    ∀ (x g : E), g ∈ S f x → x ∈ D f
@N02 : ∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : InnerProductSpace ℝ E]
  (f : E → ℝ) (V : Set E),
  Convex ℝ V → (∀ x ∈ V, (S (fun y => ↑(f y)) x).Nonempty) → ConvexOn ℝ V f
@S : {E : Type u_1} →
  [inst : NormedAddCommGroup E] → [InnerProductSpace ℝ E] → (E → EReal) → E → Set E

```

Decode what generic S does on bottom or identicallytop, what P restricts and whether N01 implies domain-of-S inclusion/empty outside by quantifier conversion. N02 assumes support existence, not produced by a function-convexity premise; inspect global forall y versus only V, REAL f domain and weight endpoints. No source identification requested.
