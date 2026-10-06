Requested distinct restricted decoder GPT-6 Astra/medium. Read ONLYthis packet, no other files/listings/sourceidentity/proof bodies/old verdict/compilation. Write ONLY blind-reconstruction-v1.md and blind-receipt-v1.json here, actor.task=/root/normal_blind/input-reportSHA. Seven slots N01,N02,N03; honest priorhistory/restrictedpacket, no source/proof/Goal certification.

Imported notation/context supplied only: EReal both infinities/REAL coercion; D(f)={x|fx<top}; P(f)=(forallx,fx!=bottom) AND existsx existsr:REAL,fx=coe r; C(f)=Convex REAL {(x,r):E×REAL|fx<=coe r}. intrinsicInterior REAL A is coercion image of interior of preimage A in affineSpan REAL A, not closure/ambientinterior. Normedlinear carriers providezero/nonempty. Finite-dimensional REAL normed carriers complete; no separateCompleteSpace terminalbinder. Continuous linear a uses notation E→L[REAL]REAL.

Global support notation:
```lean
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
def S (f : H → EReal) (x : H) : Set H :=
 {g | ∀ y, f x + (inner ℝ g (y-x) : EReal) ≤ f y}
```

Neutral terminal headers with explicitcontexts/no bodies:
```lean
theorem N01 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (f : E → EReal) (hbot : ∀ y, f y ≠ ⊥) (hc : C f) (x : E) (hx : x ∈ intrinsicInterior ℝ (D f)) : ∃ (a : E →L[ℝ] ℝ) (b : ℝ), ((a x + b : ℝ) : EReal) = f x ∧ ∀ y, ((a y + b : ℝ) : EReal) ≤ f y

theorem N02 {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] (f : F → EReal) (hf : P f) (hc : C f) (x : F) (hx : x ∈ intrinsicInterior ℝ (D f)) : (S f x).Nonempty

theorem N03 {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] (f : F → EReal) (hf : P f) (hc : C f) (x : F) (hx : x ∈ interior (D f)) : (S f x).Nonempty
```

N01/N02 are PRECISE PLANNED terminaltypes, no compiled body claim. N03 existing retained actualtype, no proof supplied. Distinguish global affine minorant alone from CONTACT plus globalbound, specified x versus existsx, relative versus ambient interior, no-bottom versus P, global supports and slopezero/uniqueness. No probabilities/algorithm/oracle input; no full-dimensional/closed/differentiable condition beyond printed terminaltypes. Do not infer source identity.
