Required restricted reconstruction, GPT-6 Astra/medium. Read ONLY this file in this pass; no source identity/numbered original names/earlier verdicts/other files/proof bodies.19neutral retained header/type expressions plus3neutral definitions. Write only blind-reconstruction-v1.md and blind-receipt-v1.json here, packet/report SHA and seven slots for every N01–N19. State supplied notation is not independently inspected imported bodies. Do not compile or source-review/claim clean history/human/external/runtime attestation.

Supplied neutral notation: P(a,r)=if |r|<=a then r^2/2 else a*(|r|-a/2); V is the full-space nonempty closed convex domain, F(a,z,y)(w)=P(a,<z,w>-y). Shared project selects nearest point; step(V,eta,f,x)=project(V,x-eta*gradient(f,x)); iterate starts x0 and updates using loss t only for the next state; regret sums loss_t(x_t)-loss_t(u) over0<=t<T. These are supplied definitions/notation, not proof bodies. Imported real calculus/norm/inner-product/filter notation standard.

Actual available scoped context for vector targets:
```lean
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

```

Neutral actual headers (without proofs):
```lean
theorem N01 (f g : ℝ → ℝ) (c d : ℝ) (hf : HasDerivAt f d c) (hg : HasDerivAt g d c) (he : f c = g c) : HasDerivAt (fun x => if x ≤ c then f x else g x) d c

theorem N02 (delta r : ℝ) (hd : 0 ≤ delta) : P delta r = if r ≤ -delta then -delta * r - delta ^ 2 / 2 else if r ≤ delta then r ^ 2 / 2 else delta * r - delta ^ 2 / 2

theorem N03 (r : ℝ) : P 0 r = 0

theorem N04 (f g df dg : ℝ → ℝ) (c x : ℝ) (hf : ∀ r, HasDerivAt f (df r) r) (hg : ∀ r, HasDerivAt g (dg r) r) (he : f c = g c) (hd : df c = dg c) : HasDerivAt (fun r => if r ≤ c then f r else g r) (if x ≤ c then df x else dg x) x

theorem N05 (delta r : ℝ) (hd : 0 ≤ delta) : HasDerivAt (P delta) (if r ≤ -delta then -delta else if r ≤ delta then r else delta) r

theorem N06 (delta r : ℝ) (hd : 0 ≤ delta) : deriv (P delta) r = max (-delta) (min r delta)

theorem N07 (delta : ℝ) (hd : 0 ≤ delta) : ConvexOn ℝ Set.univ (P delta)

theorem N08 (delta r : ℝ) (hd : 0 ≤ delta) : |deriv (P delta) r| ≤ delta

theorem N09 (delta r : ℝ) (hd : 0 ≤ delta) : deriv (P delta) r = if |r| ≤ delta then r else delta * Real.sign r

theorem N10 (delta y : ℝ) (hd : 0 ≤ delta) (z x : E) : HasGradientAt (fun w => P delta (inner ℝ z w - y)) (deriv (P delta) (inner ℝ z x - y) • z) x

theorem N11 (delta y : ℝ) (hd : 0 ≤ delta) (z : E) : ConvexOn ℝ Set.univ (fun w => P delta (inner ℝ z w - y))

theorem N12 (delta y : ℝ) (hd : 0 ≤ delta) (z x : E) : ‖gradient (fun w => P delta (inner ℝ z w - y)) x‖ ≤ delta * ‖z‖

theorem N13 (x : E) : project (V : Domain E) x = x

theorem N14 (delta y : ℝ) (hd : 0 ≤ delta) (z : E) : RegularLoss V (F delta z y)

theorem N15 (delta y eta : ℝ) (hd : 0 ≤ delta) (z x : E) : step V eta (F delta z y) x = x - eta • ((if |inner ℝ z x - y| ≤ delta then inner ℝ z x - y else delta * Real.sign (inner ℝ z x - y)) • z)

theorem N16 (delta Z eta : ℝ) (hd : 0 ≤ delta) (hZ : 0 ≤ Z) (heta : 0 < eta) (z : ℕ → E) (y : ℕ → ℝ) (x0 u : E) (T : ℕ) (hz : ∀ t < T, ‖z t‖ ≤ Z) : regret V eta (fun t => F delta (z t) (y t)) x0 u T ≤ ‖x0 - u‖ ^ 2 / (2 * eta) + eta / 2 * ((T : ℝ) * (delta * Z) ^ 2) - ‖iterate V eta (fun t => F delta (z t) (y t)) x0 T - u‖ ^ 2 / (2 * eta)

theorem N17 (delta Z : ℝ) (hd : 0 ≤ delta) (hZ : 0 ≤ Z) (z : ℕ → E) (y : ℕ → ℝ) (x0 u : E) (T : ℕ) (hT : 0 < T) (hz : ∀ t < T, ‖z t‖ ≤ Z) : regret V (1 / Real.sqrt T) (fun t => F delta (z t) (y t)) x0 u T / T ≤ (‖x0 - u‖ ^ 2 + (delta * Z) ^ 2) / (2 * Real.sqrt T)

theorem N18 (delta Z : ℝ) (x0 u : E) : Filter.Tendsto (fun T : ℕ => (‖x0 - u‖ ^ 2 + (delta * Z) ^ 2) / (2 * Real.sqrt T)) Filter.atTop (nhds 0)

theorem N19 (delta Z : ℝ) (hd : 0 ≤ delta) (hZ : 0 ≤ Z) (z : ℕ → E) (y : ℕ → ℝ) (x0 u : E) (hz : ∀ t, ‖z t‖ ≤ Z) (epsilon : ℝ) (he : 0 < epsilon) : ∀ᶠ T : ℕ in Filter.atTop, regret V (1 / Real.sqrt T) (fun t => F delta (z t) (y t)) x0 u T / T < epsilon
```

Authoritative neutralized actual @constant types (same separately elaborated constants, classes/quantifiers retained; original names replaced only):
```text
N01 : ∀ (f g : ℝ → ℝ) (c d : ℝ),
  HasDerivAt f d c → HasDerivAt g d c → f c = g c → HasDerivAt (fun x => if x ≤ c then f x else g x) d c
N02 : ∀ (delta r : ℝ),
  0 ≤ delta →
    P delta r =
      if r ≤ -delta then -delta * r - delta ^ 2 / 2 else if r ≤ delta then r ^ 2 / 2 else delta * r - delta ^ 2 / 2
N03 : ∀ (r : ℝ), P 0 r = 0
N04 : ∀ (f g df dg : ℝ → ℝ) (c x : ℝ),
  (∀ (r : ℝ), HasDerivAt f (df r) r) →
    (∀ (r : ℝ), HasDerivAt g (dg r) r) →
      f c = g c → df c = dg c → HasDerivAt (fun r => if r ≤ c then f r else g r) (if x ≤ c then df x else dg x) x
N05 : ∀ (delta r : ℝ),
  0 ≤ delta →
    HasDerivAt (P delta) (if r ≤ -delta then -delta else if r ≤ delta then r else delta) r
N06 : ∀ (delta r : ℝ),
  0 ≤ delta → deriv (P delta) r = max (-delta) (min r delta)
N07 : ∀ (delta : ℝ), 0 ≤ delta → ConvexOn ℝ Set.univ (P delta)
N08 : ∀ (delta r : ℝ),
  0 ≤ delta → |deriv (P delta) r| ≤ delta
N09 : ∀ (delta r : ℝ),
  0 ≤ delta → deriv (P delta) r = if |r| ≤ delta then r else delta * r.sign
@N10 : ∀ {E : Type u_1} [inst : NormedAddCommGroup E]
  [inst_1 : InnerProductSpace ℝ E] [inst_2 : CompleteSpace E] (delta y : ℝ),
  0 ≤ delta →
    ∀ (z x : E),
      HasGradientAt (fun w => P delta (inner ℝ z w - y))
        (deriv (P delta) (inner ℝ z x - y) • z) x
@N11 : ∀ {E : Type u_1} [inst : NormedAddCommGroup E]
  [inst_1 : InnerProductSpace ℝ E] [CompleteSpace E] (delta y : ℝ),
  0 ≤ delta → ∀ (z : E), ConvexOn ℝ Set.univ fun w => P delta (inner ℝ z w - y)
@N12 : ∀ {E : Type u_1} [inst : NormedAddCommGroup E]
  [inst_1 : InnerProductSpace ℝ E] [inst_2 : CompleteSpace E] (delta y : ℝ),
  0 ≤ delta → ∀ (z x : E), ‖gradient (fun w => P delta (inner ℝ z w - y)) x‖ ≤ delta * ‖z‖
@N13 : ∀ {E : Type u_1} [inst : NormedAddCommGroup E]
  [inst_1 : InnerProductSpace ℝ E] [inst_2 : CompleteSpace E] (x : E),
  BanditRL.OnlineGradientDescent.project V x = x
@N14 : ∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : InnerProductSpace ℝ E]
  [CompleteSpace E] (delta y : ℝ),
  0 ≤ delta →
    ∀ (z : E),
      BanditRL.OnlineGradientDescent.RegularLoss V
        (F delta z y)
@N15 : ∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : InnerProductSpace ℝ E]
  [inst_2 : CompleteSpace E] (delta y eta : ℝ),
  0 ≤ delta →
    ∀ (z x : E),
      BanditRL.OnlineGradientDescent.step V eta (F delta z y)
          x =
        x - eta • (if |inner ℝ z x - y| ≤ delta then inner ℝ z x - y else delta * (inner ℝ z x - y).sign) • z
@N16 : ∀ {E : Type u_1} [inst : NormedAddCommGroup E]
  [inst_1 : InnerProductSpace ℝ E] [inst_2 : CompleteSpace E] (delta Z eta : ℝ),
  0 ≤ delta →
    0 ≤ Z →
      0 < eta →
        ∀ (z : ℕ → E) (y : ℕ → ℝ) (x0 u : E) (T : ℕ),
          (∀ t < T, ‖z t‖ ≤ Z) →
            BanditRL.OnlineGradientDescent.regret V eta
                (fun t => F delta (z t) (y t)) x0 u T ≤
              ‖x0 - u‖ ^ 2 / (2 * eta) + eta / 2 * (↑T * (delta * Z) ^ 2) -
                ‖BanditRL.OnlineGradientDescent.iterate V eta
                          (fun t => F delta (z t) (y t)) x0 T -
                        u‖ ^
                    2 /
                  (2 * eta)
@N17 : ∀ {E : Type u_1} [inst : NormedAddCommGroup E]
  [inst_1 : InnerProductSpace ℝ E] [inst_2 : CompleteSpace E] (delta Z : ℝ),
  0 ≤ delta →
    0 ≤ Z →
      ∀ (z : ℕ → E) (y : ℕ → ℝ) (x0 u : E) (T : ℕ),
        0 < T →
          (∀ t < T, ‖z t‖ ≤ Z) →
            BanditRL.OnlineGradientDescent.regret V (1 / √↑T)
                  (fun t => F delta (z t) (y t)) x0 u T /
                ↑T ≤
              (‖x0 - u‖ ^ 2 + (delta * Z) ^ 2) / (2 * √↑T)
@N18 : ∀ {E : Type u_1} [inst : NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] (delta Z : ℝ) (x0 u : E),
  Filter.Tendsto (fun T => (‖x0 - u‖ ^ 2 + (delta * Z) ^ 2) / (2 * √↑T)) Filter.atTop (nhds 0)
@N19 : ∀ {E : Type u_1} [inst : NormedAddCommGroup E]
  [inst_1 : InnerProductSpace ℝ E] [inst_2 : CompleteSpace E] (delta Z : ℝ),
  0 ≤ delta →
    0 ≤ Z →
      ∀ (z : ℕ → E) (y : ℕ → ℝ) (x0 u : E),
        (∀ (t : ℕ), ‖z t‖ ≤ Z) →
          ∀ (epsilon : ℝ),
            0 < epsilon →
              ∀ᶠ (T : ℕ) in Filter.atTop,
                BanditRL.OnlineGradientDescent.regret V (1 / √↑T)
                      (fun t => F delta (z t) (y t)) x0 u T /
                    ↑T <
                  epsilon
P : ℝ → ℝ → ℝ
@V : {E : Type u_1} →
  [inst : NormedAddCommGroup E] → [inst_1 : InnerProductSpace ℝ E] → BanditRL.OnlineGradientDescent.Domain E
@F : {E : Type u_1} →
  [inst : NormedAddCommGroup E] → [InnerProductSpace ℝ E] → ℝ → E → ℝ → E → ℝ

```
