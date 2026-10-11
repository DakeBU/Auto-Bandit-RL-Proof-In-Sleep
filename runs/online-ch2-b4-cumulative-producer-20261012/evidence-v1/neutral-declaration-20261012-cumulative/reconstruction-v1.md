# Source-blind declaration reconstruction

Declaration: `BanditRL.OnlineConvex.cumulative_regularizer_source_strongConvex`. This report decodes only the two supplied text inputs; it supplies no proof, build result, acceptance decision, or source-fidelity verdict.

## Input hashes

- `declaration-v1.txt`: `42189737dd7e6fc527186c17faa33ffc2306e18e931a1da4258819ecc37b6d68`
- `context-v1.txt`: `3591ecf9a0c22104bdb7a201830dae9912f57883a930a7149f75f189b0edc5e5`

## Binder order

```lean
{E : Type*}
[NormedAddCommGroup E]
[NormedSpace ℝ E]
(V : Set E)
(hV : V.Nonempty)
(psi : E → ℝ)
(loss : ℕ → E → EReal)
(n : ℕ)
(lam : ℝ)
(hlam : 0 ≤ lam)
(hpsi : StrongConvexOn V lam psi)
(hbot : ∀ i < n, ∀ x, loss i x ≠ ⊥)
(hdom : ∀ i < n, V ⊆ effectiveDomain (loss i))
(hloss : ∀ i < n, ConvexOn ℝ V (fun x => (loss i x).toReal))
```

## Seven semantic slots

### 1. Objects spaces

E is an arbitrary real normed vector space with its given NormedAddCommGroup norm and NormedSpace structure. V is a subset of E, psi is real valued on all E, loss is a natural-number-indexed family of EReal-valued functions on all E, n is a natural number, and lam is a real number. EReal is the extended real codomain with bottom and top.

### 2. Quantifiers

All declaration parameters are universally quantified, in the binder order recorded below. Prefix hypotheses apply to every natural i < n. The bottom exclusion quantifies every x in E, whereas domain inclusion and loss convexity restrict to V. The final inequality quantifies x in V, then y in V, then a real a with 0 < a and a < 1. The conclusion also has a pointwise formula for every x in V. SourceProper contains a global bottom exclusion and an existential finite-value witness.

### 3. Assumptions

V is nonempty; lam >= 0; psi is StrongConvexOn V lam. By the supplied definitions the latter includes Convex ℝ V and, for x,y in V and real a,b >= 0 with a+b=1, psi(a • x+b • y) <= a*psi(x)+b*psi(y)-a*b*(lam/2)*‖x-y‖^2. For every i < n, loss i never equals bottom anywhere in E; every x in V satisfies loss i x < top; and x ↦ (loss i x).toReal is ConvexOn ℝ V. Thus each prefix loss is finite on V. No separate named convex-set binder exists: convexity of V is already included in hpsi even when n=0.

### 4. Conclusion

For the locally defined F(x) = ((psi(x) : EReal) + sum_{i=0}^{n-1} loss(i,x)) + extendedIndicator(V,x), the theorem gives a four-part conjunction: SourceProper F; effectiveDomain F = V; the displayed finite real-sum identity on V; and the displayed strong-convexity inequality on V for strictly interior a. SourceProper means (∀x, F(x) ≠ bottom) and (∃x, ∃r ∈ ℝ, F(x) = (r : EReal)). Effective domain means {x | F(x) < top}. Combined with properness, domain equality gives exactly the finite-valued locus V, and F(x)=top outside V.

### 5. Constants norm

The modulus is the supplied nonnegative real lam. The correction is the real expression (lam/2)*a*(1-a)*‖x-y‖^2, then embedded in EReal. The norm is precisely the given norm of E used in StrongConvexOn; no alternate norm, equivalent renorming, dual norm, or inner-product norm is introduced. All real-to-EReal coercions and the EReal multiplications/additions/subtraction are those shown in the declaration. No dimension, horizon-dependent scaling, or hidden constant appears.

### 6. Probability

Absent. There is no probability space, randomness, expectation, event, almost-sure qualifier, or probabilistic guarantee.

### 7. Boundary exclusions

n may be zero: the finite sum is empty and zero, all three loss hypotheses are vacuous, and F=psi+extendedIndicator V. Nonemptiness, lam>=0, and StrongConvexOn V lam remain. lam may be zero. x=y is allowed. The final inequality only states 0<a<1, although the psi assumption includes endpoint weights. No empty V is permitted. No completeness, finite-dimensionality, inner product, closedness, boundedness, smoothness, lower semicontinuity, bounded-below assumption, minimizer attainment, strict positive modulus, loss behavior for i>=n, or outside-V loss convexity is assumed or concluded.

## Explicit formulas

Write \(\iota:\mathbb R\to\mathrm{EReal}\) for the finite-value embedding and \(\ell_i(x)=\mathrm{loss}\ i\ x\). Scalar products in E are written without a bullet below.

\[
F(x)=\bigl(\iota(\psi(x))+\sum_{i=0}^{n-1}\ell_i(x)\bigr)+I_V(x),\qquad I_V(x)=\begin{cases}0&x\in V,\\+\infty&x\notin V.\end{cases}
\]

\[
\forall x\in V,\quad F(x)=\iota\!\left(\psi(x)+\sum_{i=0}^{n-1}\operatorname{toReal}(\ell_i(x))\right).
\]

\[
\forall x,y\in V\;\forall a\in\mathbb R,\quad 0<a<1\Longrightarrow F(ax+(1-a)y)\le\iota(a)F(x)+\iota(1-a)F(y)-\iota\!\left(\frac{\lambda}{2}a(1-a)\lVert x-y\rVert^2\right).
\]

The four conjuncts are properness, exact effective domain, the finite identity, and the inequality, in that order.

## Extended-real addition, domain, and properness

The plus signs in F are ordinary EReal addition, left-associated around the regularizer, prefix sum, and indicator. This is not an infimal convolution or a separately defined source-specific sum. The indexed notation ∑ i ∈ range n is the finite sum over natural indices 0 through n-1. Under hbot, each summand is a real value or top everywhere; psi is always finite and the indicator is zero or top. Thus F uses only finite/top additions, with top absorbing in this restricted domain, and no bottom/top mixed addition is needed. On V all prefix losses and F are finite, toReal recovers their genuine real values, and convexity of V keeps ax+(1-a)y in V. Both endpoint values in the concluding inequality are finite and its subtracted correction is finite, so the inequality involves no indeterminate infinity subtraction. The supplied context does not give the implementation of EReal arithmetic or toReal at infinities; no convention for those irrelevant mixed-infinity cases is inferred. Domain inclusion alone would allow bottom because bottom<top; hbot is essential for interpreting the prefix losses as finite on V. Properness is the supplied definition, not a claim of boundedness below or existence of a minimizer.

## Syntax and interpretation limits

No unresolved binding or scope ambiguity was found in the visible declaration. The let binds F across the full conjunction; psi is real-valued and only then embedded; the correction is formed in ℝ before coercion; loss toReal is used only in the convexity hypothesis and finite identity. The supplied context expands StrongConvexOn and UniformConvexOn but not ConvexOn or the EReal implementation. ConvexOn is read in its ordinary Lean mathematical sense of convexity on V, including convexity of V; the independent convexity premise inside StrongConvexOn is explicit in the supplied text. No intended application, external source claim, proof validity, compilation result, or source-fidelity judgment is reconstructed.
