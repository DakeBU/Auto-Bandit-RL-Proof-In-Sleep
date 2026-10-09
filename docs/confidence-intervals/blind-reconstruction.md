# Independent formal reconstruction: confidence intervals

Decoder identity: `/root/generic_blind_decode`.
Run ID: `generic-blind-decode-20261009-efd2870d-d7f6-4aa9-89a8-e2a410527bab`.
Only input read: `docs/confidence-intervals/formal-packet.md`.
Packet SHA256: `447ad210c92d5963b3052c0b81afbcf82de2af6c4729696ae92b2ac26440bafc`.
Source blind: true. This is a reconstruction, not a source review or acceptance verdict.

## Four declarations

All four are in `BanditRLProof.ConfidenceIntervals`. Scalars are real numbers; finite indices use `Fin K` for a natural number `K`.

### 1. `bias_statistical_composition`

Implicit binders: `{μ ν estimate b s : ℝ}`. Explicit proof arguments, in order: `(hb : |ν - μ| ≤ b)` and `(hs : |estimate - ν| ≤ s)`. Conclusion: `|estimate - μ| ≤ b + s`.

For any three real values and two real upper bounds satisfying those two absolute-error inequalities, the direct error is at most their sum. The intermediate value is `ν`. No probability space, expectation, sample, distribution, or stochastic qualification occurs. The proof is the triangle inequality after writing `estimate - μ = (estimate - ν) + (ν - μ)`.

### 2. `survivors`

This is a `noncomputable def`, not a theorem. Implicit binder: `{K : ℕ}`. Explicit arguments, in order: `(active : Finset (Fin K))` and `(estimate radius : Fin K → ℝ)`. Result type: `Finset (Fin K)`.

Its literal definition is:

```lean
active.filter fun i => ∀ j ∈ active, estimate j - radius j ≤ estimate i + radius i
```

Thus `i` survives exactly when `i ∈ active` and every active index `j` has lower endpoint `estimate j - radius j` at most the upper endpoint `estimate i + radius i`. The comparison includes `j = i`; it uses a non-strict inequality. No nonnegativity condition is imposed by the definition.

### 3. `optimal_survives`

Implicit binder: `{K : ℕ}`. Explicit binders, in order:

```lean
(active : Finset (Fin K))
(μ estimate radius : Fin K → ℝ)
(star : Fin K)
(hstar : star ∈ active)
(hopt : ∀ i ∈ active, μ i ≤ μ star)
(hconf : ∀ i ∈ active, |estimate i - μ i| ≤ radius i)
```

Conclusion: `star ∈ survivors active estimate radius`.

Every active true value is bounded above by the true value at the selected active index `star`, and every active estimate has the stated absolute-error bound. Consequently every active lower endpoint lies below the upper endpoint of `star`, so that selected maximizer survives. The maximizer need not be unique. The hypotheses concern only active indices.

### 4. `large_gap_removed`

Implicit binder `{K : ℕ}`, followed by these explicit and implicit arguments in their actual order:

```lean
(active : Finset (Fin K))
(μ estimate radius : Fin K → ℝ)
(star i : Fin K)
(hstar : star ∈ active)
{r : ℝ}
(hwidth : ∀ j ∈ active, radius j ≤ r)
(hconf : ∀ j ∈ active, |estimate j - μ j| ≤ radius j)
(hgap : 4 * r < μ star - μ i)
```

Conclusion: `i ∉ survivors active estimate radius`.

The selected comparator `star` is active, all active radii are bounded by a common real number `r`, and all active estimates satisfy the confidence inequalities. A strictly greater-than-`4r` true-value gap from `star` to `i` forces removal. Neither active membership of `i` nor global optimality of `star` is assumed. If `i` were a survivor, it would be active, allowing the confidence and width premises to be applied to it. Those bounds would force the lower endpoint of `star` strictly above the upper endpoint of `i`, contradicting the survivor comparison.

## Seven semantic slots, compared using formal content only

| Slot | Composition | Survivors definition | Optimal survives | Large gap removed |
|---|---|---|---|---|
| 1. Quantification | Five implicit reals | Implicit natural `K`; finite active set; two real functions | Implicit `K`; active set; three real functions; selected index | Implicit `K` and real `r`; active set; three functions; two indices |
| 2. Object / literal meaning | Absolute real errors through `ν` | Filter by all active lower-endpoint / candidate upper-endpoint comparisons | Membership in that literal filter | Nonmembership in that literal filter |
| 3. Required premises | Two deterministic absolute-error bounds | None | Selected index active, maximal true value on active set, all active error bounds | Comparator active, all active radius upper bounds and error bounds, strict true gap |
| 4. Claimed result | Error at most `b+s` | A finite subset of active | Selected maximizer retained | Selected candidate excluded |
| 5. Constants / inequality direction | Coefficients one; weak `≤` | Weak `≤`; all comparisons retained at equality | Weak optimality and confidence bounds | Threshold `4*r`; gap must be strict |
| 6. Scope / conventions | Real absolute value; no stochastic interpretation | `Finset (Fin K)`; candidate compared to every active index, including itself | Assumptions only on active set | Comparator need not be optimal; candidate need not initially be active |
| 7. Edge cases / limits | Premises imply `b,s ≥ 0`; no separately stated sign assumptions | Empty active yields empty survivors; negative radii allowed as input | `hstar` excludes empty active and makes `K=0` unavailable; ties allowed; confidence implies active radii nonnegative | `hstar` and confidence/width imply `r ≥ 0`; inactive candidates are already absent; equality of the gap to `4*r` gives no removal claim |

For `r=0`, all active error bounds and widths force exact estimates and zero active radii. The removal theorem then applies to every strictly positive comparator gap. Nothing is asserted about inactive estimates, radii, or true values except where they appear as the candidate gap. For `K=0`, there are no indices to instantiate the last two statements; the definition still accepts the empty active set.

## What these declarations do not prove

They do not establish how an estimate or radius is obtained, that any error bound holds with a particular probability, a uniform-in-time event, concentration, sampling independence, a sample budget, termination, regret, or identification guarantees for an algorithm. They do not prove uniqueness of an optimum, strict separation at the exact `4*r` threshold, that every retained index is optimal, or that every removed index is suboptimal without the displayed comparator and gap premises. The definitions and theorems are bounded deterministic real inequalities and finite-set facts.
