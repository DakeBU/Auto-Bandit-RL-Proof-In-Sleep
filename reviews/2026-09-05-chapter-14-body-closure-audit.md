# Chapter 14 body closure audit

## Scope and evidence

Re-read the local author-text extraction through the end of the proof on
author pp.186-191 (physical pp.195-200), stopping before Notes. The task's
goal requires every mathematical body claim to be mapped or explicitly open.
The old table's treatment of metric counterclaims as explanatory nonclaims
is not sufficient evidence of whole-body closure.

Current arithmetic full check: commit 2a31a01, running in C:/a14,
log `tmp/ch14-arithmetic-full-check.log`. Do not infer completion from imports.
Verified existing logs: affinity at b8325c2 (400 tests, 7 skipped, 190.612s),
Gaussian/coding at 1e8af14 (400 tests, 7 skipped, 187.291s). Huffman full gate
at dff13cb is recorded in its route log (400 tests, 7 skipped, 183.908s).

## Main terminal coverage

- Eq.14.1 and Eq.14.2: recursive huffmanOptimalCode, huffmanCode_optimal,
  huffmanCode_entropy_sandwich; the old Eq.14.1 'no optimum' row is stale.
- Arithmetic coding: actual affine interval/dyadic address construction,
  prefix-free support code, explicit zero-mass escape tag, finite overhead 3,
  arithmeticBlockCode_rate_tendsto_entropy. Exact-real classical construction,
  not executable finite-precision coding. Full gate pending.
- Converse: sourceBlock_code_rate_lower_bound and
  sourceBlock_code_family_limit_ge_entropy apply to every local prefix code.
- Eqs.14.4-14.9 and Gaussian/testing example: compiled terminals exist;
  old conversion-window Gaussian/overlap gaps are stale, not new proof gaps.
- Source affinity proof route is covered by integral Jensen and L2 bounds,
  not only by the alternative binary-event proof.

## Additional body assertions requiring resolution

1. Fixed-length coding at ceil(log2 N): binaryAddress representation is
   available, but the exact source-mapped alphabet/cardinality wrapper is
   not yet identified. N=1 conflicts with allowing empty words versus the
   local explicit nonempty-word convention; retain a stated boundary.
2. 'Uniform code is recovered': do not assert that uniform length is globally
   optimal for arbitrary N. For N=3, a binary tree with lengths 1,2,2 has
   mean 5/3, below the constant two-bit code. Resolve as a qualified source
   interpretation (power-of-two case), not a false theorem.
3. Zero-mass entropy explanation: sum terms at zero are handled; the displayed
   right-limit x log(1/x) -> 0 still needs a source-mapped adapter or exact
   verified existing declaration.
4. Eq.14.4 starts with cross-entropy minus entropy, after explicitly dropping
   rounding. The finite KL log-ratio terminal exists, but identify/prove this
   algebraic first equality with support conditions. Do not claim exact code
   length differences for rounded Huffman/Shannon codes.
5. Non-symmetry and triangle-inequality failure: need actual counterexample
   declarations/canaries. No such source-mapped local declarations were found
   in the current information-theory files/index search. Keep as open rather
   than silently exclude them from required mathematical body claims.
6. Common domination by P+Q and finite support iff finite KL: inspect exact
   available adapters/canaries before deciding whether a wrapper is missing.

## Evidence closure remaining

Conversion window, obligation ledger and exports contain stale milestone
claims. Historical accepted/site/remote rows refer to a narrower earlier
scope, not current whole-body verification. Detailed Markdown/LaTeX exports,
site content/build/render and any required publication evidence must be
synchronized after proof coverage is settled. No whole-chapter promotion is
justified by this audit. Decision remains partial; goal remains active.

## Follow-up: metric counterclaims

RelativeEntropyNonMetric now supplies two focused-compiled source witnesses:
Bernoulli asymmetry at 0 versus 1/2, and Gaussian triangle failure for means
0,1,2 with common variance 1. The latter has three finite KL values. See
`reviews/2026-09-05-chapter-14-metric-route.md`. This resolves the identified
local proof gap for item 5, but not its pending aggregate/export verification.

## Follow-up: cross entropy and zero limit

CrossEntropy now provides focused-compiled `relativeEntropy_finite_crossEntropy`
and `entropyTerm_tendsto_zero_right`, resolving the local proof gaps in items
3 and 4. The real cross-entropy identity has the required support/AC premise;
it does not apply to singular infinite KL and does not claim an exact rounded
code-length difference. Aggregate and export synchronization remain pending.
