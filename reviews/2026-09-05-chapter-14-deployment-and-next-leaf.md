# Chapter 14 deployment verification and finite-alphabet continuation

## Verified remote evidence

PR #103 merged as `5c0ba47fbf600ef2e8592c60cc179b0df0df9bf7`.
Authoritative-main workflow `33842361700` completed successfully: build job
`100927076747` passed library/Tests, protocol validation, website generation,
link/formula checks, and artifact upload; deploy job `100932269095` passed.
The build finished at 2026-09-04 06:23:06 UTC and deployment at 06:23:20 UTC.

On 2026-09-05 the public Chapter 14 URL returned HTTP 200 and contained
`relativeEntropy_trim_le`, `kraft_inequality`, the arbitrary finite-alphabet
gap, and the whole-chapter coverage label. This is content/deployment
verification; desktop/mobile visual inspection remains the earlier local
verification documented in the extension review.

The merged slice does not satisfy all required body rows. Whole-chapter
coverage remains `partial`, and the overall formalization goal remains active.

## Next required leaf: Eq. (14.4)

Source: `TXT-LATTIMORE-SZEPESVARI-2020`, Chapter 14 Eq. (14.4).
Target: for arbitrary finite alphabets with measurable singletons and
probability measures P and Q, identify measure KL with the finite sum
of p(x) log(p(x)/q(x)) when Q has no zero atom of positive P mass;
otherwise obtain infinity. Zero-P terms must contribute zero.

Retrieval on the installed Mathlib found `integral_fintype` in
`Mathlib.MeasureTheory.Integral.Bochner.SumMeasure`,
`Measure.withDensity_rnDeriv_eq` and `Measure.withDensity_apply`, and
`InformationTheory.klDiv_of_ac_of_integrable` / `klDiv_of_not_ac`.
Searches for `finiteDiscrete` in task memory and local declaration statements
returned no hits. No generic discrete-KL identity was found in KL Basic.

Route: derive atomwise absolute continuity from the finite atomic measure
decomposition; identify the RN density through its with-density measure on
singletons; prove finite-domain log-likelihood integrability under finite
measures; expand the integral using `integral_fintype`; and use probability
normalization to remove Mathlib's finite-measure mass correction.
The singular branch must be proved from an actual positive-P/zero-Q atom.

Initial status: retrieval/proof-route record only.
Classification: Mathlib-candidate generic identity, with a thin Chapter 14
adapter. The conversion-window and obligation target are unchanged.

## Local proof progress

`BanditRLProof/LowerBounds/FiniteDiscreteKL.lean` now passes direct
`lake env lean` checking. It proves the RN atom identity, the density ratio
on nonzero reference atoms, the singular support-mismatch branch, the finite
`klFun` sum, and the probability-measure sum of `p log(p/q)` under absolute
continuity. Integrability follows from `SimpleFunc.ofFinite`; zero source
atoms are simplified separately, without a strict-positivity assumption.

This is focused evidence only. The atomwise-support/absolute-continuity
equivalence, regression canary, root integration, full harness and synchronized
chapter evidence are still pending. Whole-chapter status remains partial.

## Support characterization and integration attempt

The same finite-atomic route uses `sum_measure_singleton` and
`measure_mono_null` to prove absolute continuity equivalent to atomwise
support inclusion. This supplies an exhaustive finite-sum/infinity statement
and an infinity-iff-support-mismatch theorem. Root import and three-symbol
endpoint canaries have been added for validation. The first direct check
reported only an ambiguous `not_imp` name. The corrected version passed;
the compiler identified that simp argument as unnecessary, so it was removed.
The root integration and canaries still require verification.

The short-path validation checkout `C:\a14` built the root library at
`e218fb6` successfully (root module: 129 seconds). Its first Tests pass found
two parsing errors for the infinity notation in the new root-import canary;
the explicit `(⊤ : ENNReal)` spelling fixes those statements without changing
their meaning. The corrected canary also directly exercises the finite-sum
formula on a three-symbol Dirac law and prints all eight new declarations'
axiom dependencies. These final canary changes are at `9d4b44a`.

The primary long-path `python tools/bandit.py check` attempt failed while
writing the unrelated long-named RL cumulative-average-rate `.olean`, matching
the existing Windows path limitation. It did successfully build
`FiniteDiscreteKL`. The full gate must be rerun in the short checkout; the
failed long-path invocation is not a completed full gate.

Direct root-import canary checking at `9d4b44a` subsequently passed (exit 0),
including the three-symbol finite-sum calculation and singular example.
All eight new declarations report only `propext`, `Classical.choice`, and
`Quot.sound`. Eq. (14.4) is therefore locally compiled and canaried; the
full-check rerun and website/export synchronization remain distinct gates.

The short-path full check at `9d4b44a` subsequently passed the library build,
the complete Tests build (8,895 jobs), the proof-graph exporter Lean check,
and the forbidden-placeholder scan. The Python suite was still running at
this checkpoint. Its log is `C:\a14\tmp\ch14-finite-kl-full-check.log`.
No full-check completion or remote deployment is claimed for this slice yet.

## Completed finite-alphabet local gate

The short-path `python tools/bandit.py check` at `9d4b44a` finished with exit
0: library, Tests (8,895 jobs), proof-graph exporter Lean check, forbidden
placeholder scan, and 400 Python tests (7 skipped, 183.530 seconds) all passed.
The earlier in-progress checkpoint above is superseded by this final result.
No Lean source has changed since that gate. Markdown/LaTeX exports, source
cards, README, theory tree, and website content now include the finite-alphabet
formula and retain the other whole-chapter gaps. Site verification follows
separately; no remote publication of this slice is claimed.

The updated local site then passed `build_site.py --lean-verified` and
`check_site.py`: 659 pages, 605 modules, 8,232 declarations, zero placeholders,
and valid internal links, anchors, and mathematical fallbacks. The generated
Chapter 14 page includes the three finite-alphabet terminal declarations with
exact Lean statements and retains the whole-chapter `Partial` label. This is
local generated-site evidence, not browser layout QA or remote deployment.

Next required mathematical leaf: Eq. (14.5), the supremum over finite
measurable discretisations and its equality with RN KL. A search for KL
supremum/partition/map identities in the installed Mathlib information-theory
directory found no direct adapter. The existing arbitrary-sub-sigma-algebra
DPI can provide one inequality, but not the supremum-attainment/approximation
direction. This dependency remains explicitly open rather than being inferred
from finite Eq. (14.4).
