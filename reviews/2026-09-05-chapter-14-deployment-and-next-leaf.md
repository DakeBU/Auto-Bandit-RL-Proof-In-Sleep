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

Status: retrieval/proof-route record only; no new Lean theorem is claimed.
Classification: Mathlib-candidate generic identity, with a thin Chapter 14
adapter. The conversion-window and obligation target are unchanged.
