# Independent-review repair: arbitrary-event overlap

Read-only independent review of 2bd82f7 found a P2 source-proof coverage gap:
the p.191 sufficiency step requires overlap <= P(A)+Q(A complement) for
every measurable A, whereas the existing local adapter only gives equality
at the likelihood-comparison event. Existing BH remains valid but does not
substitute for the frozen requirement to map every source proof claim.

Target: `commonDensityOverlap_le_testingError`, finite P,Q dominated by a
sigma-finite common measure, arbitrary measurable A. No new target assumptions.
Route: split the integral of min across A/complement using
`integral_add_compl`; apply `integral_mono` with min_le_left/right on restricted
measures; finish with `Measure.setIntegral_toReal_rnDeriv`. Existing
`integrable_min_commonDensity` and RN-density integrability discharge all
integrability obligations. This general finite-measure leaf is a
Mathlib-candidate; no new dependency is required.

Canary: chain squared-affinity/KL, Le Cam overlap and the new arbitrary-event
bound, for arbitrary probability measures and common domination. Also typecheck
the source reversed-KL remark by swapping P,Q and complementing A.

Validation pending; independent review must recheck the final compiled diff.
