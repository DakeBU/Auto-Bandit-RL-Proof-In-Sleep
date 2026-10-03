# HOO contained packing and near-optimality dimension

This is a partial producer milestone for the repaired Algorithm 1 / Theorem 6 contract, not completion of the Lipschitz topic or the all-ten Goal.

`HOOPacking.lean` implements source Definition 4 literally: disjoint open balls are entirely contained in the target set. A1's finite-scale ambient bound proves the natural supremum is finite and attained for every positive radius. Shrinking balls proves the coarse-scale ambient comparison without adding a metric, symmetry, compactness or an attained reward maximizer. A1 and Lemma 3 at c=2 construct a contained packing from the actual near-optimal nodes at depth h.

`HOODimension.lean` implements Definition 5 in the extended reals with the explicit log(0)=-infinity clarification frozen in commit c88f0c8. Zero packings do not invoke Lean's totalized real logarithm. Positive packings use the exact real logarithmic quotient. The dimension is max(0, limsup as epsilon tends to zero from above), retaining infinite values.

A real d strictly above that dimension gives an eventual bound N(epsilon)<=epsilon^(-d) directly from limsup. A1's smaller-radius ambient packing number supplies the coarse-scale bound. For every finite positive radius cap R, the theorem derives a positive uniform K covering all 0<epsilon<=R. At c=4*nu1/nu2 this yields

    |I_h| <= K * (nu2*rho^h)^(-d)

for every depth h, with K independent of h. The power bound is a conclusion, not a model hypothesis or an assumed confidence/regret premise.

The pre-existing infinite-arm noisy A1/A2 model and expected poor-region visits remain available through the shared public root. This milestone does not yet establish the dimension value for that particular model. It also does not close the actual selected-node regret partition, geometric summation, depth optimization, full expected regret rate or actual/pseudo-regret expectation identity. Independent semantic review, accepted topic mapping and the all-topic ICLR evidence remain pending. No efficiency evaluation or graph-derived discovery claim is made.

Validation is recorded separately in `runs/extended-topics-20260917/hoo-dimension-validation.json`; focused compilation alone must not be described as a joint gate.
