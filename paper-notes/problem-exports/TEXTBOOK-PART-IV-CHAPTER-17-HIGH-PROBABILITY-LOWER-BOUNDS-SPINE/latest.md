# Proof Export: Chapter 17 high-probability lower-bound dependency slice

Task id: TEXTBOOK-PART-IV-CHAPTER-17-HIGH-PROBABILITY-LOWER-BOUNDS-SPINE

Status: synchronized partial proof export. The declarations below compile;
Theorem 17.1, Corollaries 17.2--17.3, Theorem 17.4, Claim 17.6, and
Claim 17.7 do not.

## Compiled Lean declarations

- BanditRLProof.LowerBounds.tailAtLeast
- BanditRLProof.LowerBounds.stochasticHighProbabilityThreshold
- BanditRLProof.LowerBounds.stochasticMinimaxHighProbabilityThreshold
- BanditRLProof.LowerBounds.adversarialHighProbabilityThreshold
- BanditRLProof.LowerBounds.exists_tailMass_ge_of_integral_ge
- BanditRLProof.LowerBounds.exists_cdfTail_ge_of_integral_ge
- BanditRLProof.LowerBounds.measureReal_diff_ge_delta
- BanditRLProof.LowerBounds.adversarialRegretLowerExpression
- BanditRLProof.LowerBounds.adversarialRegretLowerExpression_ge_quarter
- BanditRLProof.LowerBounds.randomRegret_ge_quarter_of_clippingDecomposition

## Natural-language proof map

The three threshold definitions preserve the constants and logarithm arguments
of the source statements. In particular, the factor 1/4 in Theorem 17.1
multiplies the whole minimum, the stochastic minimax threshold uses
log(1/(4 delta)), and the adversarial threshold uses log(1/(2 delta)).

Claim 17.5 is formalized as a first-moment selection argument. If an
integrable tail-mass function has average at least delta under a probability
measure, Mathlib's integral-value witness supplies an instance whose value is
at least the average, hence at least delta. Specializing the function to
x |-> 1 - F_x(u) gives the source CDF-tail statement. Lean exposes the
integrability premise that the textbook leaves implicit.

The probability-combination leaf uses the outer-measure inequality
P(A) - P(B) <= P(A \ B). Thus P(A) >= 2 delta and P(B) <= delta imply
P(A \ B) >= delta, matching the combination of Claims 17.6 and 17.7.
Finally, if the distinguished arm is pulled at most n/2 times and clipping
occurs at most n/4 times, the right-hand side of Eq. (17.8) is at least
Delta n/4; transitivity transfers this lower bound to random regret.

## Exact boundary

The stochastic terminal still needs the same-policy adaptive-history
likelihood-ratio/KL decomposition already blocked in Chapters 15--16. The
adversarial terminal still needs the source's shared-noise clipped-normal
construction, the pull-count testing argument of Claim 17.6, and the clipping
concentration argument of Claim 17.7. The compiled threshold surfaces and
transfer leaves do not assert existence of the hard bandit instance or reward
matrix, and no Chapter 17 source terminal is exported as proved.
