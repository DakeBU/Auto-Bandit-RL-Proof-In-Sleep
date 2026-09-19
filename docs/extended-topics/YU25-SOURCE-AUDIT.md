# Yu et al. UAI 2025: scope and local proof audit

Source: Corruption-Robust Variance-aware Algorithms for Generalized Linear
Bandits under Heavy-tailed Rewards, PMLR244, pp4826-4843.
Pinned PDF SHA256: 1613cdda48c005f3fe094f95747413deac90b7b604c6ba7af41c8ee4a33824f1.
Independent source reviewer A inspected the entire locally supplied mathematical
proof material, including appendices A-D. The originally cited Li-Sun2024 published version, code and errata remain
unverified. A later dependency audit inspected the distinct Li-Sun2023v2
preprint and derived an explicitly changed confidence contract; see below. This is not a complete
transitive proof certification or Lean acceptance.

The model assumes finite conditional noise variance, predictable variance bounds,
a known horizon and corruption budget, bounded features/parameter, and an
increasing GLM link with derivative bounded above and away from zero. The
algorithm uses constrained pseudo-Huber integral regression and optimistic
matrix confidence sets. It does not cover arbitrary infinite-variance raw
(1+epsilon)-moment rewards and does not replace BCL's scalar source target.
Its guarantee is high-probability pseudo-regret, not expected realized regret.

The conditional regret summation checks given the confidence statements, but:
- p4838 auxiliary clean loss prints a plus integral, opposite Eq2; the minus
  sign is needed for its gradient and strong convexity argument.
- Generic standardized residuals are not conditionally mean zero; this holds
  only at the true predictor. Hessian derivative evaluation also has a typo.
- Central score and uniform-curvature proofs are outsourced to Li-Sun2024.
  A deterministic linear-to-GLM curvature adapter and a repaired finite-horizon
  confidence proof are now independently reviewed as mathematics; the original
  probability contract and exact published-version transfer remain unverified.
- The corruption budget must be supplied predictably, not set to a future
  realized random total. Unknown-budget adaptation is not proved locally.
- Zero actions need a convention for the displayed division by zero; t=0
  needs its separately stated radius; optimization needs attainment conditions.

These are scoped proof/specification gaps, not a blanket false-theorem claim.
The finite-variance Student-t(3) experiment does not broaden the theorem to
infinite variance. No independent experimental reproduction was performed.
Detailed independent evidence, rendered-page checks and excluded scope are in
private review-20260919/yu25-full-audit.md; its hash belongs in the run receipt.

## Transitive dependency audit: explicit mathematical repair

The independently retrieved Li-Sun preprint is arXiv:2303.05606v2,
13 March2023, *Variance-aware robust reinforcement learning with linear
function approximation under heavy-tailed rewards*. Its PDF SHA256 is
44baf2c55a0039c9b06295ee2d687c6b8ceb7e83d0b8fea5d92767414e46167d.
This is not yet established to be identical to the cited TMLR2024 paper.
Appendix B.3-B.6 and the exact F.1 interface were inspected, including rendered
formula checks.

The GLM residual difference is controlled by 2KLB/sigma. The scale containing
sqrt(KLB) then controls the squared residual perturbation and yields the
regularized Hessian lower bound kH/4 on the true-residual concentration event.
No conditional centering is assumed away from the true parameter.

The preprint score-bias summation loses a factor2; retaining it still fits the
alpha=8 stopping envelope. Its displayed per-time union budgets do not prove
the advertised delta/2 allocations. A separate finite-horizon repair supplies
explicit curvature, stopped cross-term and quadratic-term events, then closes
the first-violation and constrained-minimizer arguments. The zero-noise branch
is handled directly, and zero features have a finite tau convention.

This is an explicitly changed mathematical contract: log6 replaces log2,
score radii use prefix kappa, the regularization remainder is derived as4,
and the total failure allocation is newly proved. The tau0 condition is
derived from the scale calculation rather than conflating the preprint's
main-text LB factor with its appendix formulation. Predictable scales need
only satisfy stated lower bounds, not the original exact maximum rule. C1
link regularity and the all-constrained-minimizers quantifier are explicit.
Independent mathematical repair/source-scope reviews and the detailed private
derivation are hash-bound in
`runs/extended-topics-20260919/glm-confidence-audit.json`.

No Lean implementation, original-log2 confidence certification, corrupted
policy regret, published-version equivalence, or complete heavy-topic
acceptance follows from this audit. These findings do not replace the frozen
BCL actual-policy performance and finite-counterexample endpoint.
