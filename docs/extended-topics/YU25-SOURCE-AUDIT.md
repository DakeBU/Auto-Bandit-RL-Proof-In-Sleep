# Yu et al. UAI 2025: scope and local proof audit

Source: Corruption-Robust Variance-aware Algorithms for Generalized Linear
Bandits under Heavy-tailed Rewards, PMLR244, pp4826-4843.
Pinned PDF SHA256: 1613cdda48c005f3fe094f95747413deac90b7b604c6ba7af41c8ee4a33824f1.
Independent source reviewer A inspected the entire locally supplied mathematical
proof material, including appendices A-D. External Li-Sun2024 concentration and
curvature proofs, code and errata were not audited. This is not a complete
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
- Central score and uniform-curvature proofs are outsourced to Li-Sun2024;
  the exact linear-to-GLM curvature transfer remains unverified here.
- The corruption budget must be supplied predictably, not set to a future
  realized random total. Unknown-budget adaptation is not proved locally.
- Zero actions need a convention for the displayed division by zero; t=0
  needs its separately stated radius; optimization needs attainment conditions.

These are scoped proof/specification gaps, not a blanket false-theorem claim.
The finite-variance Student-t(3) experiment does not broaden the theorem to
infinite variance. No independent experimental reproduction was performed.
Detailed independent evidence, rendered-page checks and excluded scope are in
private review-20260919/yu25-full-audit.md; its hash belongs in the run receipt.
