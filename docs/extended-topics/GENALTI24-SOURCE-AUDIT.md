# Recent heavy-tail source audit: Genalti et al., COLT 2024

Source: *[epsilon,u]-Adaptive Regret Minimization in Heavy-Tailed Bandits*,
Genalti, Marsigli, Gatti and Metelli, PMLR247 (2024).
Frozen PDF SHA256: `65eceb2cd402baa8c7f5b60d273a103fbd181cf6803a4b7f0d2f4092742fe5b6`.

The independent source reviewer read the model, algorithms and all locally
supplied proofs of Theorems2-8, Proposition9 and the numerical appendix
(pp17-34), with consequential formulas checked on rendered pages. This is a
full reading of the supplied main proofs, not a claim that those statements
passed semantic acceptance. Externally cited concentration/lower-bound proofs,
any later errata/code and the full bibliography were not independently audited.

The positive unknown-parameter results impose truncated non-positivity of the
signed discarded tail on an optimal arm at every threshold. This is a material
restriction absent from our known-parameter raw-moment target. The estimator
also uses a data-dependent common threshold, independent sample splitting and
an empirical-variance index. Its result cannot simply substitute for the
sample-ordinal truncation algorithm formalized here.

The review records the following literal-source obstructions for adjudication:

- Theorem2 Eq5's fixed-T normalized infinite supremum conflicts with the
  elementary raw-moment implication |mu_i|<=u^(1/(1+epsilon)), hence normalized
  regret<=2T. Its proof uses a sufficiently-large-T condition depending on the
  scale ratio before letting that ratio diverge. Reordered asymptotic
  nonadaptivity claims are a separate question, not refuted by this diagnosis.
- Algorithm1's displayed nonzero-count guard contains log(tau^-3), negative
  for tau>1. Even changing the sign leaves a guard coefficient4 below the
  positive-root requirement c=(1+sqrt2)^2. Literal root existence is not ensured.
- Theorem7's Eq57 threshold coefficient20 yields a 20^q factor with
  q=epsilon/(1+epsilon), while the subsequent proof uses20. Exact constants
  need adjudication; the intended rate is not thereby disproved.
- The numerical root approximation needs an explicit step-size/root condition
  for the printed twice-root bound. Odd horizons and adaptive split-sample
  concentration require their stated conventions to be checked.

These are source-audit findings, not new Lean impossibility theorems or claims
of an author-issued correction. The complete review retains assumptions,
anchors, derivations and additional qualifications. Other recent papers in
SOURCE-AUDIT.md remain screened-only until separately read in full.

Private report: `E:/ABRL/maintenance/extended-topics-20260919-claude/review-20260919/genalti24-full-audit.md`.
Report SHA256: `a575ee6a9af373171a8060da3cb027a8f133d960245def164d0029a76a3c5a76`.
