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


## Fixed-horizon adjudication (2026-09-20)

The Eq5 obstruction is now independently adjudicated in
[the finite-horizon proof](GENALTI24-FINITE-HORIZON.md): every measurable policy
has normalized expected pseudo-regret at most2T, uniformly over positive u
and admissible instances. A separate compiled Lean prototype derives that cap
from the actual raw moments. Eq6 necessarily requires a horizon growing with
the scale ratio; no repaired asymptotic lower bound is accepted. The algorithm
root, other constants, and external concentration dependencies above remain
separate unresolved issues. This checkpoint is not whole-paper acceptance.

The subsequent `genalti-supremum-audit.json` checkpoint adds a compiled EReal
supremum non-infinity theorem, actual-process image-law membership, and a
nonempty sharp K2/epsilon1 instance. Independent blind/source reviews accept
the explicit enlarged-class contract; production integration was subsequently accepted in `genalti-production-validation.json`; this historical prototype checkpoint did not itself establish integration.


## Root and guard adjudication (2026-09-20)

[The root/guard derivation](GENALTI24-ROOT-ADJUDICATION.md) gives the complete positive-root classification, a pathwise second-round failure of literal Algorithm1, and a first-request failure even after correcting only the guard logarithm sign. The latter has a finite K2,T1024 admissible witness under explicit indexed-sample semantics retaining repeated observations. The exact unique-root guard uses c=(1+sqrt2)^2 with a strict nonzero-count threshold; equality gives nonunique roots. The numerical doubling factor2 bound requires a relative initial-scale condition, and the integer iteration bound needs rounding. These are separately reviewed mathematical results, not a repaired concentration/regret theorem or Lean implementation. See `runs/extended-topics-20260919/genalti-root-audit.json`.


## Fixed-sample concentration adjudication (2026-09-20)

The [root concentration reconstruction](GENALTI24-ROOT-CONCENTRATION.md) proves Theorem5's constants for the precise intersection of root existence and failure. It supplies root measurability, derives the bounded independent exponential-moment bound, and handles the missing low-population-mass branch. A sparse two-point law with s6 refutes the stronger same-confidence conditional-on-root-existence interpretation; it is not a reachable algorithm-history claim.

The [split-mean reconstruction](GENALTI24-SPLIT-MEAN-CONCENTRATION.md) uses independent n+n observations and a direct uncentered exponential-moment estimate to justify the linear term ML/(3n). Shared root-good accounting gives failure4delta, and converting n to total sample count s=2n preserves the source constant8. The earlier centered-range concern is resolved by this separate proof, not by asserting |Y-EY|<=M. Both results retain explicit event semantics, raw moments and sample multiplicity. The [prefix corollary](GENALTI24-ADAPTIVE-PREFIX-CONCENTRATION.md) transfers these events to measurable adaptive counts in a causal iid paired-stream realization: fixed-arm per-round failure at most4(t-1)/t^3 and at most4 expected exception rounds over a finite horizon. It preserves the extra K cost for an unrestricted selected arm. Empirical-variance index handling, Eq57/counting and full regret remain open. No new Lean result is claimed. Evidence: `runs/extended-topics-20260919/genalti-concentration-audit.json`.
