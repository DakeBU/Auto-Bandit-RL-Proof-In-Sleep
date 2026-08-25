# NeurIPS 2025 stochastic-gradient-bandit source audit

Task id: `PAPER-AUDIT-NEURIPS-2025-STOCHASTIC-GRADIENT-BANDIT`

Kind: `literaturePort`

Status: `activePort`

Harness: `hierarchical`

## Goal

Compile the finite-action algebra, generated-history Equation-(5) bridge,
source-exact two-arm rate identities, and bounded-reward exponential-moment
layer underlying Algorithm 1 and
Equations (3)--(11) of Baudry, Johnson, Vary,
Pike-Burke, and Rebeschini, *Does
Stochastic Gradient really succeed for Bandits?* (NeurIPS 2025). The audit
separates the reusable softmax/update/regret mechanism, pathwise zero-sum/odds
structure, and Equation-(8) analytic inequality from the paper's still-open
conditional recurrences and learning-rate-dependent stochastic arguments.

## Frozen source

- Source card: `PPR-BAUDRY-JOHNSON-VARY-PIKEBURKE-REBESCHINI-2025-SGB`.
- Official proceedings page:
  <https://proceedings.neurips.cc/paper_files/paper/2025/hash/a4e683f0ce6b91e7fbdae9d32642d88f-Abstract-Conference.html>.
- Official camera-ready PDF:
  <https://proceedings.neurips.cc/paper_files/paper/2025/file/a4e683f0ce6b91e7fbdae9d32642d88f-Paper-Conference.pdf>.
- Official PDF SHA-256:
  `a3aff97fe2179c47fff61cc51453b84a082332e2a205f7fa2268cc68cba73b3d`.
- Source windows: problem and regret on physical PDF p. 1; SGB policy and
  Equations (3)--(8) on pp. 2--4; Algorithm 1 and its gradient verification
  on p. 22; Appendix A.2 Equations (9)--(11) on pp. 22--23.

## Placement

- Scenario: `SCN-STOCHASTIC-FINITE`.
- Textbook roots: Sutton--Barto Section 2.8 for the gradient-bandit algorithm;
  Lattimore--Szepesvari Chapters 4 and 6 for pseudo-regret and finite
  stochastic-bandit notation.
- Mathlib cards: `MLIB-FINSET-SUMS`, `MLIB-EXP-LOG-INEQUALITIES`,
  `MLIB-ORDER-ALGEBRA`.
- Project interfaces: finite probability vectors and expected-regret algebra.

## Exact first targets

1. Encode the source softmax denominator and sampling probabilities and prove
   positivity, normalization, and strict coordinate positivity.
2. Encode Algorithm 1 / Equation (4)'s selected-arm increment and prove the
   parameter increments sum to zero when the sampling probabilities sum to
   one.
3. Compile Equation (5) as a finite conditional-mean calculation: the
   probability-weighted expected increment equals both the policy-gradient
   coordinate and the instantaneous-gap coordinate.
4. Compile Equation (6)'s finite-horizon best-arm cumulative identity and the
   positive-gap lower bound.
5. Compile Equation (7)'s deterministic regret decomposition into a
   post-convergence parameter term and a squared failure-mass term, with all
   positivity and gap-envelope hypotheses explicit.
6. Record the source learning-rate regimes separately; do not claim Theorems
   1--4 or the stochastic history/kernel bridge in this first audit.

## Active process-level extension

The next non-overlapping target is the generated-history bridge for Equation
(5).  It is deliberately narrower than the paper's rate theorems:

1. Define the recursive parameter vector after an inclusive finite
   action/reward history, with the exact Algorithm-1 update and a fixed
   learning rate.
2. Prove that this state is measurable and induces a measurable finite-action
   softmax policy, including the initial softmax law.
3. Instantiate the repository's `Thompson.HistoryAlgorithm` and canonical
   measurable-environment trajectory kernel with that policy.
4. Identify the generated successor action law and the successor pair law
   given the observed prefix.
5. Under explicit coordinate-update integrability and arm-reward integral
   equalities, prove that the
   conditional one-step source increment agrees with the already compiled
   finite Equation-(5) mean/gap expression.

This extension promotes `SGB-HISTORY` from `blocked` to `partial`: the
recursive process and its Equation-(5) conditional-kernel integrals now
compile, while the source-specific reward regularity and all rate arguments
remain downstream.  It cannot promote `SGB-RATES`, Lemmas 2--3, or Theorems
1--4.  The Lean process accepts a general `initialTheta`; Algorithm 1's source
initialization is the specialization `initialTheta := fun _ => 0`.

## Active two-arm rate-structure extension

The first non-overlapping slice toward Theorem 1 is now compiled without
promoting the theorem endpoint:

1. Prove pathwise that the recursive Algorithm-1 parameter sum equals the
   initial parameter sum on every inclusive finite history.
2. Specialize the source zero initialization and define an explicit
   source-time adapter: Lean time `0` is source `theta_{.,1}`, while Lean time
   `n+1` is the parameter after consuming trace pair `n`.
3. For `Fin 2`, prove that the two coordinates are negatives, the initial law
   is uniform, and the second-arm probability is the complement of the first.
4. Compile the exact softmax odds and its two multiplicative consumers from
   Appendix A.2 Equation (11), both on finite histories and the source-time
   trace adapter.

This closes the pathwise Equation-(9)/(11) structure used at the start of the
Theorem 1 proof. It does not by itself compile either conditional exponential
recurrence, the expected squared failure-mass bound, or the final regret
inequality.

## Active bounded-reward exponential-moment extension

The next independent analytic slice now compiles the exact source constant
and Equation (8), without relabelling a standalone probability integral as a
generated-history conditional theorem:

1. Define `C_eta = 2 * sum_{n >= 0} (2*eta)^n/(n+2)!` and prove the shifted
   series summable.
2. Prove monotonicity of `C_eta` on nonnegative parameters and the source
   comparison `C_eta <= exp(2*eta)`.
3. Split the exponential series after its linear term and identify the tail
   with `q^2/2 * C_(|q|/2)`.
4. Prove the pointwise Equation-(8) inequality for `|reward| <= 1`.
5. Lift it to a probability integral, deriving both reward and exponential
   integrability from almost-everywhere measurability and support in `[-1,1]`.

This closes the source-exact analytic inequality and the monotonicity bridge
needed to compare the varying `C_(a_t/2)` and `C_(b_t/2)` with `C_eta`.
Instantiating Equation (8) on each conditional reward kernel and deriving both
exponential recurrences remain separate obligations.

## Semantic boundary

The finite sum over the selected arm is the exact algebra obtained after
conditioning on the pre-action history and replacing the reward by its arm
mean.  The process extension constructs the recursive SGB state, measurable
softmax policy, canonical action/reward trajectory, initial and successor
conditional laws, and the corresponding history-step-kernel integrals under
explicit coordinate-update integrability and arm-reward integral equalities.
It also exposes the source zero-initialized two-arm parameter/probability
process and exact Equation-(11) odds identity. Separately, it compiles the
source-exact `C_eta` and Equation-(8) inequality for a generic bounded reward
law. It does not package the paper's source-specific reward regularity as a
uniform producer of the Equation-(5) kernel hypotheses, compose Equation (8)
with the generated conditional kernels, or prove a learning-rate rate.

## Nonclaims

This task does not compile Theorems 1--4, Lemmas 2--3, any logarithmic or
polynomial regret rate, the sharp two-arm threshold, or the `K`-dependent
learning-rate threshold.  It does not claim the external paper is verified.
It compiles the local finite-action mechanism and a generated process-level
Equation-(5) bridge, the pathwise Equation-(9)/(11) two-arm structure, and the
standalone bounded-reward Equation-(8) inequality consumed by those results.
The source's conditional recurrences and expected squared
failure-mass estimates and every paper-level rate endpoint remain open.

## Lean target

```lean
BanditRLProof.StochasticGradientBandit.softmaxProbability_sum
BanditRLProof.StochasticGradientBandit.sum_sourceIncrement
BanditRLProof.StochasticGradientBandit.expectedSourceIncrement_eq_gradientCoordinate
BanditRLProof.StochasticGradientBandit.expectedSourceIncrement_eq_gapCoordinate
BanditRLProof.StochasticGradientBandit.bestParameterIncrementSum_ge
BanditRLProof.StochasticGradientBandit.sourceRegretDecomposition_le
BanditRLProof.StochasticGradientBandit.historyParameter
BanditRLProof.StochasticGradientBandit.trajectoryMeasure_condDistrib_action
BanditRLProof.StochasticGradientBandit.trajectoryMeasure_condDistrib_nextPair_given_environment_prefix
BanditRLProof.StochasticGradientBandit.integral_measurableEnvironmentHistoryStepKernel_sourceIncrement_eq_gapCoordinate
BanditRLProof.StochasticGradientBandit.historyParameter_sum_eq_initial
BanditRLProof.StochasticGradientBandit.twoArmParameterAt_sum_eq_zero
BanditRLProof.StochasticGradientBandit.twoArmProbabilityAt_zero
BanditRLProof.StochasticGradientBandit.softmaxProbability_zero_div_one
BanditRLProof.StochasticGradientBandit.twoArmProbabilityAt_zero_div_failure_eq_exp_two_mul
BanditRLProof.StochasticGradientBandit.twoArmProbabilityAt_exp_two_mul_failure_eq_success
BanditRLProof.StochasticGradientBandit.sourceC
BanditRLProof.StochasticGradientBandit.sourceC_le_exp_two_mul
BanditRLProof.StochasticGradientBandit.exp_mul_le_sourceEqEight
BanditRLProof.StochasticGradientBandit.integral_exp_mul_le_sourceEqEight_of_ae_abs_le_one
```

Target files: `BanditRLProof/Algorithms/StochasticGradientBanditAudit.lean`,
`BanditRLProof/Algorithms/StochasticGradientBanditTrajectoryAudit.lean`,
`BanditRLProof/Algorithms/StochasticGradientBanditTwoArmRate.lean`, and
`BanditRLProof/Algorithms/StochasticGradientBanditExponentialAudit.lean`.

## Gate

```bash
lake env lean BanditRLProof/Algorithms/StochasticGradientBanditAudit.lean
lake env lean BanditRLProof/Algorithms/StochasticGradientBanditTrajectoryAudit.lean
lake env lean BanditRLProof/Algorithms/StochasticGradientBanditTwoArmRate.lean
lake env lean BanditRLProof/Algorithms/StochasticGradientBanditExponentialAudit.lean
lake env lean Tests/StochasticGradientBanditPaperAuditCanary.lean
python tools/bandit.py check
```

## Current evidence

- [x] The official PDF is hash-frozen at the SHA-256 above.
- [x] The source equations, pseudo-code, page windows, and scope boundary are
  mapped before Lean proof search.
- [x] The finite source-audit module compiles with 26 named declarations.
- [x] The generated-history extension compiles with 18 named declarations:
  recursive state/measurability, initial and successor softmax laws, the
  canonical pair trajectory, and Equation-(5) history-step-kernel integrals.
- [x] The two-arm rate-structure extension compiles with 18 named
  declarations: the pathwise parameter-sum invariant, explicit source-time
  adapter, zero initialization, initial uniform law, and Equation-(11)
  softmax-odds identities and consumers.
- [x] The exponential-moment extension compiles with 14 named declarations:
  the source `C_eta`, summability, monotonicity and exponential comparison, the exact
  Equation-(8) tail identity, and pointwise/integral bounded-reward forms.
- [x] The typed canary compiles; twenty representative theorem prints use only
  `propext`, `Classical.choice`, and `Quot.sound`.
- [x] Refresh the reference index, proof Blueprint, website, and anonymous
  claim ledger to agree on the 26-plus-18-plus-18-plus-14 declaration split
  and its boundary.
- [x] Refresh the separate paper repository's arXiv and ICLR audit tables,
  abstracts, evidence summaries, and limitations to the same 76-declaration,
  four-layer boundary; both PDFs and curated source-package tests pass.
- [x] Re-run the full gates after the new layer and evidence refresh:
  `lake build` completed 8,836 jobs, `lake build Tests` completed 8,862 jobs,
  `python tools/bandit.py check` passed 232 tests with 6 designed skips, and
  the Lean-verified site/check covered 642 pages, 7,876 declarations, 17,021
  Lean source links, 14 Mermaid blocks, and valid internal links, anchors,
  formula fallbacks, and deployment workflow.
- [x] Independent source/claim reviews of both the two-arm and Equation-(8)
  layers find no blocking, high, or medium issue.
- [x] The process-level extension above is implemented and compiled.
