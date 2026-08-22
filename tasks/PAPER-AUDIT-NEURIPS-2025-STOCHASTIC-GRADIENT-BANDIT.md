# NeurIPS 2025 stochastic-gradient-bandit source audit

Task id: `PAPER-AUDIT-NEURIPS-2025-STOCHASTIC-GRADIENT-BANDIT`

Kind: `literaturePort`

Status: `activePort`

Harness: `hierarchical`

## Goal

Compile the finite-action algebra and generated-history Equation-(5) bridge
underlying Algorithm 1 and Equations (3)--(7) of Baudry, Johnson, Vary,
Pike-Burke, and Rebeschini, *Does
Stochastic Gradient really succeed for Bandits?* (NeurIPS 2025). The audit
separates the reusable softmax/update/regret mechanism from the paper's later
learning-rate-dependent stochastic arguments.

## Frozen source

- Source card: `PPR-BAUDRY-JOHNSON-VARY-PIKEBURKE-REBESCHINI-2025-SGB`.
- Official proceedings page:
  <https://proceedings.neurips.cc/paper_files/paper/2025/hash/a4e683f0ce6b91e7fbdae9d32642d88f-Abstract-Conference.html>.
- Official camera-ready PDF:
  <https://proceedings.neurips.cc/paper_files/paper/2025/file/a4e683f0ce6b91e7fbdae9d32642d88f-Paper-Conference.pdf>.
- Official PDF SHA-256:
  `a3aff97fe2179c47fff61cc51453b84a082332e2a205f7fa2268cc68cba73b3d`.
- Source windows: problem and regret on physical PDF p. 1; SGB policy and
  Equations (3)--(7) on pp. 2--3; Algorithm 1 and its gradient verification
  on p. 22.

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

## Semantic boundary

The finite sum over the selected arm is the exact algebra obtained after
conditioning on the pre-action history and replacing the reward by its arm
mean.  The process extension constructs the recursive SGB state, measurable
softmax policy, canonical action/reward trajectory, initial and successor
conditional laws, and the corresponding history-step-kernel integrals under
explicit coordinate-update integrability and arm-reward integral equalities.
It does not package the paper's source-specific reward regularity as a uniform
producer of those hypotheses or prove a learning-rate rate.

## Nonclaims

This task does not compile Theorems 1--4, Lemmas 2--3, any logarithmic or
polynomial regret rate, the sharp two-arm threshold, or the `K`-dependent
learning-rate threshold.  It does not claim the external paper is verified.
It compiles the local finite-action mechanism and a generated process-level
Equation-(5) bridge consumed by those results, while leaving every
learning-rate/failure-probability endpoint open.

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
```

Target files: `BanditRLProof/Algorithms/StochasticGradientBanditAudit.lean`
and `BanditRLProof/Algorithms/StochasticGradientBanditTrajectoryAudit.lean`.

## Gate

```bash
lake env lean BanditRLProof/Algorithms/StochasticGradientBanditAudit.lean
lake env lean BanditRLProof/Algorithms/StochasticGradientBanditTrajectoryAudit.lean
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
- [x] The typed canary compiles; nine representative theorem prints use only
  `propext`, `Classical.choice`, and `Quot.sound`.
- [x] The reference index, proof Blueprint, website, anonymous claim ledger,
  and paper table agree on the 26-plus-18 declaration split and its boundary.
- [x] Full Lean/tests/site gates pass (`8848` Lean jobs; `197` Python tests,
  `4` platform skips; Lean-verified site build/check).
- [x] Independent source/claim review finds no blocking, high, or medium issue.
- [x] The process-level extension above is implemented and compiled.
