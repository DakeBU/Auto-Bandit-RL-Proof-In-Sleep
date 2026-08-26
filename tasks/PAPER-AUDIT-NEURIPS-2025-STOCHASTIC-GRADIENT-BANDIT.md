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
structure, Equation-(8) analytic inequality, generated conditional kernels,
two-arm recurrence interfaces, and the paper's exact two-arm Theorem 1
endpoint.  Theorems 2--4 and the general-`K` learning-rate regimes remain
outside the compiled boundary.

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

This extension promoted `SGB-HISTORY` from `blocked` to `partial`: the
recursive process and its Equation-(5) conditional-kernel integrals compile.
The fixed-IID source-contract and bounded-support layers below close the fixed
two-arm law-to-environment-contract producer and derive the generated-history
`Integrable sourceIncrement` premise.  At that stage global recurrence
iteration and every rate argument remained downstream; the later final layer
below now promotes only Theorem 1.  It does not promote `SGB-RATES`, Lemmas
2--3, or Theorems 2--4.  The Lean process accepts a general `initialTheta`;
Algorithm 1's source
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
The generic probability-law theorem remains a distinct analytic layer; the
generated-kernel instantiation is supplied by the next extension rather than
being silently inferred here.

## Active generated-kernel and two-arm recurrence extension

Four declarations now instantiate Equation (8) on the generated initial and
successor reward kernels under explicit bounded-support and fixed-mean
hypotheses.  Ten further declarations compile the exact forward and inverse
two-arm successor algebra at a fixed history, including the additive
success/failure-square recurrence forms, while three declarations fix the
source zero initialization and both time-one recurrence bounds.

These are generated-kernel and fixed-history results.  They do not by
themselves identify a global conditional expectation on the full trajectory
or iterate either recurrence through time.

## Active measurable trajectory recurrence extension

Twenty-five declarations package a
`TwoArmBoundedFixedMeanEnvironmentContract`, measurable forward/inverse
potentials and bounds, the canonical two-arm trajectory and prefix
filtration, and almost-everywhere conditional-distribution transports for both
successor recurrences.  The contract fixes support in `[-1,1]` and the two arm
means at every initial/successor fiber.  The fixed-IID adapter below realizes
the source model as a specialization, but this is not an equivalent fixed-`nu`
encoding: the broader contract also permits history-varying conditional laws
with the same support and means.

For a general prior, the prefix used here contains the latent environment, so
the filtration is environment-revealed.  A fixed/Dirac environment recovers
the fixed-instance reading used in the source theorem.

## Active fixed-horizon path-integrability extension

Nineteen declarations derive the initial contract wrappers, transport reward
support to every finite trajectory coordinate and prefix, bound the recursive
source parameter, identify the two exponential potentials, prove both
fixed-horizon potentials integrable, identify conditional expectation with
the conditional-distribution integral, expose tower-ready forward and inverse
conditional recurrence bounds, and derive initial/successor
`Integrable sourceIncrement` directly from bounded support.

This closes the fixed-horizon integrability and one-step conditional-
expectation boundary.  Those operations are not proved by this layer itself;
the later recurrence and terminal layers provide them.

## Active fixed-IID source-contract extension

Nine declarations (two definitions and seven theorems) now realize the fixed
two-arm source assumptions as a stationary history environment over `Unit`.
They define the arm-indexed reward kernel and environment, identify every
initial and successor feedback fiber with the selected arm law, supply reward
measurability, and prove
`twoArmFixedIIDEnvironment_contract`.  The final theorem maps probability
laws with a.e. support in `[-1,1]` and the stated integral means into the
existing `TwoArmBoundedFixedMeanEnvironmentContract`.

This is a one-way source-law-to-contract bridge.  It neither states nor proves
that every history-dependent environment satisfying the broader contract is
fixed IID.  The final fixed-IID theorem reuses the generic bounded-support
integrability leaf to compile Equation (5)'s successor-history gap-coordinate
identity without a caller-supplied integrability premise.  The iterated
conditional recurrences and regret endpoint are supplied only by the later
recurrence and Theorem-1 layers.

## Active bounded-support Equation-(5) integrability extension

This compiled leaf is the direct bounded-support corollary exposed by the
preceding source adapter.  It transports
`|reward| <= 1` through the generated initial and successor pair kernels,
combines it with the compiled pointwise inequality
`|sourceIncrement| <= |reward|`, and derives `Integrable sourceIncrement`.
The fixed-IID wrapper then invokes the existing Equation-(5) gap-coordinate
identity without a caller-supplied integrability premise.

This leaf uses `MLIB-MEASURE-INTEGRAL` and `MLIB-PROBABILITY-KERNEL` and adds
no new moment, independence, or reward-regularity assumption.  The generic
bounded fixed-mean contract is sufficient; the fixed-IID environment is the
paper-exact downstream specialization.  These three declarations do not by
themselves perform global tower iteration, prove Equation (7), or promote
Theorem 1.

## Active unconditional recurrence and failure-mass extension

Thirty-seven declarations now integrate the tower-ready conditional bounds,
iterate the resulting scalar forward and inverse recurrences, bridge the
normalized initial pair, and prove the source-indexed failure-mass estimate

`1 / 4 + sum n in range N, E[(1 - p_(n+2))^2]
  <= 1 / (2 * eta * (Delta - eta * sourceC eta))`.

The extra `1 / 4` is the uniform source round `t = 1`; Lean prefix index `n`
corresponds to source parameter/probability time `n + 2`.  The final estimate
uses only `0 < eta`, `eta * sourceC eta < Delta`, the existing bounded
fixed-mean contract, and a probability prior.  No independence, MGF, or extra
moment assumption is added.

This extension closes the generic unconditional one-step recurrences, finite
iteration, inverse telescope, normalized initial bridge, and expected squared
failure-mass sum.  The final layer below consumes this result to close the
remaining Theorem-1 route.

## Compiled Theorem-1 endpoint

Thirty-two declarations now close the exact source endpoint rather than a
probability-schedule proxy:

1. identify the generated conditional source increment with
   `Delta * p * (1-p)` and integrate the Equation-(5) tower;
2. telescope the expected best-arm parameter, including the exact initial
   `Delta / 4` term;
3. bound the forward exponential potential and apply Jensen/log with the
   source horizon `T = tailHorizon + 1`;
4. define finite pseudo-regret from the actions actually sampled on the
   generated trajectory and identify its expectation through the initial and
   successor conditional action laws;
5. assemble Equation (7) with the compiled failure-square estimate; and
6. specialize the whole chain to fixed armwise IID reward laws under a Dirac
   environment prior.

The terminal `twoArmFixedIIDDirac_theoremOne` retains the source assumptions
`0 < Delta < 1`, `0 < eta`, and `eta * sourceC eta < Delta`, and proves the
source right-hand side

`log (1 + 4 * eta * Delta * T) / (2 * eta)
  + Delta / (2 * eta * (Delta - eta * sourceC eta))`.

This closes Theorem 1 only.  It does not promote Theorems 2--4 or the whole
paper.

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
law. The fixed-IID source adapter derives the existing bounded fixed-mean
contract from fixed two-arm probability laws with support and integral-mean
hypotheses; the bridge is deliberately one-way rather than an equivalence.
The generic bounded-support wrapper now closes the separate generated-history
`Integrable sourceIncrement` premise and a fixed-IID consumer compiles the
resulting one-step Equation-(5) gap identity.
The generated-kernel,
fixed-history, measurable-trajectory, fixed-horizon integrability, and
tower-ready one-step conditional-expectation statements now feed compiled
unconditional recurrences, finite scalar iteration, and a source-indexed
expected squared failure-mass estimate.  The expected-parameter/Jensen bridge,
fixed-IID/Dirac specialization, Equation-(7) generated-regret assembly, and
actual sampled-action bridge now compile in the final layer.  The remaining
learning-rate endpoints stay open.

## Nonclaims

This task compiles Theorem 1 but not Theorems 2--4, Lemmas 2--3 beyond any
locally reused ingredients, the sharp two-arm threshold, or the general-`K`
learning-rate threshold.  It does not claim the external paper is verified.
It compiles the local finite-action mechanism, the generated process-level
Equation-(5)/(8) bridges, the pathwise Equation-(9)/(11) two-arm structure,
initial and fixed-history recurrence inequalities, their measurable
conditional-distribution transport, and fixed-horizon integrable
conditional-expectation forms, together with the fixed-IID source-law-to-
environment-contract bridge and bounded-support Equation-(5) integrability
wrappers.  The generic unconditional recurrences, finite iteration, normalized
initial mixture, and expected squared failure-mass estimate also compile.
The final 32-declaration layer closes the expected-parameter/Jensen consumer,
fixed-IID/Dirac specialization, actual sampled-action bridge, Equation-(7)
terminal assembly, and exact Theorem-1 bound.  Every other paper-level rate
endpoint remains open.

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
BanditRLProof.StochasticGradientBandit.integral_measurableEnvironmentHistoryStepKernel_exp_actionReward_le_sourceEqEight_of_mean
BanditRLProof.StochasticGradientBandit.integral_twoArmHistoryStepKernel_exp_forwardSuccessor_le_add_success_sq
BanditRLProof.StochasticGradientBandit.integral_twoArmHistoryStepKernel_exp_inverseSuccessor_le_sub_failure_sq
BanditRLProof.StochasticGradientBandit.integral_twoArmInitialPairKernel_exp_forwardIncrement_le
BanditRLProof.StochasticGradientBandit.integral_twoArmInitialPairKernel_exp_inverseIncrement_le
BanditRLProof.StochasticGradientBandit.TwoArmBoundedFixedMeanEnvironmentContract
BanditRLProof.StochasticGradientBandit.trajectoryPrefix_condDistrib_integral_forwardSuccessor_le
BanditRLProof.StochasticGradientBandit.trajectoryPrefix_condDistrib_integral_inverseSuccessor_le
BanditRLProof.StochasticGradientBandit.integrable_twoArmForwardTrajectorySuccessorPotential
BanditRLProof.StochasticGradientBandit.integrable_twoArmInverseTrajectorySuccessorPotential
BanditRLProof.StochasticGradientBandit.twoArmForwardTrajectorySuccessor_condExp_le_recurrenceBound
BanditRLProof.StochasticGradientBandit.twoArmInverseTrajectorySuccessor_condExp_le_recurrenceBound
BanditRLProof.StochasticGradientBandit.integrable_measurableTwoArmInitialPairKernel_sourceIncrement_of_contract
BanditRLProof.StochasticGradientBandit.integrable_measurableTwoArmHistoryStepKernel_sourceIncrement_of_contract
BanditRLProof.StochasticGradientBandit.twoArmFixedIIDRewardKernel
BanditRLProof.StochasticGradientBandit.twoArmFixedIIDRewardKernel_apply
BanditRLProof.StochasticGradientBandit.twoArmFixedIIDRewardKernel_isMarkov
BanditRLProof.StochasticGradientBandit.twoArmFixedIIDEnvironment
BanditRLProof.StochasticGradientBandit.twoArmFixedIIDEnvironment_initialFeedback_apply
BanditRLProof.StochasticGradientBandit.twoArmFixedIIDEnvironment_feedback_apply
BanditRLProof.StochasticGradientBandit.twoArmFixedIIDReward_aestronglyMeasurable
BanditRLProof.StochasticGradientBandit.twoArmFixedIIDEnvironment_contract
BanditRLProof.StochasticGradientBandit.integral_twoArmFixedIIDHistoryStepKernel_sourceIncrement_eq_gapCoordinate
BanditRLProof.StochasticGradientBandit.twoArmTrajectorySourceIncrement_condExp_ae_eq_successFailure
BanditRLProof.StochasticGradientBandit.integral_twoArmTrajectoryParameterZero_eq_successFailureSum
BanditRLProof.StochasticGradientBandit.twoArmGeneratedExpectedPseudoRegret_eq_parameter_add_failureSq
BanditRLProof.StochasticGradientBandit.integral_twoArmTrajectoryParameterZero_le_source_log_bound
BanditRLProof.StochasticGradientBandit.integral_twoArmSampledPseudoRegret_eq_generated
BanditRLProof.StochasticGradientBandit.twoArmGeneratedExpectedPseudoRegret_le_sourceTheoremOne
BanditRLProof.StochasticGradientBandit.integral_twoArmSampledPseudoRegret_le_sourceTheoremOne
BanditRLProof.StochasticGradientBandit.twoArmFixedIIDDirac_theoremOne
```

Target files: `BanditRLProof/Algorithms/StochasticGradientBanditAudit.lean`,
`BanditRLProof/Algorithms/StochasticGradientBanditTrajectoryAudit.lean`,
`BanditRLProof/Algorithms/StochasticGradientBanditTwoArmRate.lean`, and
`BanditRLProof/Algorithms/StochasticGradientBanditExponentialAudit.lean`,
`BanditRLProof/Algorithms/StochasticGradientBanditConditionalExponentialAudit.lean`,
`BanditRLProof/Algorithms/StochasticGradientBanditTwoArmRecurrence.lean`,
`BanditRLProof/Algorithms/StochasticGradientBanditTwoArmInitialRecurrence.lean`,
`BanditRLProof/Algorithms/StochasticGradientBanditTwoArmMeasurableRecurrence.lean`,
`BanditRLProof/Algorithms/StochasticGradientBanditTwoArmPathIntegrability.lean`,
`BanditRLProof/Algorithms/StochasticGradientBanditTwoArmFixedIID.lean`, and
`BanditRLProof/Algorithms/StochasticGradientBanditTwoArmTheoremOne.lean`.

## Gate

```bash
lake env lean BanditRLProof/Algorithms/StochasticGradientBanditAudit.lean
lake env lean BanditRLProof/Algorithms/StochasticGradientBanditTrajectoryAudit.lean
lake env lean BanditRLProof/Algorithms/StochasticGradientBanditTwoArmRate.lean
lake env lean BanditRLProof/Algorithms/StochasticGradientBanditExponentialAudit.lean
lake env lean BanditRLProof/Algorithms/StochasticGradientBanditConditionalExponentialAudit.lean
lake env lean BanditRLProof/Algorithms/StochasticGradientBanditTwoArmRecurrence.lean
lake env lean BanditRLProof/Algorithms/StochasticGradientBanditTwoArmInitialRecurrence.lean
lake env lean BanditRLProof/Algorithms/StochasticGradientBanditTwoArmMeasurableRecurrence.lean
lake env lean BanditRLProof/Algorithms/StochasticGradientBanditTwoArmPathIntegrability.lean
lake env lean BanditRLProof/Algorithms/StochasticGradientBanditTwoArmFixedIID.lean
lake env lean BanditRLProof/Algorithms/StochasticGradientBanditTwoArmTheoremOne.lean
lake env lean Tests/StochasticGradientBanditPaperAuditCanary.lean
lake env lean Tests/StochasticGradientBanditConditionalExponentialAuditCanary.lean
lake env lean Tests/StochasticGradientBanditTwoArmRecurrenceCanary.lean
lake env lean Tests/StochasticGradientBanditTwoArmInitialRecurrenceCanary.lean
lake env lean Tests/StochasticGradientBanditTwoArmMeasurableRecurrenceCanary.lean
lake env lean Tests/StochasticGradientBanditTwoArmPathIntegrabilityCanary.lean
lake env lean Tests/StochasticGradientBanditTwoArmFixedIIDCanary.lean
lake env lean Tests/StochasticGradientBanditTwoArmTheoremOneCanary.lean
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
- [x] The generated-kernel Equation-(8) bridge compiles with 4 named
  declarations for the initial and successor kernels.
- [x] The fixed-history successor-recurrence extension compiles with 10 named
  declarations, and the source-initial recurrence extension compiles with 3.
- [x] The measurable contract/trajectory/filtration extension compiles with 25
  named declarations, including both a.e. conditional-distribution recurrence
  transports.
- [x] The path-integrability extension compiles with 19 named declarations:
  2 initial contract wrappers, 4 reward-support transports, 2 source-increment
  bounds, 2 bounded-support source-increment integrability theorems, 1
  history-parameter envelope, 2 potential identities, 2 fixed-horizon
  integrability theorems, 2 conditional-expectation/conditional-distribution
  identities, and 2 tower-ready conditional recurrence bounds.
- [x] The fixed-IID source-contract extension compiles with 9 named
  declarations: 2 definitions and 7 theorems, ending in the one-way
  `twoArmFixedIIDEnvironment_contract` bridge and the generated-history
  Equation-(5) gap-coordinate wrapper.
- [x] The fixed-IID construction discharges Equation-(5)'s generated-history
  `Integrable sourceIncrement` premise from bounded support; it adds no
  independence, moment, positive-gap, or learning-rate-sign hypothesis.
- [x] The unconditional-recurrence extension compiles with 37 named
  declarations: 7 definitions, 21 lemmas, and 9 theorems, including the
  normalized initial bridge and resulting generic source-indexed failure-mass
  sum.
- [x] The Theorem-1 endpoint layer compiles with 32 named declarations: 5
  definitions and 27 theorems, including the actual sampled-action regret
  bridge and `twoArmFixedIIDDirac_theoremOne`.
- [x] The twelve compiled layers contain 215 named declarations in the exact
  `26+18+18+14+4+10+3+25+19+9+37+32` split.
- [x] Refresh the declaration indexes, proof Blueprint, website build, and
  anonymous claim ledger to the 215-declaration boundary.
- [x] Refresh the separate paper repository's arXiv and ICLR audit tables,
  rebuild both PDFs, and synchronize the verified revision to Overleaf.
- [x] Re-run the repository-wide Lean, harness, website, and anonymous-artifact
  gates after the evidence refresh.
- [x] Complete an independent mathematical review of the final Theorem-1
  assumptions, source-time fence, constants, sampled-action semantics, and
  representative axiom prints; no P0/P1 issue was found and key endpoints use
  only `propext`, `Classical.choice`, and `Quot.sound`.
- [x] Complete an independent mathematical review of the unconditional
  recurrence/telescope signs, positivity, source-time fence, and `1 / 4`
  initial term; no P0/P1 issue was found, and the remaining P2 promotion
  boundary is recorded above.
- [x] Complete an independent model-based review of the final synchronized
  mathematical, paper, website, and artifact claims; no P0/P1 issue was found.
  Independent human-expert target validation remains a separate open evidence
  requirement and is not implied by this check.
- [x] The process-level extension above is implemented and compiled.
