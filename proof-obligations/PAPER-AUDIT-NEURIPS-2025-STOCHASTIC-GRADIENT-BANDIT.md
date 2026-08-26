# Proof obligations: NeurIPS 2025 stochastic-gradient-bandit source audit

Task id: `PAPER-AUDIT-NEURIPS-2025-STOCHASTIC-GRADIENT-BANDIT`

| Obligation | Evidence target | Status | Boundary |
| --- | --- | --- | --- |
| SGB-3 softmax law | positive denominator, positive coordinates, sum one | compiled | deterministic finite action set |
| SGB-4 Algorithm-1 update | exact selected/nonselected formula and zero-sum | compiled | reward is a scalar input |
| SGB-5 conditional-mean algebra | gradient and gap coordinate identities | compiled | finite categorical expectation after conditioning |
| SGB-6 best-arm cumulative lower bound | pointwise and finite-horizon forms | compiled | unique best and positive minimum gap explicit |
| SGB-7 regret split | post-convergence plus squared failure mass | compiled | maximum-gap envelope and positive `eta*Delta` explicit |
| SGB-HISTORY-STATE | recursive parameter state and measurability | compiled | inclusive history and fixed learning rate explicit |
| SGB-HISTORY-POLICY | initial/successor finite softmax Markov laws | compiled | generated from the recursive state, not assumed |
| SGB-HISTORY-TRAJECTORY | canonical pair trajectory and successor conditional laws | compiled | uses an explicit measurable history environment |
| SGB-EQ5-COND-MEAN | conditional-kernel integral of the generated source increment | compiled | coordinate-update integrability and arm-reward integral equalities remain explicit |
| SGB-TWO-ARM-STRUCTURE | pathwise Equation (9), source-time adapter, uniform initialization, and Equation (11) odds | compiled | `Fin 2`, source zero initialization, and exact trace-time fence explicit |
| SGB-EQ8-EXPONENTIAL-MOMENT | source-exact `C_eta`, its monotonicity, `C_eta <= exp(2 eta)`, and Equation (8) | compiled | generic probability law with a.e. measurable reward supported on `[-1,1]`; retained as a standalone analytic theorem |
| SGB-EQ8-GENERATED-KERNEL | Equation (8) on the generated initial and successor reward kernels | compiled | 4 declarations; armwise support and fixed means remain explicit |
| SGB-TWO-ARM-SUCCESSOR-RECURRENCE | forward/inverse fixed-history successor recurrence inequalities | compiled | 10 declarations; generated-kernel Equation (8), exact signs, and success/failure-square remainders |
| SGB-TWO-ARM-INITIAL-RECURRENCE | uniform source initialization and both time-one recurrence inequalities | compiled | 3 declarations; zero initialization gives `p_1=1/2` |
| SGB-MEASURABLE-RECURRENCE | measurable bounded fixed-mean contract, trajectory, filtration, and a.e. conditional-distribution transport | compiled | 25 declarations; general prior reveals latent `Env`, while a fixed/Dirac environment gives the fixed-instance reading |
| SGB-PATH-INTEGRABILITY | finite-prefix reward support, source-parameter envelope, potential identities/integrability, condexp identities, tower-ready recurrence bounds, and bounded-support source-increment integrability | compiled | 19 declarations in the exact 2+4+2+2+1+2+2+2+2 split; no global tower iteration is claimed |
| SGB-FIXED-IID-SOURCE-CONTRACT | fixed two-arm probability laws to the bounded fixed-mean history-environment contract and one-step Equation-(5) consumer | compiled | 9 declarations: 2 definitions and 7 theorems; `twoArmFixedIIDEnvironment_contract` is a one-way bridge, not an equivalence |
| SGB-EQ5-BOUNDED-SUPPORT-INTEGRABILITY | derive initial and successor pair-kernel `Integrable sourceIncrement` from the existing bounded-support contract | compiled | `abs_sourceIncrement_softmax_le_abs_reward`, finite-action comp-product support transport, and a constant-one integrability envelope; no moment or independence premise |
| SGB-FIXED-IID-EQ5-INTEGRABILITY | discharge Equation-(5)'s `Integrable sourceIncrement` premise on the generated fixed-IID history | compiled | `integral_twoArmFixedIIDHistoryStepKernel_sourceIncrement_eq_gapCoordinate` consumes the existing probability, support, mean, and gap equalities; it remains a one-step kernel identity |
| SGB-UNCONDITIONAL-RECURRENCE | unconditional forward/inverse recurrences, finite iteration, normalized initial bridge, and resulting generic source-indexed expected squared failure-mass sum | compiled | 37 declarations; `twoArmFullFailureMassSqSum_le` includes source round `t=1` as `1/4`; no Equation-(7) or regret endpoint is claimed |
| SGB-THEOREM-1 | exact two-arm finite-regret endpoint | compiled | 32 declarations close the Equation-(5) conditional-expectation tower, expected-parameter telescope, forward Jensen/log bound, actual sampled-action regret bridge, Equation-(7) assembly, and fixed-IID/Dirac source endpoint with exact horizon and constants |
| SGB-T4-SOURCE-CONTRACT | Appendix-E positive drift margin, audited finite survival-event composition under explicit premises, and finite geometric transient-phase envelope | compiled | 8 declarations: 2 definitions and 6 theorems; no general-`K` generated process, stopped supermartingale/Doob bound, uniform buffered-event producer, or Theorem 4 is claimed |
| SGB-THEOREMS-2-4 | logarithmic/polynomial and general-`K` learning-rate endpoints | blocked | source-specific rate arguments uncompiled |
| SGB-CANARY | typed checks and representative axiom prints | compiled | baseline axioms only |
| SGB-EVIDENCE-SITE | reference index, Blueprint, website source links, anonymous ledger | compiled | local generated evidence records 223 declarations: the frozen 215-declaration Theorem-1 stack in the exact `26+18+18+14+4+10+3+25+19+9+37+32` split plus 8 Theorem-4 source-contract leaves; live Pages remains unchanged until the reviewed branch is merged and deployed |
| SGB-REVIEW | independent source/claim review | partial | independent theorem-contract review matched assumptions, constants, sampled-action semantics, fixed-IID/Dirac meaning, and source time fence with no P0/P1; human-expert target validation remains pending, so this row is not promoted |

No obligation may be promoted because a prose theorem card exists. Only the
focused Lean module, canary, full gate, and generated evidence may move the
finite algebra, process, generated Equation-(8), recurrence, or path-
integrability rows to `compiled`; the overall audit remains `partial`, and the
Theorem-1 row is `compiled` while Theorems 2--4 remain `blocked`.  Global
unconditional recurrence iteration, expected failure-mass control, the
expected-parameter/Jensen consumer, fixed-IID/Dirac specialization,
Equation-(7) assembly, and the sampled-action endpoint now compile; the other
source learning-rate endpoints remain absent.  The fixed-IID adapter discharges
the separate fixed two-arm source-law producer by mapping its probability,
support, measurability, and integral-mean hypotheses into the bounded fixed-
mean contract.  The map is one-way and does not identify the broader contract
with fixed IID laws.  The bounded-support leaves now discharge Equation-(5)'s
separate generated-history `Integrable sourceIncrement` premise and the
fixed-IID consumer reuses that result.  The separate unconditional module
  closes the generic tower/failure-mass slice, and the final theorem module
  consumes it without weakening the source target.

## Compiled Theorem-4 source-contract gate

- Source location: Theorem 4 and Appendix E Steps 1--4, physical PDF
  pp. 47--49.
- Target file:
  `BanditRLProof/Algorithms/StochasticGradientBanditTheoremFourContractAudit.lean`.
- Canary:
  `Tests/StochasticGradientBanditTheoremFourContractAuditCanary.lean`.
- Compiled scope: positive Equation-(22) drift margin; for `0 < pPrime` and
  `c < 1/2`, the audited finite lower bound `pPrime * (1 - 2*c)` and its strict
  positivity; and, for `0 < rho <= 1`, finite phase-mass sums bounded termwise
  by `(1 - rho)^j` and therefore bounded in total by `1/rho`.
- Source-contract diagnosis: Step 4 switches between the buffer directions
  `q >= c` and `q < c`, while its displayed probability direction does not
  provide the lower bound required by Step 3.
- Nonclaims: the gate does not produce the uniform `c,pPrime` event from the
  bounded equal-gap IID process, build the general-`K` generated trajectory,
  prove a stopped supermartingale/Doob estimate, or compile Theorem 4.

## Compiled Theorem-1 endpoint

The final layer is recorded as follows.

- Source location: Theorem 1 and Appendix A.2 of the official camera-ready
  paper.
- Target file:
  `BanditRLProof/Algorithms/StochasticGradientBanditTwoArmTheoremOne.lean`.
- Terminal declaration: `twoArmFixedIIDDirac_theoremOne`.
- Semantic target: expected pseudo-regret of the actions actually sampled by
  the generated two-arm Algorithm-1 trajectory, not a supplied probability
  schedule or deterministic proxy.
- Source fence: Lean `tailHorizon + 1` is the paper's `T`, with the uniform
  first action included explicitly.
- Source contract: fixed armwise IID probability laws, a.e. reward support in
  `[-1,1]`, stated integral means, `0 < eta`, `0 < Delta < 1`, exact mean gap,
  and `eta * sourceC eta < Delta`.
- Exact conclusion:
  `R_T <= log (1 + 4 * eta * Delta * T) / (2 * eta)
    + Delta / (2 * eta * (Delta - eta * sourceC eta))`.
- Nonclaims: this endpoint does not compile Theorems 2--4, a general-`K`
  result, or the whole external paper.

## Compiled bounded-support Equation-(5) leaf

The completed leaf is recorded as follows.

- Source card: `PPR-BAUDRY-JOHNSON-VARY-PIKEBURKE-REBESCHINI-2025-SGB`.
- Scenario: `SCN-STOCHASTIC-FINITE`.
- Source locations: Equation (5), physical PDF p. 3; the fixed-IID bounded
  reward model, physical PDF p. 1.
- Local APIs: `measurable_sourceIncrement`,
  `abs_sourceIncrement_softmax_le_abs_reward`,
  `TwoArmBoundedFixedMeanEnvironmentContract`,
  `measurableEnvironmentInitialPairKernel`, and
  `measurableEnvironmentHistoryStepKernel`.
- Mathlib route: `MLIB-MEASURE-INTEGRAL` and
  `MLIB-PROBABILITY-KERNEL`, specifically `Measure.ae_compProd_of_ae_ae`,
  `Integrable.of_bound`, and the finite/probability-measure constant envelope.
- Target files:
  `BanditRLProof/Algorithms/StochasticGradientBanditTwoArmPathIntegrability.lean`
  and
  `BanditRLProof/Algorithms/StochasticGradientBanditTwoArmFixedIID.lean`.
- First leaves:
  `integrable_measurableTwoArmInitialPairKernel_sourceIncrement_of_contract`,
  `integrable_measurableTwoArmHistoryStepKernel_sourceIncrement_of_contract`,
  and `integral_twoArmFixedIIDHistoryStepKernel_sourceIncrement_eq_gapCoordinate`.
- Hidden regularity: none beyond the existing measurable Markov environment
  and bounded-support contract. Fixed IID is a downstream specialization,
  not an extra premise needed by the generic integrability leaves.
- Pivot rule: if the domination proof fails, audit the pair-kernel support
  transport or the finite-measure instance. Do not add an independence,
  second-moment, or caller-supplied integrability assumption.
