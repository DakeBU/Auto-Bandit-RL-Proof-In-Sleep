# Conversion Window: NeurIPS 2025 stochastic-gradient-bandit source audit

Task id: `PAPER-AUDIT-NEURIPS-2025-STOCHASTIC-GRADIENT-BANDIT`

Source card: `PPR-BAUDRY-JOHNSON-VARY-PIKEBURKE-REBESCHINI-2025-SGB`

Scenario card: `SCN-STOCHASTIC-FINITE`

## Natural-language statement

For a nonempty finite action set, let `p` be the softmax transform of a real
parameter vector `theta`. If action `a` is selected and has conditional mean
reward `mu a`, Algorithm 1 changes coordinate `k` by

`(1-p k) r` when `a=k`, and by `-(p k) r` otherwise.

Conditioning on the pre-action history gives Equation (5): the expected
increment is `p k * (mu k - sum_j p j * mu j)`, equivalently
`p k * (sum_j p j * gap j - gap k)`. For the unique best arm with every
other gap at least `Delta`, summing yields Equation (6)'s lower bound. A
maximum-gap envelope and the identity
`1-p = p*(1-p) + (1-p)^2` then yield Equation (7).

On the generated Algorithm-1 history, the update coordinates sum to zero, so
the source zero initialization yields Equation (9) pathwise. For two arms the
parameters are opposites and the softmax law therefore satisfies Equation
(11), `p_1/(1-p_1) = exp(2*theta_1)`. The source-time adapter makes the indexing
explicit: Lean time zero is the untouched source `theta_{.,1}`, and Lean time
`n+1` has consumed exactly trace pair `n`.

For any reward `r` supported on `[-1,1]`, the source's shifted exponential
series
`C_eta = 2 * sum_{n>=0} (2*eta)^n/(n+2)!` yields Equation (8),
`E[exp(q*r)] <= 1 + q*E[r] + q^2/2*C_(|q|/2)`.  The compiled integral form
derives integrability from almost-everywhere measurability and bounded
support, but has not yet been instantiated inside the generated conditional
reward kernels.

## Lean mapping

| Source symbol | Meaning | Lean declaration | Type / role | Status |
| --- | --- | --- | --- | --- |
| `theta_{k,t}` | parameter coordinate | `theta : Action -> Real` | deterministic pre-action state | mapped |
| `p_{k,t}` | softmax action probability | `softmaxProbability theta k` | normalized finite weight | mapped |
| `delta theta_{k,t}` | source update before learning-rate scaling | `sourceIncrement p reward selected k` | one-step update | mapped |
| `mu_k` | conditional arm-reward mean | `mean : Action -> Real` | conditional-mean contract | mapped |
| `Delta_k` | suboptimality gap | `gap : Action -> Real` | deterministic gap coordinate | mapped |
| `E_t[Delta_{A_t}]` | instantaneous expected gap | `instantaneousGap p gap` | finite weighted sum | mapped |
| `E_t[delta theta_{k,t}]` | expected coordinate increment | `expectedSourceIncrement p mean k` | finite conditional-mean algebra | mapped |
| `theta_{1,T+1}` | cumulative best parameter | `bestParameterIncrementSum eta p gap best horizon` | expected-increment sum | mapped with boundary |
| `R_T` | finite expected pseudo-regret | `sourceExpectedPseudoRegret p gap horizon` | gap-weighted finite sum | mapped with boundary |
| `sum_k theta_{k,t}=0` | source Equation (9) | `historyParameter_zeroInitialization_sum` | pathwise inclusive-history invariant | compiled |
| `theta_{.,t}` | source pre-action time | `twoArmParameterAt eta trace (t-1)` | zero at Lean time zero; prefix through `t-2` thereafter | compiled with fence |
| `p_{.,t}` | source two-arm pre-action law | `twoArmProbabilityAt eta trace (t-1)` | softmax of the fenced parameter | compiled with fence |
| `p_{1,t}/(1-p_{1,t})=exp(2 theta_{1,t})` | source Equation (11) | `twoArmProbabilityAt_zero_div_failure_eq_exp_two_mul` | exact printed odds form; Lean arm zero is source arm one | compiled |
| `C_eta` | shifted exponential-series constant | `sourceC eta`, `sourceC_mono` | exact series plus nonnegative-parameter monotonicity | compiled |
| `E[exp(qr)]` second-order bound | source Equation (8) | `integral_exp_mul_le_sourceEqEight_of_ae_abs_le_one` | generic probability integral under a.e. measurable `|r| <= 1` | compiled with generated-kernel composition open |

## Assumption ledger

| Assumption | Lean status | Source | Blocking? |
| --- | --- | --- | --- |
| nonempty finite action set | typeclasses | Algorithm 1 / Eq. (3) | no |
| softmax denominator | explicit positive finite sum | Eq. (3) | no |
| sampling mass sums to one | theorem | Eq. (3) | no |
| reward conditional mean depends on selected arm | pointwise kernel-integral interface | Eq. (5) | no for the compiled trajectory bridge; a uniform source-assumption producer remains downstream |
| gaps satisfy `gap k = bestMean - mean k` | explicit equality | Eq. (5) | no |
| unique best arm and positive minimum gap | explicit hypotheses | Eq. (6) | no |
| maximum-gap envelope | explicit hypotheses | Eqs. (2), (7) | no |
| history measurability and conditional reward kernel | recursive policy, canonical trajectory, and pointwise kernel-integral bridge compiled | Algorithm 1 / Eq. (5) | no for the process bridge; source-specific uniform regularity remains downstream |
| source zero initialization and `K=2` | explicit source-time specialization | Algorithm 1 / Eqs. (9)--(11) | no for the compiled pathwise structure |
| `C_eta` and bounded-reward exponential moment | compiled standalone | Eq. (8) / Theorem 1 | no for the analytic inequality; generated conditional composition remains blocking |
| generated conditional recurrences and expected squared failure mass | not compiled | Theorem 1 proof | yes for Theorem 1 |
| other learning-rate thresholds | not attempted | Theorems 2--4 | yes for those paper endpoints |

## Local API and proof route

| Leaf | Existing APIs/imports | Cards | Intended route | Pivot rule |
| --- | --- | --- | --- | --- |
| softmax normalization | `Real.exp_pos`, finite sums, field algebra | `MLIB-FINSET-SUMS`, `MLIB-EXP-LOG-INEQUALITIES` | cancel common positive denominator | pivot only if denominator simplification lacks a stable API |
| update zero-sum | `Finset.sum_ite`, probability normalization | `MLIB-FINSET-SUMS` | split selected coordinate from complement | retain exact source signs |
| Eq. (5) mean form | finite split-sum algebra | `MLIB-FINSET-SUMS` | isolate selected action, distribute `p k` | do not replace with an assumed gradient oracle |
| Eq. (5) gap form | mean-gap equality and normalization | `MLIB-ORDER-ALGEBRA` | rewrite weighted means through common best mean | retain exact direction |
| Eq. (6) | nonnegative finite sums | `MLIB-FINSET-SUMS`, `MLIB-ORDER-ALGEBRA` | pointwise gap lower bound then sum | do not introduce stochastic independence |
| Eq. (7) | gap envelope, Eq. (6), scalar identity | `MLIB-ORDER-ALGEBRA` | split failure mass and divide by positive `eta*Delta` | leave rate estimates open |
| recursive parameter state | `History.FinitePairHistory`, measurable finite sums | `MLIB-FINSET-SUMS` | recurse over inclusive histories and reuse `sourceIncrement` coordinatewise | keep the exact selected/nonselected source signs and fixed learning-rate scale |
| history policy | `Exp3.finiteActionKernel`, `Exp3.finiteActionMeasure`, `Thompson.HistoryAlgorithm` | `MLIB-PROBABILITY-KERNEL` | package the recursive softmax vector as the initial and successor Markov laws | do not assume a policy oracle or an external trajectory law |
| generated pair trajectory | `Thompson.MeasurableHistoryEnvironment`, `canonicalMeasurableEnvironmentTrajectoryKernel`, `canonicalMeasurableEnvironmentTrajectoryKernel_condDistrib_succ` | `MLIB-PROBABILITY-KERNEL` | reuse the repository's canonical action/reward trajectory constructor | retain the inclusive-history indexing and environment input explicitly |
| Equation-(5) process bridge | `historyStepKernel`, finite-action kernel integration, arm-reward integral hypotheses | `MLIB-CONDITIONAL-EXPECTATION`, `MLIB-MEASURE-INTEGRAL`, `MLIB-FINSET-SUMS` | integrate `sourceIncrement` against the generated next-pair law, then rewrite by the compiled finite mean/gap identity | if full `condexp` syntax is brittle, first expose the exact conditional-kernel integral; do not relabel a marginal expectation as conditional expectation |
| Equation (9) on generated histories | `historyParameter_zero/succ`, `sum_sourceIncrement`, `softmaxProbability_sum` | `MLIB-FINSET-SUMS` | dependent-history induction and zero-initialization specialization | preserve inclusive-history indexing |
| source-time fence | `Preorder.frestrictLe`, `historyParameter` | `MLIB-FINSET-SUMS` | time zero is untouched; time `n+1` consumes prefix through `n` | do not shift the first update into source time one |
| Equation (11) | `Fin.sum_univ_two`, `Real.exp_sub`, softmax positivity | `MLIB-EXP-LOG-INEQUALITIES`, `MLIB-ORDER-ALGEBRA` | turn the zero-sum invariant into opposite coordinates and cancel the positive softmax denominator | retain the exact odds direction and Lean/source arm mapping |
| `C_eta` and Equation (8) | `Real.summable_pow_div_factorial`, shifted `tsum`, `integral_mono_ae` | `MLIB-EXP-LOG-INEQUALITIES`, `MLIB-MEASURE-INTEGRAL` | split the exponential series after degree one, dominate the tail using bounded support, then integrate | do not relabel the generic probability integral as a generated conditional theorem |

## Proof DAG

| Node | Interface | Dependencies | Lean declaration | Gate | Status |
| --- | --- | --- | --- | --- | --- |
| SGB-3 | softmax probability vector | finite exp sum | `softmaxProbability_sum` | focused Lean | compiled |
| SGB-4 | update zero-sum | SGB-3 / generic normalized `p` | `sum_sourceIncrement` | focused Lean | compiled |
| SGB-5A | expected increment, mean form | SGB-4 | `expectedSourceIncrement_eq_gradientCoordinate` | focused Lean | compiled |
| SGB-5B | expected increment, gap form | SGB-5A | `expectedSourceIncrement_eq_gapCoordinate` | focused Lean | compiled |
| SGB-6 | best-coordinate cumulative lower bound | SGB-5B | `bestParameterIncrementSum_ge` | focused Lean | compiled |
| SGB-7 | regret decomposition | SGB-6 | `sourceRegretDecomposition_le` | focused Lean | compiled |
| SGB-HISTORY-STATE | recursive parameter state and measurability | SGB-3--5 | `historyParameter`, `measurable_historyParameter` | focused Lean | compiled |
| SGB-HISTORY-POLICY | initial/successor softmax Markov laws | SGB-HISTORY-STATE plus finite-action kernels | `historyAlgorithm`, `trajectoryMeasure_condDistrib_action_zero_given_environment`, `trajectoryMeasure_condDistrib_action` | focused Lean | compiled |
| SGB-HISTORY-TRAJECTORY | generated successor action/pair conditional laws | SGB-HISTORY-POLICY plus canonical trajectory kernel | `trajectoryKernel`, `trajectoryMeasure_condDistrib_nextPair_given_environment_prefix` | focused Lean | compiled |
| SGB-EQ5-COND-MEAN | generated conditional-kernel integral equals Equation (5) | SGB-HISTORY-TRAJECTORY plus coordinate-update integrability and arm-reward integral equalities | `integral_measurableEnvironmentHistoryStepKernel_sourceIncrement_eq_gapCoordinate` | full trajectory gate | compiled with those hypotheses explicit |
| SGB-9 | generated pathwise zero-sum and source-time fence | SGB-3--4 and SGB-HISTORY-STATE | `historyParameter_sum_eq_initial`, `twoArmParameterAt_sum_eq_zero` | focused Lean plus indexing canary | compiled |
| SGB-11 | exact two-arm softmax odds consumers | SGB-9 plus finite softmax algebra | `softmaxProbability_zero_div_one`, `twoArmProbabilityAt_exp_two_mul_failure_eq_success` | focused Lean | compiled |
| SGB-8 | source `C_eta` and bounded-reward exponential-moment inequality | exponential-series summability plus a.e. support in `[-1,1]` | `sourceC_le_exp_two_mul`, `integral_exp_mul_le_sourceEqEight_of_ae_abs_le_one` | focused Lean | compiled standalone |
| SGB-RATES | Theorems 1--4 | SGB-HISTORY, SGB-11, SGB-8, reward regularity, conditional recurrences, and expected failure-mass analysis | reserved | paper endpoint | blocked |

The process API permits an arbitrary `initialTheta`; the paper's Algorithm 1
is recovered by the specialization `initialTheta := fun _ => 0`.

## Gaps

- [x] Compile the recursive parameter state, its measurability, and the
  initial/successor softmax action kernels.
- [x] Instantiate the canonical generated action/reward trajectory and prove
  its successor action/pair conditional laws.
- [x] Prove that the finite expected-increment sum is the corresponding
  conditional-kernel integral on that trajectory under explicit coordinate-
  update integrability and arm-reward integral equalities.
- [x] Compile the source zero-initialized Equation-(9) invariant, explicit
  two-arm source-time fence, uniform initial law, and Equation-(11) odds.
- [ ] Package the source paper's reward assumptions as a uniform producer of
  those hypotheses across the generated history, including the stronger
      arm-reward regularity from which update integrability should follow.
- [x] Compile the source-exact `C_eta` and Equation-(8) bounded-reward
  exponential-moment inequality on a generic probability measure.
- [ ] Instantiate Equation (8) on each generated conditional reward kernel,
  use the compiled `C_eta` monotonicity, and compile both two-arm
  conditional recurrences.
- [ ] Bound the expected squared failure mass and assemble Theorem 1's exact
  finite regret inequality.
- [ ] Prove any logarithmic or polynomial regret regime.
- [ ] Verify the two-arm sharp threshold or the general-`K` threshold.
