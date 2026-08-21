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

## Assumption ledger

| Assumption | Lean status | Source | Blocking? |
| --- | --- | --- | --- |
| nonempty finite action set | typeclasses | Algorithm 1 / Eq. (3) | no |
| softmax denominator | explicit positive finite sum | Eq. (3) | no |
| sampling mass sums to one | theorem | Eq. (3) | no |
| reward conditional mean depends on selected arm | finite-mean interface | Eq. (5) | no for algebra; yes for trajectory lift |
| gaps satisfy `gap k = bestMean - mean k` | explicit equality | Eq. (5) | no |
| unique best arm and positive minimum gap | explicit hypotheses | Eq. (6) | no |
| maximum-gap envelope | explicit hypotheses | Eqs. (2), (7) | no |
| history measurability and conditional reward kernel | not constructed | Algorithm 1 | yes for trajectory lift |
| learning-rate threshold and failure probability | not attempted | Theorems 1--4 | yes for paper endpoints |

## Local API and proof route

| Leaf | Existing APIs/imports | Cards | Intended route | Pivot rule |
| --- | --- | --- | --- | --- |
| softmax normalization | `Real.exp_pos`, finite sums, field algebra | `MLIB-FINSET-SUMS`, `MLIB-EXP-LOG-INEQUALITIES` | cancel common positive denominator | pivot only if denominator simplification lacks a stable API |
| update zero-sum | `Finset.sum_ite`, probability normalization | `MLIB-FINSET-SUMS` | split selected coordinate from complement | retain exact source signs |
| Eq. (5) mean form | finite split-sum algebra | `MLIB-FINSET-SUMS` | isolate selected action, distribute `p k` | do not replace with an assumed gradient oracle |
| Eq. (5) gap form | mean-gap equality and normalization | `MLIB-ORDER-ALGEBRA` | rewrite weighted means through common best mean | retain exact direction |
| Eq. (6) | nonnegative finite sums | `MLIB-FINSET-SUMS`, `MLIB-ORDER-ALGEBRA` | pointwise gap lower bound then sum | do not introduce stochastic independence |
| Eq. (7) | gap envelope, Eq. (6), scalar identity | `MLIB-ORDER-ALGEBRA` | split failure mass and divide by positive `eta*Delta` | leave rate estimates open |

## Proof DAG

| Node | Interface | Dependencies | Lean declaration | Gate | Status |
| --- | --- | --- | --- | --- | --- |
| SGB-3 | softmax probability vector | finite exp sum | `softmaxProbability_sum` | focused Lean | compiled |
| SGB-4 | update zero-sum | SGB-3 / generic normalized `p` | `sum_sourceIncrement` | focused Lean | compiled |
| SGB-5A | expected increment, mean form | SGB-4 | `expectedSourceIncrement_eq_gradientCoordinate` | focused Lean | compiled |
| SGB-5B | expected increment, gap form | SGB-5A | `expectedSourceIncrement_eq_gapCoordinate` | focused Lean | compiled |
| SGB-6 | best-coordinate cumulative lower bound | SGB-5B | `bestParameterIncrementSum_ge` | focused Lean | compiled |
| SGB-7 | regret decomposition | SGB-6 | `sourceRegretDecomposition_le` | focused Lean | compiled |
| SGB-HISTORY | recursive history policy and conditional expectation | SGB-3--7 plus kernels/measurability | reserved | full trajectory gate | blocked |
| SGB-RATES | Theorems 1--4 | SGB-HISTORY plus failure-regret analysis | reserved | paper endpoint | blocked |

## Gaps

- [ ] Construct the full history-dependent SGB parameter state and action
  kernel.
- [ ] Prove that the finite expected-increment sum is the corresponding
  conditional expectation on that trajectory.
- [ ] Prove any logarithmic or polynomial regret regime.
- [ ] Verify the two-arm sharp threshold or the general-`K` threshold.
