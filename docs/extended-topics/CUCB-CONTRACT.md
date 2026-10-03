# CUCB frozen representative line

Date: 2026-09-17. Status: **contract frozen; implementation and acceptance incomplete**. This selects the full general probabilistically triggered CUCB line, not only a deterministic-feedback corollary. The all-ten-topic goal is unchanged.

## Source and algorithm

Primary source: Chen, Wang, Yuan, Wang, JMLR 17(50), 2016, Algorithm 1 and Theorems 1 and 2, [PDF](https://jmlr.org/papers/volume17/14-298/14-298.pdf), SHA256 `6a29fc188cd1490c53864eb4f839e572551c171388fc27ba256a7e61424e856c`. Version comparison and recent-source scope are in COMBINATORIAL-SOURCE-AUDIT.md. The 2013 paper supplies historical context; its initialization is not used here.

Finite nonempty base arms and finite nonempty feasible super-arm family. Each round's action precedes fresh feedback. The feedback contains an observed-arm mask (including selected arms) and their bounded [0,1] outcomes. Possible triggering sets are nonempty; discard arms never triggerable before constructing the instance. Each arm has a positive minimum triggering probability p_i across actions that can trigger it. Cross-arm dependence and nonlinear nonnegative rewards are allowed.

Make the source's iid observed-arm assumption explicit at the primitive round-law level: for each fixed action S and arm i, the joint law of observing i and its outcome in measurable B is p_i^S times its fixed marginal law D_i(B). This is a feedback-model compatibility assumption, not a supplied concentration bound. Fresh draws from the round law and oracle kernel construct the causal trajectory. Derive the adaptive MGF and count tails. Do not assume that outcome-dependent censoring automatically preserves an arm's marginal law.

The reward coordinate is nonnegative and integrable under every action's round law; its mean equals r_mu(S). There is no imposed uniform reward bound. The score family r_v(S) for vectors v in [0,1]^m satisfies source monotonicity and bounded smoothness on the possible triggering set of S. Specify continuous strictly increasing f on nonnegative reals with f(0)=0, and explicitly require that positive gaps up to Delta_max lie in its range. This range clause makes the printed inverse meaningful; it is a disclosed formal domain clarification, not a claim that strict increase implies surjectivity. Polynomial smoothness satisfies it.

The oracle is a measurable probability kernel on feasible actions, for each score vector, returning an alpha-approximate action with probability at least beta, where 0<alpha,beta<=1. Its random draw precedes and is independent of fresh environment feedback conditional on the current input/action. Measurability and conditional success must follow from this kernel construction.

Algorithm: initial counts zero and empirical means one. At round t>=1, unobserved arms receive index one; otherwise index min(empirical + sqrt(3 log(t)/(2 count)),1). Call the oracle, observe triggered outcomes and update exactly their counts and sums. There is no forced arm-covering initialization. One infinite causal algorithm/law serves every horizon.

## Mandatory performance endpoints

For every integer n>=1, signed approximation regret is

    n alpha beta opt_mu - E[sum_{t=1}^n actualReward_t].

Prove its equality to the corresponding mean-reward expression. For each arm, define minimum/maximum positive gaps among bad actions that can trigger it; arms with no such actions contribute zero. Define Delta_max=0 when no bad action exists.

With u=f^{-1}(d), preserve the exact piecewise threshold

    ell_n(d,p) = 6 log(n)/u^2                         if p=1,
                 max(12 log(n)/(u^2 p),24 log(n)/p)  if 0<p<1.

1. Theorem 1: regret <= sum_i [ell_n(Delta_i_min,p_i) Delta_i_min + integral from Delta_i_min to Delta_i_max of ell_n(x,p_i) dx] + (1+(2+1_{p_*<1}) pi^2/6) m Delta_max.
2. Theorem 2 for f(x)=gamma x^omega, gamma>0 and 0<omega<=1. If p_*=1: regret <= (2 gamma/(2-omega)) (6m log(n))^(omega/2) n^(1-omega/2) + (1+pi^2/3)m Delta_max. If p_*<1: regret <= (2 gamma/(2-omega)) (12m log(n)/p_*)^(omega/2) n^(1-omega/2) + (1+pi^2/2)m Delta_max + sum_i (24 log(n)/p_i) Delta_max.

The small horizons must be handled, even where a source auxiliary lemma states n>m. Preserve both p branches, the refined integral, exponents and constants. A coarse minimum-gap theorem, assumed visit bound, expected-regret consumer or linear/top-k special case cannot close the contract.

## Disclosed proof repairs

- Use the journal's floor/weighted-sum counting argument. Correct its stray per-arm terms when summing and handle zero counts separately. A pathwise power-envelope argument may replace conditioning on terminal counters without changing the endpoint.
- Replace the analysis-only counter choice argmin N_i p_i by argmin N_i/c(Delta_S,p_i), where c(d,p)=ell_n(d,p)/log(n) denotes the explicit positive coefficient above (defined without division by log(n)). This choice uses the current action and fixed true instance, before observing current outcomes. It is not executed by the learner. Then a charged counter exceeding its own threshold forces every possible triggered arm's counter to exceed its corresponding threshold, including mixed p=1/p<1 cases. Prove existence, predictability, one-increment behavior, and the trigger-count concentration for this repaired choice. Until all these are proved, this is a proposed repair, not acceptance of the source theorem.
- In any conditional-probability decomposition retain conditional mixing weights. Derive the oracle and trigger estimates from the actual round law, not from independence asserted after adaptive selection.

## Mandatory proof obligations and acceptance

1. Actual measurable CUCB history/update/index/oracle/feedback trajectory, all horizons and exact observations.
2. Primitive bounded outcome and reward laws, source reward assumptions, inverse domain, feasible oracle, conditional success and actual/mean reward identity.
3. Adaptive selected-arm concentration, including zero observations, and charged-trigger lower-tail concentration; derive all MGFs from the primitive laws.
4. Predictable normalized-threshold charging, exact counters, sufficient-sampling contradiction, finite union and summable probability bounds with source constants.
5. Refined gap-dependent weighted counting/integral and signed oracle-failure cancellation yielding Theorem 1.
6. Polynomial envelope, finite concavity and both triggering cases yielding Theorem 2.
7. Public canaries with multiple non-singleton feasible actions, distinct rewards, genuinely noisy outcomes, nontrivial triggering and a nontrivial approximation-oracle case. Include deterministic-trigger recovery and no-bad-action boundary.
8. Public root and Tests, full shared harness, standard-axiom audit, independent source-semantic review including every repair, shared topic/source/declaration mappings, reproducible all-topic ICLR evidence. Compilation alone does not accept the topic.

Applications such as influence maximization, improved TPM bounds and CMOSS are contextual comparisons, not extra frozen endpoints. Their omission does not remove any result listed above. No combinatorial implementation or performance endpoint existed when this contract was frozen.
