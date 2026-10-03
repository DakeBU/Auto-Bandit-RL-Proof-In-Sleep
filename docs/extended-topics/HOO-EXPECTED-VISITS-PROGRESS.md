# HOO expected regional visits

Proof source: `d798f79825db50a9a68704e8ce7ed0f82c23c223`.
Frozen repaired contract: `LIPSCHITZ-HOO-CONTRACT.md`, `47474f9`.
This closes the expected poor-region visit bound supporting source Lemmas
14–17. It does not close Theorem 6 or the Lipschitz topic.

Let `Delta_v = best - sup_{x in P_v} f(x)` and
`D_v = nu1 * rho^(depth v)`. For `Delta_v > D_v`, the actual generated HOO
history and reward trajectory satisfy

```
E[T_v(N)] <= 8 log(max(N,2)) / (Delta_v - D_v)^2 + 4.
```

The endpoint is `RegularCovering.poor_region_expected_visits`. Its hypotheses
are the source A1 covering/dissimilarity model, A2 weak Lipschitz condition,
bounded Markov reward kernels with the specified reward-mean identity, and
`best` equal to the global supremum. It does not assume a global maximizer,
confidence inequalities, optimistic indices, a path-comparison conclusion,
expected counts or a regret bound. The inner-ball hypotheses in the regular
covering are reserved for the still-open packing argument; the visit proof
uses the covering and diameter part of that model.

The proof retains the exact actual algorithm and proceeds through:

1. Regional mean bounds from representative membership, A1/A2 and regional
   suprema. A zero-visit U value is infinity, so it cannot underestimate a
   finite optimum.
2. Optimal-region U underestimation and poor-region U overestimation above
   `8 log(max(n,2))/(Delta_v-D_v)^2`, using the already constructed trajectory
   confidence. Index time `n` means `n` observed rewards, before decision `n`.
3. A deterministic infinite branch preserving regional suprema. Each finite
   tree has a first missing branch node. Backward B recursion and actual
   search-path monotonicity yield the finite branch-underestimation witness.
4. A poor-region selection event above the threshold is contained in its
   own U failure or one of at most `n+1` branch U failures. The resulting
   budget is `n(n+2) exp(-4 log(max(n,2)))`.
5. The total budget is at most 3: for `n>=2` it is bounded by
   `2(1/(n-1)-1/n)`, while the `n=0,1` terms are handled explicitly.
6. The shared threshold-count argument yields `E[T_v(N)] <= ceil(A_N)+3`.
   Integrability follows from `T_v(N)<=N`, and `ceil(A_N)<A_N+1` gives the
   displayed additive-four result.

`visitTrace` is only the measurable binary record of whether an actual HOO
action visits one fixed region. `visitTrace_pullCount` proves its exact
identity with the generated history's `visits`. This permits actual reuse of
`HeavyTail.lintegral_pullCount_threshold`, which in turn consumes the shared
UCB threshold-count lemmas. It does not replace the infinite action space or
its history-dependent reward law with a two-arm learning problem.
`HeavyTail.reciprocal_telescope` and the earlier fixed-MGF/finite-union
interfaces are also used. These source-level dependencies are not a measured
efficiency result or a new compiled-reference export.

The audited endpoint and path/index producers use only `propext`,
`Classical.choice` and `Quot.sound`. Existing noisy process/action canaries
remain, but a fully instantiated infinite-arm A1/A2 witness and its application
of this visit endpoint are still required. The current axiom audit is not
independent semantic review.

Remaining mandatory work includes near-optimality packing, the three-way
regret partition, approximation bounds, finite-depth optimization, the full
Theorem 6 rate and actual-regret expectation identity, complete model witness,
independent source/semantic acceptance, shared topic mapping and all-topic
ICLR evidence. Accepted topics remain 0/10.
