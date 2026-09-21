# HOO actual regret partition and finite expected sums

This producer milestone advances the frozen repaired Algorithm 1 / Theorem 6 contract. It is not the optimized regret theorem, independent semantic acceptance or completion of a topic.

`HOOPartition.lean` defines the actual source I_h and J_(h+1) sets using finite binary words and regional suprema. It proves prefix heredity of near-optimality, root membership, |J_(h+1)|<=2|I_h| and the strict regional gap for boundary nodes. For every word, the least failing prefix gives the source three-way cover: below a good depth-H node, a shallow good node, or below a bad child of a good parent. These classes are proved pairwise disjoint. Their indicator sums give an exact regret decomposition on the actual causal action trace.

`Algorithms/HOORegretPartition.lean` proves all three pathwise contributions. Deep good subtrees cost at most 4*nu1*rho^H*N. Shallow good nodes use actual action injectivity to contribute at most once each. Bad subtrees use the good parent's gap bound, with their prefix indicators identified exactly with the stored history's visits. Their expected visits are bounded by 8*log(max(N,2))/(nu1*rho^(h+1))^2+4 using the existing actual-trajectory theorem.

`Algorithms/HOOExpectedRegret.lean` proves integrability of the actual gaps from source mean bounds, and of the finite count sums, before integrating the pathwise inequality. It obtains the source's explicit three-term expected-regret bound for each cutoff H and horizon N. The near-optimality limsup producer then supplies one positive K, independent of both H and N, to yield:

    E[R_N] <= 4*nu1*rho^H*N
      + sum_(h<H) 4*nu1*rho^h * K*(nu2*rho^h)^(-d)
      + sum_(h<H) 8*nu1*rho^h * K*(nu2*rho^h)^(-d)
          * (8*log(max(N,2))/(nu1*rho^(h+1))^2+4).

Here d is any real exponent strictly above the actual Definition-5 dimension. The bound is derived from the actual policy and reward law, not a supplied regret/partition/count oracle. The explicitly stated mean range [0,1] is part of the original model. No compactness, attained maximizer, metric symmetry or triangle inequality is added.

`Tests/HOORegretCanary.lean` instantiates the unoptimized expected bound at every cutoff/horizon for the existing complete infinite-arm noisy A1/A2 model. This does not yet calculate that model's dimension or instantiate the final asymptotic rate.

Remaining: explicit geometric sum constants, integer depth optimization including small horizons, actual/cumulative regret expectation identity, concrete-model dimension, independent semantic review, topic acceptance/mapping and all-ten ICLR evidence. Accepted topics remain 0/10. No controlled efficiency run or graph-derived discovery claim.

Validation receipt: `runs/extended-topics-20260917/hoo-partition-validation.json`. Focused builds and joint validation are distinct statuses.
