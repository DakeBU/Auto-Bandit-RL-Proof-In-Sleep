# Classical Bandit Proof Techniques

Source cards live in `research-wiki/textbooks/bandit-classics.md`; reusable
Mathlib routes live in `research-wiki/mathlib/theorem-cards.md`; the broad
proof tree lives in `research-wiki/theory-tree/bandit-theory-tree.md`.

## Regret Decomposition

Typical stochastic finite-arm regret proofs factor through:

```text
regret(T) = sum over arms of gap(arm) * pullCount(arm, T)
```

ABRL local status:

- `BanditRLProof.pseudoRegret` is compiled as a dependency-light recursive
  pseudo-regret surface.
- LML theorem card `Bandits.regret_eq_sum_pullCount_mul_gap` records the
  Mathlib/LML version.
- Mathlib retrieval cards `MLIB-FINSET-SUMS`, `MLIB-FINTYPE-FIN`, and
  `MLIB-ORDER-ALGEBRA` should be searched before adding generic finite-sum or
  gap algebra lemmas.

## Explore-Then-Commit

Proof route:

1. Round-robin exploration gives exactly `m` pulls per arm.
2. Commit arm maximizes empirical mean.
3. A sub-Gaussian tail bound controls wrong commit probability.
4. Expected pull count follows from wrong commit probability.
5. Regret follows from pull-count decomposition.

Blocking technologies:

- sub-Gaussian reward sums;
- empirical mean argmax measurability;
- conversion between history-indexed and time-indexed rewards.

## UCB

Proof route:

1. Initial round-robin ensures every arm has positive pull count.
2. Chosen arm maximizes empirical mean plus width.
3. On the good event, a suboptimal pull implies pull count is bounded by
   confidence width algebra.
4. Bad events are controlled by upper and lower sub-Gaussian tails.
5. Summing probabilities gives expected pull-count and regret bounds.

Blocking technologies:

- logarithmic confidence width over `Real`;
- tail-event measurability;
- finite sum/integral exchange;
- harmonic or summability bound for bad events.

## Thompson Sampling

Proof route:

1. Posterior action distribution equals posterior best-action distribution.
2. Bayesian regret decomposes through posterior confidence bounds.
3. Clipped UCB controls optimistic and pessimistic terms.
4. Bounded mean and sub-Gaussian contracts close the final bound.

Blocking technologies:

- conditional distributions;
- posterior over environments;
- clipped confidence bound algebra;
- Bayesian regret integrability.
