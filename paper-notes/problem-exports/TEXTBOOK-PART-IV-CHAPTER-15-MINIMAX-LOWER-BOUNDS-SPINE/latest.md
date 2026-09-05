# Proof Export: Chapter 15 Lemma 15.1, Theorem 15.2, and Exercise 15.7 data-processing leaf

Task id: `TEXTBOOK-PART-IV-CHAPTER-15-MINIMAX-LOWER-BOUNDS-SPINE`

Status: synchronized from locally compiled declarations. The Chapter 15 body
terminals are compiled; Exercise 15.7 remains partial.

## Lean Declarations

- `LowerBounds.banditHistoryRelativeEntropy_eq_expectedPulls_sum`
- `LowerBounds.finiteArmedGaussianMinimaxLowerBound`
- `LowerBounds.unitGaussianMinimaxExpectedPseudoRegret_ge`
- `LowerBounds.klDiv_map_le`
- `LowerBounds.klDiv_observedBanditHistory_le_expectedPulls_sum`

## Natural-Language Proof

For one common randomized history policy, the finite-history law is expanded
one round at a time. The policy kernel cancels between the two environments;
the conditional reward KL is averaged under the first law and regrouped by
arm. This proves Lemma 15.1 with the exact direction
`D(P_nu^pi,P_nu'^pi)` and first-law expected pull counts.

For Theorem 15.2, start from the source Gaussian base environment, choose a
least-explored alternative arm, and raise only its mean. The unit-Gaussian KL
formula and Lemma 15.1 keep the base-to-changed history KL at most `1/2` under
the source gap choice. Bretagnolle--Huber on the source pull-count event then
forces one of the two expected pseudo-regrets to be at least
`sqrt((k-1)n)/27`. The Lean terminal constructs the unit-cube environment for
every randomized policy, and the separate lattice consumer proves the
worst-case/minimax form.

The Exercise 15.7 dependency `klDiv_map_le` proves that a measurable map cannot
increase KL. In the finite-KL branch, the pushed-forward Radon--Nikodym density
is a conditional expectation of the source density; conditional Jensen for
the convex `klFun` compares their integrals. Infinite source KL is handled
directly. Applying this theorem to the complete deterministic-horizon history
and rewriting by Lemma 15.1 yields
`klDiv_observedBanditHistory_le_expectedPulls_sum`.

This last corollary still counts every pull through a fixed terminal horizon.
Exercise 15.7 itself additionally requires a measurable stopped-history law,
an information bound charging pulls only through the bounded stopping time,
and factorization of an arbitrary `F_tau`-measurable random element. Those
nodes remain planned and are not claimed by this export.
