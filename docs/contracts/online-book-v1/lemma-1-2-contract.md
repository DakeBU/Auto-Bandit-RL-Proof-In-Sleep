# Lemma 1.2 v1: stabilized source intent

Source: v10 printed page 4, PDF page 16. For arbitrary real losses on V and a minimizer of each finite prefix, the sum of current losses at each current-prefix leader is at most the sum of all losses at the final leader. No convexity, compactness, probabilistic assumption or algorithm existence claim.

Lean uses an arbitrary type X and subset V. `leader n` minimizes losses indexed 0,...,n-1 for positive n; no condition on leader 0 is required. This is equivalent to the source one-based x-star_n. A horizon of zero has empty sums and no nonemptiness obligation; positive horizons imply V is inhabited from leader membership. Prefix-optimality is assumed exactly as in the source, not a regret or stability inequality. Conclusion is the exact final-leader comparison. Dependencies are finite-sum successor identity and order transitivity.

Edit window: new OnlineLearningFoundations module and this run's evidence. No modification to fixed OGD contracts. Native statement fence captured before worker proof. Chapter-level acceptance additionally requires remaining Chapter 1 terminals and full gates.
