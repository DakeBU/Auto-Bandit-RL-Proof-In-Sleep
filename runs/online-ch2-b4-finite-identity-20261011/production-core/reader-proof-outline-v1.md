The finite-real identity is established for an arbitrary spliced trajectory y, arbitrary losses and regularizers, and positive finite T.

1. Inclusive cumulative potentials satisfy G_(n+1)(v) = G_n(v) + psi_(n+1)(v) - psi_n(v) + loss_(n+1)(v). This is Finset.sum_range_succ and real algebra.
2. Prove the displayed identity for every prefix n+1 while keeping y fixed. The one-round base case is the direct difference of G_0 values. At the successor, split the final loss difference, the final within-round potential difference, and the final regularizer drift. Substituting the cumulative-potential recurrence cancels the interior terms; the induction hypothesis leaves exactly the new endpoint gap.
3. Instantiate n=T-1. Positivity gives (T-1)+1=T; the literal endpoint splice gives y(T)=z. No minimizer, convexity, or algorithm premise is used.

Actual authored mathematical parents: Finset.sum_range_succ, Finset.sum_range_zero, Nat.sub_add_cancel, ordinary real ring/linear arithmetic and equality simplification. The compiled constant-occurrence export supplies the full elaborator-level TYPE/VALUE inventory; it is neither a minimal necessity claim nor a transitive graph.

Boundary: this proves only the frozen finite-real algebra identity locally. EReal finiteness adaptation, attainment, optimizer/trajectory producers, sharp Young endpoints, complete B4 parents, all seven containers and six future claims, chapter/Goal closure and integration remain open. A distinct BODY review is still required.
