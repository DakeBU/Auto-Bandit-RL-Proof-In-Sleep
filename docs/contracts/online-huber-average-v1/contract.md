# Example2.15 horizon schedule and upper average regret v1

Same pinned source Example2.15 pp15-16/PDF27-28. Freeze three exact terminals and full compiled dependency context before bodies. The algorithm uses eta=1/sqrt(T), independent of comparator, labels and future gradients. T>=1 for the finite bound; the eventual statement ignores the finite initial horizons. This is the source known-horizon constant-step family, not an anytime algorithm claim.

Every comparator and initialization are allowed in the unbounded space. Delta>=0 and feature bound Z>=0 retain zero degeneracies. Fixed-step residual is retained in its existing theorem; nonnegative residual may be dropped for the average upper bound. The explicit envelope is (norm(x0-u)^2+(delta*Z)^2)/(2sqrt(T)), which tends to0. The source performance statement is one-sided: eventually average regret<epsilon. Do not claim regret tends exactly to0 or absolute loss differences vanish, since the algorithm may outperform a comparator.

DAG: actual fixed-step Huber regret -> horizon algebra -> average upper bound; sqrt/inverse limit -> envelope tends0 -> eventual upper regret. Same-model director/architect review, body-only scratch window, no alteration of old terminals. Public integration, full gates and source mapping remain required for acceptance.
