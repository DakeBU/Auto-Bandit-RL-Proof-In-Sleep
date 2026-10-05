# OGD source repair obligations

| source_to_feasible | DifferentiableOn.differentiableAt, IsOpen.mem_nhds | unproved |
| regular_to_feasible | ConvexOn.subset, DifferentiableOn.differentiableAt | unproved |
| linear_regular | LinearMap.convexOn, ContinuousLinearMap.differentiable | unproved |
| gradient_linear | hasGradientAt_iff_hasFDerivAt, continuous dual derivative | unproved |
| first_order | OnlineConvex.convex_gradient_lower_bound | unproved |
| lemma_2_12 | first_order, linear_regular, gradient_linear, old lemma_2_12 quadratic component | unproved |
| theorem_2_13_fixed | new lemma_2_12, old iterate_mem, finite telescope | unproved |
| variable_one_step | new lemma_2_12, old iterateVariable_mem | unproved |
| theorem_2_13_variable_bound | variable_one_step, old weighted_potential_sum | unproved |
| theorem_2_13_variable | theorem_2_13_variable_bound, Metric.dist_le_diam_of_mem | unproved |
| equation_2_1_distance | theorem_2_13_fixed, actual gradient sum bounds | unproved |
| equation_2_1 | equation_2_1_distance, a priori pairwise diameter | unproved |

Version2 unproved obligations are frozen; prior version1 rejection and all failures retained. Future current-state overlays preserve immutable reviewed files. Allowed failure classes follow the harness; semantic/assumption changes require a new reviewed version. Source contract acceptance is not body/package acceptance. Current native command evidence and leaf attempts live in runs/online-ogd-migration-20261005. Chapter2/book remain incomplete; complete migration and enumeration mandatory.
