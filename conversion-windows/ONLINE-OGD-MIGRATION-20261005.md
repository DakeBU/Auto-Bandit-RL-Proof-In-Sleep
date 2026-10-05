# OGD source regularity repair conversion window

Frozen source: Orabona v10, printed12–15/PDF24–27, loss game printed8/PDF20. Source and twelve signatures: docs/contracts/online-ogd-migration-v2; distinct contract review: source-contract-receipt-v2.json. V1 is rejected as broad source coverage; its true stronger-assumption proof bodies stay unchanged.

Lean0 is source round1; iterateT is source x_(T+1). SourceRegularLoss uses an arbitrary open differentiability neighborhood and convexity on V; source_to_feasible must produce convexity on V plus ambient derivatives at every feasible point. The supplied ambient extension fixes gradients; no extension independence.

Same old project/step/iterate/iterateVariable/regret definitions. Fixed terminal has no diameter premise and retains negative distance. Variable terminal uses T>=1, positive adjacent nonincreasing schedule and eta(T-1); exact diameter requires boundedness. Tuned terminal has positive D,G,T and actual-run gradient bounds. See immutable source-intent and actual header fingerprints.

| Target | Actual dependencies | State |
|---|---|---|
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

Proof scope fixed in proof-obligations-proving-v2.json. First leaf source_to_feasible. No theorem consumers, new algorithm or weakened terminal. Body/public canary/axioms/root/Tests/full harness/actual graph/shared registry/reader/PR gates pending. Global SGB frontier and whole-book active Goal unchanged.
