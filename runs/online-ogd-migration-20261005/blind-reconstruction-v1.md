# Restricted-input blind reconstruction: N01–N16

This fresh pass read only `blind-packet-v1.md` in this run as mathematical file input. No source, identity map, proof, compilation evidence, prior judgment, or other file was read. This automated actor has earlier unrelated history; no erased-history, human-review, or external-model-review claim is made. Previous artifacts are unchanged. The report reconstructs unproved headers and certifies neither proofs, compilation, source correspondence, a chapter, nor a Goal.

Independent SHA-256 of exact raw packet bytes:
`789c382de3c4a7a58a08c8d4c6f716bbcfa10eb7b84a5339c3cbdc880df2cbff`.

## Shared mathematical context

E is a complete real inner-product space with its normed additive commutative group structure. Finite dimensionality is not assumed; infinite-dimensional complete spaces are within the stated setting. A domain V supplies a nonempty closed convex carrier C⊆E. Boundedness is not part of the domain structure.

Write P_C(z) for Q1, the classical choice of a nearest point in C. The explicit projection specification is the subject of N01, not a proof supplied to this reviewer. The regularity condition Q2(V,f), written Reg_C(f), is exactly

\[
\exists U\subseteq E:\quad U\text{ open},\quad C\subseteq U,
\quad f\text{ convex on }U,\quad f\text{ differentiable on }U.
\]

The functions f:E→ℝ are real-valued everywhere. This condition requires an open ambient neighborhood containing all C; it is not just convexity/differentiability on C, relative interior, or differentiability at the played points. There is no claim of globally convex/differentiable behavior outside that U. The differentiability and gradient are over ℝ. No EReal finiteness issue or support-selector policy occurs.

The one-step map is S_η^f(x)=P_C(x−η∇f(x)). For a fixed real step η, let

\[
x_0=x_1^{\mathrm{init}},\qquad x_{t+1}=S_\eta^{f_t}(x_t),
\qquad R_T^\eta(u)=\sum_{t=0}^{T-1}[f_t(x_t)-f_t(u)].
\]

Here x₁^{init} denotes the packet's parameter named x₁, which is the time-zero output. This notation avoids shifting the packet's actual indices. These are Q4 and Q5. For a schedule η:ℕ→ℝ, let

\[
z_0=x_1^{\mathrm{init}},\qquad z_{t+1}=S_{\eta_t}^{f_t}(z_t),
\qquad R_T^{\eta_\bullet}(u)=\sum_{t=0}^{T-1}[f_t(z_t)-f_t(u)],
\]

which are Q6 and Q7. For each occurrence the gradients and iterates are from the same specified run. T rounds use losses 0,…,T−1, with terminal output x_T or z_T. Initial outputs are not automatically projected; feasibility statements explicitly assume feasible initialization.

All declarations are deterministic. No probability, expectation, filtration, random oracle, or independence hypothesis is supplied. The current loss gradient at the current play determines the next play. The causality headers compare equal strict-past losses with domain, initialization, and step or full schedule fixed. They do not certify how an external caller selected those shared parameters. No universal finite-history support-policy law is present.

## N01

1. **Objects/spaces:** Complete real inner-product E, domain C, input z∈E, chosen projection P_C(z).
2. **Quantifiers:** Every domain V and z.
3. **Assumptions:** C nonempty, closed and convex, with ambient completeness.
4. **Conclusion/metric:** P_C(z)∈C and ‖z−P_C(z)‖=inf_{w∈C}‖z−w‖. The formal infimum ranges over the subtype of members of C.
5. **Constants/indexing:** Exact distance equality, no approximation factor or additive error.
6. **Information order:** Deterministic classical nearest-point choice; no computational method or running-time guarantee.
7. **Excluded regimes:** Empty, nonclosed or nonconvex domains are outside the supplied structure; no boundedness or finite dimension required. No separate uniqueness assertion appears here.

## N02

1. **Objects/spaces:** Domain C, z,p∈E, projection P_C(z).
2. **Quantifiers:** Every z,p; the premise tests every w∈C before concluding projection equality.
3. **Assumptions:** p∈C and ∀w∈C, ⟨z−p,w−p⟩≤0, besides shared domain/space conditions.
4. **Conclusion/metric:** P_C(z)=p. Thus the specified variational inequality identifies the selected projection.
5. **Constants/indexing:** Inequality threshold exactly zero; no distance tolerance.
6. **Information order:** Deterministic all-feasible-query condition, not an observed finite sample condition.
7. **Excluded regimes:** No assertion when p lies outside C. The header is one implication; it does not explicitly state the converse characterization.

## N03

1. **Objects/spaces:** Domain C, arbitrary z∈E, comparator u∈C.
2. **Quantifiers:** Every z and every feasible u.
3. **Assumptions:** u∈C, with shared projection setting.
4. **Conclusion/metric:** ‖P_C(z)−u‖≤‖z−u‖.
5. **Constants/indexing:** Factor one for ordinary, unsquared norm distances.
6. **Information order:** Deterministic projection comparison with a fixed feasible point.
7. **Excluded regimes:** Does not state the full two-input nonexpansiveness inequality for arbitrary z,z′, or a comparator outside C. z itself need not be feasible.

## N04

1. **Objects/spaces:** Real-valued f, domain C, gradient at x, points x,u∈C.
2. **Quantifiers:** Every f with Reg_C(f) and every feasible pair x,u.
3. **Assumptions:** The open-neighborhood convexity/differentiability condition; x,u∈C.
4. **Conclusion/metric:** f(x)−f(u)≤⟨∇f(x),x−u⟩.
5. **Constants/indexing:** Coefficient one, no smoothness constant, no additive remainder.
6. **Information order:** Deterministic first-order comparison, not a stochastic estimate or a trajectory assertion.
7. **Excluded regimes:** Mere differentiability on a possibly closed C is not the written premise. No gradient bound or globally regular f is required.

## N05

1. **Objects/spaces:** f satisfying Reg_C, positive η, feasible x,u, next point S_η^f(x).
2. **Quantifiers:** Every such f,η,x,u.
3. **Assumptions:** Reg_C(f), η>0, x∈C, u∈C.
4. **Conclusion/metric:** Both inequalities hold:
   \[
   \eta[f(x)-f(u)]\le\eta\langle\nabla f(x),x-u\rangle,
   \]
   \[
   \eta\langle\nabla f(x),x-u\rangle\le
   \frac{\|x-u\|^2}{2}-\frac{\|S_\eta^f(x)-u\|^2}{2}
      +\frac{\eta^2}{2}\|\nabla f(x)\|^2.
   \]
5. **Constants/indexing:** Exact factors 1/2, η² in the gradient term, and negative next-distance term.
6. **Information order:** Deterministic current gradient followed by the projected update; both displayed comparisons are retained.
7. **Excluded regimes:** Nonpositive η excluded. No horizon, domain diameter, or gradient magnitude bound is assumed.

## N06

1. **Objects/spaces:** Constant-step trajectory x_t on C.
2. **Quantifiers:** Every real η, every loss sequence, feasible initialization, every t∈ℕ.
3. **Assumptions:** x₁^{init}∈C; no regularity or positive-step condition.
4. **Conclusion/metric:** x_t∈C.
5. **Constants/indexing:** Includes time zero, which equals the initialization.
6. **Information order:** Deterministic feasibility independent of loss regularity; the definition's gradient expression remains an object even when differentiability is not assumed.
7. **Excluded regimes:** Infeasible initialization is excluded. Zero and negative η are included in this feasibility header; no loss guarantee follows from it.

## N07

1. **Objects/spaces:** Two constant-step runs with common V,η,x₁^{init}, loss sequences f,f′.
2. **Quantifiers:** Every t, under f_s=f′_s for all s<t as whole functions E→ℝ.
3. **Assumptions:** Only those strict-prefix equalities, with shared parameters; no feasibility or regularity premise.
4. **Conclusion/metric:** x_t(f)=x_t(f′).
5. **Constants/indexing:** Strict cutoff s<t; equality at current time t is not required.
6. **Information order:** Deterministic strict-past causality of the current play for common fixed step and initialization. Current loss affects the update after this play.
7. **Excluded regimes:** At t=0 the loss premise is vacuous. Does not compare different steps/initializations, nor permit replacing whole-function equality with equality at a few points.

## N08

1. **Objects/spaces:** Constant-step trajectory x, its regret R_T^η(u), and feasible comparator u.
2. **Quantifiers:** Every η>0, run and natural T with regular losses before T; every u∈C.
3. **Assumptions:** Feasible initialization, horizon Reg_C(f_t), η>0, u∈C.
4. **Conclusion/metric:**
   \[
   R_T^\eta(u)\le\frac{\|x_1^{\mathrm{init}}-u\|^2}{2\eta}
    +\frac\eta2\sum_{t=0}^{T-1}\|\nabla f_t(x_t)\|^2
    -\frac{\|x_T-u\|^2}{2\eta}.
   \]
5. **Constants/indexing:** Exact initial term and negative terminal residual; terminal is x_T and last summed gradient is at t=T−1.
6. **Information order:** Deterministic bound using gradients from this same constant-step run, not another schedule's gradients.
7. **Excluded regimes:** T=0 allowed, with cancelling distance terms and empty sum. No boundedness or gradient bound; nonpositive η excluded.

## N09

1. **Objects/spaces:** Horizon T, positive D,G, constant tuned step η*=D/(G√T), trajectory x* and one comparator u.
2. **Quantifiers:** Every positive T,D,G and run satisfying the premises, each u∈C with the specified initial-distance bound.
3. **Assumptions:** Feasible initialization; T>0, D>0, G>0; Reg_C(f_t) for t<T; u∈C; ‖x₁^{init}−u‖≤D; ‖∇f_t(x*_t)‖≤G for every t<T on the tuned run itself.
4. **Conclusion/metric:** R_T^{η*}(u)≤DG√T.
5. **Constants/indexing:** Exact tuning D/(G√T) and coefficient one in DG√T; T is coerced from ℕ to ℝ inside square root.
6. **Information order:** Deterministic horizon-dependent choice. The header does not guarantee D,G,T are known online or permit reusing gradient bounds from a different run.
7. **Excluded regimes:** Zero D,G,T excluded. D need only bound this initial comparator distance, not the domain diameter; no anytime statement for one horizon-independent step is included.

## N10

1. **Objects/spaces:** Same tuned trajectory at η*=D/(G√T), with D a pairwise domain-distance bound.
2. **Quantifiers:** After fixing domain, run, D,G,T and hypotheses, conclude for all u∈C on the same run.
3. **Assumptions:** Feasible initialization; T,D,G>0; ∀x,y∈C, ‖x−y‖≤D; horizon regularity; actual tuned-run gradients bounded by G for every t<T.
4. **Conclusion/metric:** ∀u∈C, R_T^{η*}(u)≤DG√T.
5. **Constants/indexing:** Same step and exact bound as N09, with no comparator-dependent retuning.
6. **Information order:** Deterministic uniform comparator statement. The played trajectory is fixed before choosing the comparator in the conclusion.
7. **Excluded regimes:** No existence of a minimizing comparator is asserted. Requires positive D,G,T and domain diameter control; not an expected bound or a claim over all horizons with unchanged η*.

## N11

1. **Objects/spaces:** Variable-step trajectory z_t defined by schedule η:ℕ→ℝ.
2. **Quantifiers:** Every schedule, loss sequence, feasible initialization, and natural t.
3. **Assumptions:** x₁^{init}∈C only beyond shared structure.
4. **Conclusion/metric:** z_t∈C.
5. **Constants/indexing:** z₀=x₁^{init}; every subsequent point is produced by the prescribed projected update.
6. **Information order:** Deterministic feasibility; no regularity, monotonicity, or positive-step premise.
7. **Excluded regimes:** Includes zero/negative schedule entries. Does not by itself guarantee regret or differentiability.

## N12

1. **Objects/spaces:** Two variable-step runs with identical full schedule η, V, and initialization, but f,f′.
2. **Quantifiers:** Every t and pair of sequences with f_s=f′_s for all s<t.
3. **Assumptions:** Strict-past whole-loss equality and common fixed schedule; no feasibility/regularity conditions.
4. **Conclusion/metric:** z_t(f)=z_t(f′).
5. **Constants/indexing:** Strict cutoff t; no equality condition on current or future losses.
6. **Information order:** Deterministic conditional nonanticipation. Unlike a stronger possible statement, this header does not compare two schedules merely sharing their prefixes; it uses the identical schedule argument throughout.
7. **Excluded regimes:** t=0 included. No assertion that an externally chosen schedule cannot encode future data, and no comparison of distinct initializations.

## N13

1. **Objects/spaces:** Variable-step run, round t, consecutive z_t,z_{t+1}, and feasible comparator u.
2. **Quantifiers:** Every schedule/run, every t satisfying local positivity/regularity, and every u∈C.
3. **Assumptions:** Feasible initialization, η_t>0, Reg_C(f_t), u∈C. No regularity or positive steps at other rounds required.
4. **Conclusion/metric:**
   \[
   f_t(z_t)-f_t(u)\le
   \frac{\|z_t-u\|^2-\|z_{t+1}-u\|^2}{2\eta_t}
   +\frac{\eta_t}{2}\|\nabla f_t(z_t)\|^2.
   \]
5. **Constants/indexing:** Denominator uses current η_t; next point index t+1; negative next squared distance retained.
6. **Information order:** Deterministic one-round comparison using the gradient at the current actual play and resulting next update.
7. **Excluded regimes:** Current zero/negative η_t excluded. No horizon, decreasing schedule, diameter, or global gradient bound required.

## N14

1. **Objects/spaces:** Pure real scalar sequences a,η:ℕ→ℝ, scalar C, horizon T; no domain or actual trajectory in the formula.
2. **Quantifiers:** Every a,η,C,T meeting the premises; bounds apply to all t<T and monotonicity to t+1<T.
3. **Assumptions:** T>0; η_t>0 for t<T; η_{t+1}≤η_t when t+1<T; a_t≤C for t<T. Neither a_t≥0 nor C≥0 is assumed.
4. **Conclusion/metric:**
   \[
   \sum_{t=0}^{T-1}\frac{a_t-a_{t+1}}{2\eta_t}
   \le\frac{C}{2\eta_{T-1}}-\frac{a_T}{2\eta_{T-1}}.
   \]
5. **Constants/indexing:** Final denominator is 2η_{T−1}, not 2η_T. The terminal a_T is retained with a negative sign.
6. **Information order:** Deterministic scalar weighted telescoping inequality, not a regret bound unless separately instantiated.
7. **Excluded regimes:** No upper bound on a_T is required. T=0 excluded; at T=1 monotonicity premise is vacuous. No conditions on η after T−1 or a after T are imposed.

## N15

1. **Objects/spaces:** Variable-step run z, regret, positive horizon T, real D bounding pairwise distances in C, comparator u∈C.
2. **Quantifiers:** Every schedule/run, T,D and feasible u satisfying all horizon conditions.
3. **Assumptions:** Feasible initialization; T>0; η_t>0 for t<T; η_{t+1}≤η_t for t+1<T; Reg_C(f_t) for t<T; ∀x,y∈C, ‖x−y‖≤D; u∈C. No separately stated D>0 condition.
4. **Conclusion/metric:**
   \[
   R_T^{\eta_\bullet}(u)\le\frac{D^2}{2\eta_{T-1}}
    +\sum_{t=0}^{T-1}\frac{\eta_t}{2}\|\nabla f_t(z_t)\|^2
    -\frac{\|z_T-u\|^2}{2\eta_{T-1}}.
   \]
5. **Constants/indexing:** Last used step η_{T−1} occurs in both distance denominators; gradient terms retain their individual η_t/2 weights.
6. **Information order:** Deterministic bound on the actual scheduled run. No information constraint is imposed on schedule selection and no gradients from a different run can be substituted.
7. **Excluded regimes:** T=0 excluded; T=1 allowed. Nonempty C and the pairwise bound entail D≥0, with D=0 allowed. No gradient bound or step conditions after T−1 required.

## N16

1. **Objects/spaces:** Bounded domain C, its metric diameter d=Metric.diam(C), variable-step run and feasible comparator u.
2. **Quantifiers:** Every bounded V, schedule/run, positive horizon and u satisfying the premises.
3. **Assumptions:** Bounded C, feasible initialization; T>0; positive steps before T; nonincreasing adjacent steps before T; regular losses before T; u∈C.
4. **Conclusion/metric:**
   \[
   R_T^{\eta_\bullet}(u)\le\frac{d^2}{2\eta_{T-1}}
    +\sum_{t=0}^{T-1}\frac{\eta_t}{2}\|\nabla f_t(z_t)\|^2
    -\frac{\|z_T-u\|^2}{2\eta_{T-1}}.
   \]
5. **Constants/indexing:** Squared metric diameter, last-used η_{T−1}, and exact negative terminal term; no radius/diameter factor is added.
6. **Information order:** Deterministic actual-trajectory guarantee. The boundedness premise makes the finite-diameter interpretation appropriate; no empirical diameter estimator is supplied.
7. **Excluded regimes:** Unbounded domains and T=0 excluded. Diameter zero is allowed. Infinite-dimensional complete spaces remain in scope; neither finite dimension nor a uniform gradient bound is required.

## Reconstruction limits

The eight supplied Q0–Q7 context items and all sixteen headers are covered. Metric.diam, library projection facts, and the gradient implementation are not expanded further in the packet; no proof/library verification was performed. The distinction between ambient completeness and finite dimensionality, the exact open-neighborhood regularity witness, same-run gradient bounds, zero-based indices, and terminal residuals has been preserved. These are reconstructed statements only, with no chapter/Goal certification or source/proof acceptance.
