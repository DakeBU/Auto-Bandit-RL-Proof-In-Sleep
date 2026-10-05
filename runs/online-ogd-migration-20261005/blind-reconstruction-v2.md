# V2 restricted-input blind reconstruction: M01–M12

This fresh pass read only `blind-packet-v2.md` in this run as mathematical file input. It did not read source, provenance, name maps, proofs, compilation logs, review judgments, earlier reports, or other files. V1 artifacts are unchanged. This is a distinct automated decoding pass, not a human or external-model review. Earlier unrelated actor history is not claimed erased. No compilation, proof validation, source acceptance, chapter completion, or Goal completion is certified.

Independently calculated raw-byte packet SHA-256:
`3cd9ab15cb1287b7575f9bd334c12555af05d3ea6995e8cda82731143fd5c79e`.

## Scoped context and exact regularity distinctions

E is a complete real inner-product space with its normed additive commutative group structure. No finite-dimensional assumption is supplied. A domain V consists of a nonempty closed convex carrier C⊆E. C need not have nonempty interior or be bounded. P_C denotes the classical nearest-point choice Q1. The supplied block gives the definition of that choice, not a theorem body establishing its properties.

Every loss is an everywhere real-valued function f:E→ℝ. Three regularity predicates must be distinguished:

- Q8(V,f): f is convex on C, and for every x∈C, f is differentiable at x as a function on the ambient real space E. The premise is DifferentiableAt, not only differentiability within C. This does not ask for one open neighborhood on which all points are differentiability points, nor convexity outside C.
- Q9(V,f): there exists an open set U containing C such that f is convex on C and differentiable on U. Convexity is required on C, not on U; U itself need not be convex in this definition.
- Q2(V,f): there exists an open set U containing C on which f is both convex and differentiable. ConvexOn ℝ U f includes the convex-set requirement in the usual mathematical reading, whereas Q9 places that convexity condition on C. These are whole-domain neighborhood witnesses, not separate neighborhoods chosen only for played points.

Write Reg(f)=Q8(V,f) in the bounds below. It includes all feasible points, not merely a fixed finite trajectory. All differentiability and gradients are over ℝ. There are no extended-real losses, support-policy laws, or finite-value coercions in this packet.

The projected update is S_η^f(x)=P_C(x−η∇f(x)). With initialization a (the packet's x₁) and fixed scalar η, define

\[
x_0=a,\qquad x_{t+1}=S_\eta^{f_t}(x_t),\qquad
R_T^\eta(u)=\sum_{t=0}^{T-1}[f_t(x_t)-f_t(u)].
\]

These are Q4 and Q5. With schedule η:ℕ→ℝ, define

\[
z_0=a,\qquad z_{t+1}=S_{\eta_t}^{f_t}(z_t),\qquad
R_T^{\eta_\bullet}(u)=\sum_{t=0}^{T-1}[f_t(z_t)-f_t(u)],
\]

which are Q6 and Q7. Thus the named initialization x₁ is the actual time-zero iterate. A horizon T uses losses 0,…,T−1 and terminal iterate at T. All gradients in a bound are evaluated on the same trajectory as that bound's regret.

All statements are deterministic and contain no probability, expectation, filtration, random feedback or independence premise. The update uses the current loss gradient at the current play to form the next play. The headers do not contain a separate paired-run causality assertion and do not certify that externally selected schedules or tuning parameters are known at a particular time.

## M01

1. **Objects/spaces:** Complete real inner-product E, nonempty closed convex C, real-valued f, predicates Q9 and Q8.
2. **Quantifier order:** Every V and every f satisfying Q9(V,f).
3. **Assumptions:** A single open U contains C; f is convex on C and differentiable on U.
4. **Conclusion/metric:** Q8(V,f): f is convex on C and ambient DifferentiableAt ℝ f x holds for every x∈C.
5. **Constants/indexing:** No numeric constants, time indices, or bounds.
6. **Information/probability:** Deterministic regularity implication; the neighborhood witness is a mathematical assumption, not observed data.
7. **Boundaries:** No convexity of f on U is demanded by Q9. Only the forward implication is stated; no converse or equivalence with neighborhood regularity is asserted. Boundary points of C are included via ambient differentiability.

## M02

1. **Objects/spaces:** Same domain/function setting, predicates Q2 and Q8.
2. **Quantifier order:** Every V and f with Q2(V,f).
3. **Assumptions:** There exists open U⊇C such that f is convex on U and differentiable on U.
4. **Conclusion/metric:** Q8(V,f), meaning convexity on C and ambient differentiability at every feasible point.
5. **Constants/indexing:** No numerical or indexing terms.
6. **Information/probability:** Deterministic implication from the stronger neighborhood condition.
7. **Boundaries:** No global regularity outside U required, and no converse is claimed. Its neighborhood convexity premise is stronger in placement than M01's convexity only on C.

## M03

1. **Objects/spaces:** Domain C and arbitrary g∈E, defining real linear loss f_g(z)=⟨g,z⟩.
2. **Quantifier order:** Every V and every g.
3. **Assumptions:** Only the shared domain and ambient structures; no norm or nonzero condition on g.
4. **Conclusion/metric:** Q2(V,f_g): an open neighborhood containing C exists on which this linear loss is convex and differentiable.
5. **Constants/indexing:** No coefficient other than one in the inner product; no time index.
6. **Information/probability:** Deterministic regularity assertion for a linear function.
7. **Boundaries:** Includes g=0, unbounded C and infinite-dimensional complete E. Does not give a gradient magnitude bound or a particular numerical neighborhood radius.

## M04

1. **Objects/spaces:** Arbitrary vectors g,x∈E and f_g(z)=⟨g,z⟩.
2. **Quantifier order:** Every pair g,x.
3. **Assumptions:** Shared complete real inner-product-space setting only; no domain parameter or extra differentiability premise.
4. **Conclusion/metric:** ∇f_g(x)=g.
5. **Constants/indexing:** Exact identity, independent of x; no factor two or normalization.
6. **Information/probability:** Deterministic gradient formula, not a stochastic oracle estimate.
7. **Boundaries:** Includes zero vectors and all ambient points, whether feasible for some external domain or not. This is not itself a regret statement.

## M05

1. **Objects/spaces:** f:E→ℝ with Reg(f), and feasible x,u∈C.
2. **Quantifier order:** Every such f and every feasible pair x,u.
3. **Assumptions:** Convexity on C; ambient differentiability at every point in C; x,u∈C. No open-neighborhood witness is required in this header.
4. **Conclusion/metric:** f(x)−f(u)≤⟨∇f(x),x−u⟩.
5. **Constants/indexing:** Exact coefficient one and no additive slack.
6. **Information/probability:** Deterministic first-order loss comparison at x with comparator u.
7. **Boundaries:** Includes points on C's boundary and domains with empty ambient interior, provided ambient differentiability holds. Differentiability merely within C would be a different premise; no statement for x or u outside C.

## M06

1. **Objects/spaces:** Reg(f), positive step η, feasible x,u, and projected update S_η^f(x).
2. **Quantifier order:** Every V,f,η,x,u meeting the premises.
3. **Assumptions:** Q8(V,f), η>0, x∈C, u∈C.
4. **Conclusion/metric:** Both inequalities hold:
   \[
   \eta[f(x)-f(u)]\le\eta\langle\nabla f(x),x-u\rangle,
   \]
   \[
   \eta\langle\nabla f(x),x-u\rangle\le
   \frac{\|x-u\|^2}{2}-\frac{\|S_\eta^f(x)-u\|^2}{2}
    +\frac{\eta^2}{2}\|\nabla f(x)\|^2.
   \]
5. **Constants/indexing:** Factors exactly 1/2 and η²/2; the new squared distance appears negatively, with the intermediate inner-product comparison retained.
6. **Information/probability:** Deterministic one-update statement: the gradient at x determines the projected next point.
7. **Boundaries:** No gradient bound, diameter, or open-neighborhood regularity assumption. Nonpositive η excluded; feasible x and u required.

## M07

1. **Objects/spaces:** Fixed positive η, actual constant-step trajectory x, regret R_T^η(u), feasible comparator u.
2. **Quantifier order:** Every run and natural T with the horizon premises, and each u∈C.
3. **Assumptions:** η>0, a∈C, Q8(V,f_t) for every t<T, u∈C.
4. **Conclusion/metric:**
   \[
   R_T^\eta(u)\le\frac{\|a-u\|^2}{2\eta}
     +\frac\eta2\sum_{t=0}^{T-1}\|\nabla f_t(x_t)\|^2
     -\frac{\|x_T-u\|^2}{2\eta}.
   \]
5. **Constants/indexing:** Initial distance retained exactly; negative terminal residual uses x_T, while gradients run only through T−1; denominators are 2η.
6. **Information/probability:** Deterministic regret bound on this very constant-step run. It does not substitute gradients generated by another step or initialization.
7. **Boundaries:** T=0 allowed with empty sum and canceling distances. No bounded-domain or gradient norm assumption. Q8, rather than Q2 or Q9, is the explicit horizon regularity premise.

## M08

1. **Objects/spaces:** Scheduled trajectory z_t, its next iterate z_{t+1}, current gradient and feasible u.
2. **Quantifier order:** Every run, every t with the local premises, and every u∈C.
3. **Assumptions:** a∈C, η_t>0, Q8(V,f_t), u∈C. No positive steps or regularity at other times is required by the header.
4. **Conclusion/metric:**
   \[
   f_t(z_t)-f_t(u)\le
   \frac{\|z_t-u\|^2-\|z_{t+1}-u\|^2}{2\eta_t}
     +\frac{\eta_t}{2}\|\nabla f_t(z_t)\|^2.
   \]
5. **Constants/indexing:** Current η_t, next index t+1, exact half factors and negative next-distance contribution.
6. **Information/probability:** Deterministic local loss bound using the current gradient to form the next iterate.
7. **Boundaries:** No horizon or monotonicity condition. Nonpositive current step excluded; no neighborhood regularity witness or gradient magnitude bound required.

## M09

1. **Objects/spaces:** Scheduled trajectory, positive horizon T, pairwise domain-distance bound D∈ℝ, comparator u.
2. **Quantifier order:** Every run,T,D satisfying the horizon conditions; every u∈C.
3. **Assumptions:** a∈C, T>0, η_t>0 for t<T, η_{t+1}≤η_t when t+1<T, Q8(V,f_t) for t<T, ∀x,y∈C, ‖x−y‖≤D, u∈C. No separate D>0 premise.
4. **Conclusion/metric:**
   \[
   R_T^{\eta_\bullet}(u)\le\frac{D^2}{2\eta_{T-1}}
     +\sum_{t=0}^{T-1}\frac{\eta_t}{2}\|\nabla f_t(z_t)\|^2
     -\frac{\|z_T-u\|^2}{2\eta_{T-1}}.
   \]
5. **Constants/indexing:** Both distance denominators use the last played step η_{T−1}, not η_T. Per-round gradient weights remain η_t/2.
6. **Information/probability:** Deterministic same-run guarantee. Schedule selection has no predictability premise; this is a statement for the given schedule, not a theorem about how it was chosen.
7. **Boundaries:** T=0 excluded; T=1 makes monotonicity vacuous. D=0 permitted; nonempty C and the pairwise bound force D≥0. No restrictions on steps at t≥T or uniform gradient bound.

## M10

1. **Objects/spaces:** Bounded domain C with d=Metric.diam(C), scheduled run, T and comparator u.
2. **Quantifier order:** Every bounded V and run meeting the conditions, every positive T and u∈C.
3. **Assumptions:** Bounded C, a∈C, T>0, positive η_t for t<T, nonincreasing adjacent steps when t+1<T, Q8(V,f_t) for t<T, u∈C.
4. **Conclusion/metric:**
   \[
   R_T^{\eta_\bullet}(u)\le\frac{d^2}{2\eta_{T-1}}
    +\sum_{t=0}^{T-1}\frac{\eta_t}{2}\|\nabla f_t(z_t)\|^2
    -\frac{\|z_T-u\|^2}{2\eta_{T-1}}.
   \]
5. **Constants/indexing:** Diameter squared, exact half factors, and terminal distance with denominator 2η_{T−1}; no radius-to-diameter factor added.
6. **Information/probability:** Deterministic bound. Boundedness is explicitly present for the finite diameter interpretation; no estimated diameter or probability event appears.
7. **Boundaries:** Unbounded C and T=0 excluded; zero diameter and complete infinite-dimensional ambient spaces allowed. No gradient norm bound or neighborhood regularity required.

## M11

1. **Objects/spaces:** Positive D,G,T, tuned scalar η*=D/(G√T), actual constant-step trajectory x* and one comparator u.
2. **Quantifier order:** For each positive T,D,G and loss sequence/initialization satisfying the assumptions, each feasible u with the stated initial-distance bound.
3. **Assumptions:** a∈C; T>0, D>0, G>0; Q8(V,f_t) for t<T; u∈C; ‖a−u‖≤D; and ‖∇f_t(x*_t)‖≤G for every t<T on the trajectory generated using η*.
4. **Conclusion/metric:** R_T^{η*}(u)≤DG√T.
5. **Constants/indexing:** Exact tuning D/(G√T) and coefficient one in the bound. T is coerced from ℕ to ℝ inside the square root.
6. **Information/probability:** Deterministic horizon tuning. The gradient premise concerns this same tuned run, not another η-run. No assertion makes T,D,G observable beforehand or makes the guarantee anytime.
7. **Boundaries:** Zero D,G,T excluded. D need only bound this comparator's initial distance, not the full domain diameter; no existence of an optimal comparator is claimed.

## M12

1. **Objects/spaces:** Same horizon-tuned run with η*=D/(G√T), now with pairwise domain-distance bound D.
2. **Quantifier order:** Fix V,f,a,T,D,G and all premises first; then the conclusion holds for every u∈C on that same fixed trajectory.
3. **Assumptions:** a∈C; T,D,G strictly positive; ∀x,y∈C, ‖x−y‖≤D; Q8(V,f_t) for t<T; ‖∇f_t(x*_t)‖≤G for every t<T on the η* trajectory.
4. **Conclusion/metric:** ∀u∈C, R_T^{η*}(u)≤DG√T.
5. **Constants/indexing:** Same exact tuning and bound as M11; neither run nor step is reselected for each comparator.
6. **Information/probability:** Deterministic simultaneous comparator bound. No probabilistic qualification, gradient independence condition, or universal gradient bound away from played points is supplied.
7. **Boundaries:** Requires pairwise diameter control here, unlike M11's comparator-specific distance bound. Zero tuning parameters/horizon excluded. No minimizing comparator or horizon-independent schedule is asserted.

## Reconstruction limits

All twelve v2 headers are reconstructed in seven slots using only this packet. The precise change in regularity within this packet is substantive: Q8 uses convexity on C and ambient differentiability at every feasible point without asking for an open-neighborhood witness. Q9 and Q2 provide sufficient stronger assumptions via M01 and M02, with different convexity locations. No equivalence or converse is added. Library implementation details for projection, gradient and Metric.diam are not expanded here and were not independently verified. These statements remain unproved data for this decoder; no source/proof acceptance or chapter/Goal certification follows.
