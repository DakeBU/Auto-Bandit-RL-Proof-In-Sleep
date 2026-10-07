# Source-blind reconstruction of Q01-Q04

Actor: `/root/osd_blind`. Requested settings: GPT-6 Astra / medium. Runtime model and effort are unverified; `runtime_model_attested=false`.

Inherited decoder context is present. This decoder previously read neutral fifteen-proposition packets v1/v2 in `online-osd-public-20261007`, and a neutral twenty-one-proposition policy packet in `online-osd-policy-public-20261007`. This is not a first-exposure or history-free decoding. For this task the only input file read was `online-guessing-osd-policy-20261007/blind-packet-v2.md`. No source text, repository search, target proof bodies, other reviews, or prior verdicts were inspected. The current report reconstructs these four descriptions rather than evaluating source intent or inferring a source identity.

## Shared meanings and seven-slot convention

The ambient space of the four targets is the real line with its usual norm/inner product, a finite-dimensional real inner-product space. W is the nonempty closed convex interval [0,1] and its projection is an actual nearest-point projection. The loss is the everywhere finite extended-real embedding
\[
b_y(x)=\operatorname{embed}(|x-y|),\qquad y,x\in\mathbb R.
\]
Hence its toReal value is exactly |x-y|. Both extended-real infinities map to zero under toReal, but no such conversion ambiguity occurs for this b. Support membership means the global inequality
\[
g\in\partial b_y(x)\quad\Longleftrightarrow\quad
\forall z\in\mathbb R,\ |x-y|+g(z-x)\le|z-y|.
\]
The quantifier covers every real z, not just [0,1]. In familiar scalar terms this support set is {-1} when x<y, {1} when x>y, and [-1,1] when x=y. In particular a boundary point of W does not license unbounded normal-cone terms: these are ambient supports of b, not merely supports relative to W.

A policy p has explicit arguments
\[
p(t,\ F_{<t},\ H_t,\ f_t),\quad
F_{<t}:\operatorname{Fin}(t)\to(\mathbb R\to\overline{\mathbb R}),\quad
H_t:\operatorname{Fin}(t+1)\to\mathbb R,\quad
f_t:\mathbb R\to\overline{\mathbb R}.
\]
The first history consists of exactly t past WHOLE loss functions, the second of exactly t+1 actual output points including the current point. The current whole loss is separately available for selection. These types do not describe finite-query evaluation or computability. Policy, schedule, and initialization are exogenous parameters; the interface does not prove that their external choice is independent of future information.

Rename the code argument x1 to a and write f_t=b_{y_t}. For a specified schedule eta and policy p, define
\[
H_0=(a),\quad x_t=H_t(t),\quad
g_t=p(t,(i\mapsto f_{i.\mathrm{val}}),H_t,f_t),\quad
H_{t+1}=\operatorname{snoc}(H_t,\Pi_W(x_t-\eta_tg_t)).
\]
Thus x_0=a is the first played point (round 1 in one-based language). The current loss f_t is used to choose g_t and form x_{t+1}, after the actual current x_t has been constructed. The history records the actual projected outputs, not an auxiliary independent sequence. For T losses, played indices are 0 through T-1; x_T is the post-update endpoint.

Write L_T(eta,y,a,p) for the played-only condition
\[
\forall t<T,\quad g_t\in\partial b_{y_t}(x_t).
\]
It constrains this actual run and this prefix only. None of Q01-Q04 assumes the stronger contextual OracleLaw, which would quantify over arbitrary off-path histories. Likewise none requires the policy to be the contextual canonical current-only choice.

For each proposition, the seven slots below are: objects/ambient structure; quantifier and information scope; hypotheses; actual operation; natural-language and LaTeX conclusion; constants and indices; boundary cases and limits. This naming is an organizational convention, not an extra mathematical claim.

## Q01 — played legal support norms

1. **Objects/ambient structure.** On the real line and W=[0,1], take arbitrary eta:N->R, y:N->R, initial a in R, policy p of the displayed finite-history type, and T,t in N.
2. **Quantifier and information scope.** The compiled order first fixes eta,y,a,p,T, assumes played legality for that exact run/prefix, then quantifies over t with t<T. The initial value and outcomes are not required to lie in W. This is a claim about the actual selected g_t, not all possible outputs of p on off-path inputs.
3. **Hypotheses.** L_T(eta,y,a,p) and t<T only beyond structural definitions. There is no rate positivity, feasible-initial-point, bounded-outcome, or OracleLaw premise.
4. **Actual operation.** Evaluate p at current time, its exact past whole losses, actual H_t, and current b_{y_t}; use the resulting actual g_t.
5. **Conclusion.** Every played legal support has norm at most one:
   \[
   \|g_t\|=|g_t|\le 1\qquad(t<T).
   \]
   The scalar bound comes from membership in a global support set for absolute loss; it is not a supplied gradient-bound hypothesis.
6. **Constants and indices.** Exact norm constant 1, no dependence on T, eta, or the size of y. The strict t<T condition excludes a claim for the terminal selection g_T.
7. **Boundary cases and limits.** If T=0 there is no t<T, so the implication is vacuous. At x_t=y_t, any chosen legal g_t in [-1,1] is allowed. Endpoints 0 or 1 do not enlarge the ambient support set. Zero/negative rates and an infeasible a remain within the statement. The result says nothing about illegal or unplayed policy outputs.

## Q02 — exact clipped update

1. **Objects/ambient structure.** Real W=[0,1], arbitrary schedules eta, real outcomes y, real initial a, finite-history policy p, and t in N.
2. **Quantifier and information scope.** Universal over all these parameters without conditional premises. The selected vector is computed from the same actual history whose last point is x_t.
3. **Hypotheses.** None beyond the typed structural definitions. In particular no played legality, positivity, outcome-range, or initial feasibility assumption.
4. **Actual operation.** Apply the nearest projection on W to x_t-eta_t g_t. In one real dimension this projection is clipping first below at 0 and then above at 1.
5. **Conclusion.** The next actual output equals the explicitly clipped current update:
   \[
   x_{t+1}=\min\bigl(\max(x_t-\eta_tg_t,0),1\bigr).
   \]
   This is an identity for the actual recursion, not an assumed performance inequality.
6. **Constants and indices.** Clipping endpoints are exactly 0 and 1; the current rate and selection have index t and the output index is t+1. Scalar multiplication is ordinary real multiplication eta_t g_t.
7. **Boundary cases and limits.** An infeasible initial a is permitted; successors are clipped. At eta_t=0 the successor is the projection of x_t, which need not equal x_t if it is outside W. Negative rates or illegal feedback do not invalidate this identity. No regret claim follows from the identity alone.

## Q03 — finite positive-horizon comparator bound

1. **Objects/ambient structure.** Fix a real outcome sequence y, initial a, and one finite-history policy p; choose natural horizon T. Comparators are real u in W.
2. **Quantifier and information scope.** After y,a,p and feasibility of a, fix T>0, then require outcome feasibility on t<T and legality on the T-dependent tuned run. The conclusion is for EVERY u in [0,1] under those common inputs and assumptions: one tuned run serves all comparators.
3. **Hypotheses.** a in [0,1]; T>0; y_t in [0,1] for every t<T; and
   \[
   L_T(\eta^{(T)},y,a,p),\qquad \eta^{(T)}_s=\frac1{\sqrt T}\quad\text{for every }s.
   \]
   No off-path law and no separately supplied support-norm hypothesis are present. The stated outcome constraint remains part of this target even if a separate analysis could generalize it.
4. **Actual operation.** Construct the actual run with the constant rate 1/sqrt(T). Denote its output and selections by x_t^{(T)},g_t^{(T)}. The legality premise refers precisely to these outputs and vectors; changing eta may change H_t and hence a history-dependent policy's selection.
5. **Conclusion.** Cumulative absolute-loss excess over each fixed feasible comparator is at most sqrt(T):
   \[
   \forall u\in[0,1],\quad
   R_T^{(T)}(u):=\sum_{t=0}^{T-1}\bigl(|x_t^{(T)}-y_t|-|u-y_t|\bigr)\le\sqrt T.
   \]
   These are ordinary real losses, not ambiguous differences of infinities.
6. **Constants and indices.** Exact leading constant 1 and non-strict inequality. T is coerced from N to R inside square root. The schedule is constant within this run, not 1/sqrt(t) or 1/sqrt(t+1). The sum uses T played points, ending at x_{T-1}^{(T)}, not x_T^{(T)}.
7. **Boundary cases and limits.** T=0 is excluded although the finite sum and totalized real division can be written there. At T=1 the tuned rate is 1 and the bound is 1. Endpoints a,u,y_t in {0,1} are included. The condition on y imposes nothing after T-1. A negative regret is permitted; this is an upper bound, not an absolute-value bound. No minimizer attainment, probabilistic expectation, or anytime schedule is asserted.

## Q04 — eventual one-sided average bound over tuned runs

1. **Objects/ambient structure.** Real outcomes y:N->R, initial a, one fixed finite-history policy p, fixed feasible real comparator u, and real epsilon.
2. **Quantifier and information scope.** Fix y,a,p, assume a feasible and all y_t feasible; require played legality for EVERY positive natural horizon under that horizon's constant tuned schedule. Then fix u in [0,1] and epsilon>0. The conclusion is eventual in T along the natural-number atTop filter. The written quantifiers place u and epsilon before eventuality, so the eventual threshold may depend on the fixed inputs, u, and epsilon; no stronger uniform quantifier order is asserted here.
3. **Hypotheses.** a in [0,1]; y_t in [0,1] for all t; epsilon>0; u in [0,1]; and
   \[
   \forall T\in\mathbb N,\quad T>0\Longrightarrow L_T(\eta^{(T)},y,a,p),\qquad\eta^{(T)}_s=1/\sqrt T.
   \]
   This is played legality for an entire family of actual tuned runs, not OracleLaw on every off-path history.
4. **Actual operation.** For each horizon T, construct a fresh mathematically specified run with the same y,a,p but schedule eta^{(T)}. Its output at t is x_t^{(T)}. The expression is a sequence indexed by horizon T of T-round averages from these horizon-dependent runs, not prefixes of one fixed infinite-rate trajectory.
5. **Conclusion.** Eventually the signed average comparator excess is strictly below every prescribed positive epsilon:
   \[
   \forall^{\mathrm{eventually}}T\in\mathbb N,\qquad
   \frac{R_T^{(T)}(u)}{T}<\varepsilon.
   \]
   Equivalently for each such fixed input tuple there exists N such that every natural T>=N satisfies the displayed strict inequality, with real division by the coerced T.
6. **Constants and indices.** The numerator is exactly the sum from t=0 to T-1 of |x_t^{(T)}-y_t|-|u-y_t|. The same T determines its horizon, denominator, and constant schedule 1/sqrt(T). The finite-horizon upper rate is sqrt(T), hence its positive-horizon average upper rate is 1/sqrt(T); the conclusion uses strict <epsilon eventually.
7. **Boundary cases and limits.** Epsilon=0 and negative epsilon are excluded. T=0 may be part of the syntactically defined horizon sequence, but the legality assumption only covers T>0 and eventuality ignores this finite boundary. No assertion that the signed average converges to zero is made: a negative average bounded away from zero satisfies this one-sided conclusion. It is not a bound on absolute average regret, a pathwise stochastic result, or an anytime guarantee for one fixed schedule. The policy is common across horizons, but its actual histories and choices may differ as eta^{(T)} changes. Comparator and outcome endpoints are allowed.

## Evidence and acceptance boundary

The packet supplies typed proposition descriptions and mathematical recursion/context. Describing or elaborating a `Prop` is not constructing its proof. This reconstruction does not validate target proofs, infer an external source identity, verify source intent, accept source fidelity, certify a library gate, or claim chapter/Goal completion. Runtime model/effort remain unattested.