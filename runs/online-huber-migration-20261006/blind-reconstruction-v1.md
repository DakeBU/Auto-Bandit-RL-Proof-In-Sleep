# Restricted current-packet reconstruction: P, V, F and N01–N19

Only `blind-packet-v1.md` in this directory was read as mathematical file input for this pass. No directory listing, source, imported definition, proof body, earlier verdict, or other file was inspected. No compilation or search tool was used. Prior unrelated actor history is not erased; this is restricted current-packet reconstruction, not clean-history blinding. The distinct automated actor is `/root/normal_blind`, requested GPT-6 Astra / medium, without runtime-model attestation or human/external-model review. No proof validation, source fidelity/acceptance, chapter certification, or Goal certification is claimed.

Independent raw-byte packet SHA-256:
`fd3374ac3f548f8c577c7dd0cfc6a77733196ff40fad041b5ee7869e1c4246f7`.

## Supplied context and algorithm notation

The packet provides both header displays and neutralized constant types. I interpret their supplied text without independently checking the declarations or any claim of elaboration. N01–N09 are scalar real statements. Every vector target N10–N19 retains NormedAddCommGroup E, InnerProductSpace ℝ E and CompleteSpace E in the supplied constant type, even when mathematically stronger than needed. No finite-dimensional assumption is present. The supplied types of V and F themselves require the real inner-product structure but do not include CompleteSpace; their theorem uses do.

For concise formulas write δ for delta and
\[
\psi_\delta(r)=\begin{cases}r,&|r|\le\delta,\\\delta\operatorname{sign}(r),&|r|>\delta.\end{cases}
\]
This is notation for a displayed expression, not an additional independently inspected function. Standard real sign, derivative, gradient, norm and filter semantics are interpreted rather than implementation-verified.

The packet supplies project as a nearest-point selector, step as project(V,x−η∇f(x)), iterate with initial x₀ and update at t using loss_t to form x_{t+1}, and regret as the sum of loss differences through t<T. For f_t(w)=F(δ,z_t,y_t)(w), write
\[
x_0^\eta=x_0,\quad x_{t+1}^\eta=\operatorname{step}(V,\eta,f_t,x_t^\eta),\quad
R_T^\eta(u)=\sum_{t=0}^{T-1}[f_t(x_t^\eta)-f_t(u)].
\]
The step is constant within each run. In expressions with η=1/√T, each horizon specifies its own constant-step run; this is not the time-varying step 1/√t in a single run. T is a natural number coerced to real for arithmetic. All results are deterministic; there is no probability, independence, stochastic label law, or filtration. Supplied recursion uses the current loss only for the next state, not to choose the already played state. No separate universal paired-run causality theorem is asserted by these headers.

## P — supplied scalar definition

1. **Space:** P:ℝ→ℝ→ℝ, threshold δ and residual r.
2. **Quantifiers/information:** Defined for every real δ,r; deterministic pointwise formula.
3. **Assumptions:** None at the definition level.
4. **Algorithm identity:** A scalar loss, not an update or a gradient selector: P(δ,r)=r²/2 if |r|≤δ, otherwise δ(|r|−δ/2).
5. **Parameters/index:** Half-square normalization and threshold |r|≤δ; no time parameter.
6. **Conclusion mode:** Supplied piecewise definition, whose original body was not inspected.
7. **Boundary:** Equality at the threshold uses the quadratic branch. δ=0 is permitted; the supplied N03 characterizes it. Negative δ is definable but not covered by most regularity/bound headers.

## V — supplied full-space domain

1. **Space:** A Domain E in a real inner-product space; its own supplied type has no completeness class.
2. **Quantifiers/information:** For every such E, a fixed domain; no observed data.
3. **Assumptions:** Normed additive group and real inner-product structure.
4. **Algorithm identity:** Full-space carrier E, with nonempty/closed/convex structure, used by the shared projection/update machinery.
5. **Parameters/index:** No radius, diameter, or time parameter.
6. **Conclusion mode:** Supplied domain identity, not a verified body or a freely chosen bounded constraint set.
7. **Boundary:** Arbitrary initialization and comparator in E are feasible. No bounded-domain assumption is licensed; N13 separately identifies projection behavior in the complete-space theorem context.

## F — supplied vector loss

1. **Space:** F:ℝ→E→ℝ→E→ℝ under real inner-product structure, with no completeness in its own supplied type.
2. **Quantifiers/information:** Every δ,z,y and query w; deterministic evaluation.
3. **Assumptions:** None on parameter signs in this definition.
4. **Algorithm identity:** F(δ,z,y)(w)=P(δ,⟨z,w⟩−y), loss on a linear prediction residual.
5. **Parameters/index:** Feature z∈E, real label y, threshold δ; no half factor beyond the one already in P.
6. **Conclusion mode:** Supplied composition definition, not an independently inspected import.
7. **Boundary:** Features and labels may be zero or arbitrary in magnitude at definition level. Later gradient bounds need δ≥0 and later regret bounds control features, not labels.

## N01

1. **Space:** Real scalar functions f,g and reals c,d.
2. **Quantifiers/information:** Every f,g,c,d satisfying local premises; deterministic derivative at the joining point.
3. **Assumptions:** HasDerivAt f d c, HasDerivAt g d c, and f(c)=g(c).
4. **Algorithm identity:** Glued function h(x)=f(x) for x≤c and g(x) for x>c, not an online procedure.
5. **Parameters/index:** Same derivative d for both sides; non-strict left branch at c.
6. **Conclusion mode:** HasDerivAt h d c, an exact derivative statement.
7. **Boundary:** Requires only derivatives at c, not differentiability everywhere or continuity of derivative functions. Both value and derivative matching are retained; no conclusion away from c.

## N02

1. **Space:** Real δ,r and P.
2. **Quantifiers/information:** Every δ≥0 and every r; deterministic identity.
3. **Assumptions:** δ≥0, including zero.
4. **Algorithm identity:** Equivalent three-region representation of the supplied scalar loss.
5. **Parameters/index:**
   \[P(\delta,r)=\begin{cases}-\delta r-\delta^2/2,&r\le-\delta,\\r^2/2,&-\delta<r\le\delta,\\\delta r-\delta^2/2,&r>\delta.\end{cases}\]
6. **Conclusion mode:** Exact equality, including the linear offsets −δ²/2.
7. **Boundary:** At r=−δ the first branch is selected; at r=δ the second is selected unless δ=0, when the first test takes precedence at r=0. Branch values agree at joins. Negative δ excluded.

## N03

1. **Space:** Real residual r.
2. **Quantifiers/information:** Every r∈ℝ, deterministically.
3. **Assumptions:** Threshold fixed to zero, no other premise.
4. **Algorithm identity:** Degenerate scalar loss P(0,·).
5. **Parameters/index:** Threshold exactly 0, value exactly 0.
6. **Conclusion mode:** P(0,r)=0 for all r.
7. **Boundary:** Includes r=0 and either sign of residual. No positive-threshold restriction; it must not be silently excluded from later nonnegative-threshold claims.

## N04

1. **Space:** Real f,g, derivative profiles df,dg, join c and query point x.
2. **Quantifiers/information:** Every f,g,df,dg,c,x with global derivative-profile premises ∀r; deterministic.
3. **Assumptions:** ∀r, HasDerivAt f (df(r)) r and HasDerivAt g (dg(r)) r; f(c)=g(c); df(c)=dg(c).
4. **Algorithm identity:** h(r)=f(r) if r≤c, otherwise g(r).
5. **Parameters/index:** Derivative candidate at x is df(x) when x≤c and dg(x) otherwise.
6. **Conclusion mode:** HasDerivAt h (if x≤c then df(x) else dg(x)) x.
7. **Boundary:** Covers x=c using the left branch and matching data. Unlike N01, derivative premises range over every real r; no continuity or monotonicity of df,dg required.

## N05

1. **Space:** Real scalar loss P(δ,·), query r.
2. **Quantifiers/information:** Every δ≥0 and r; deterministic.
3. **Assumptions:** δ≥0 only.
4. **Algorithm identity:** Derivative of the specified half-quadratic/linear scalar loss.
5. **Parameters/index:** Candidate is −δ if r≤−δ; r if −δ<r≤δ; δ if r>δ.
6. **Conclusion mode:** HasDerivAt(P δ) of that candidate at r, not just a symbolic deriv equality.
7. **Boundary:** Both joins included and differentiability asserted there. δ=0 gives derivative zero throughout; negative thresholds not covered.

## N06

1. **Space:** Real δ,r and scalar derivative operator.
2. **Quantifiers/information:** Every δ≥0,r.
3. **Assumptions:** Nonnegative threshold.
4. **Algorithm identity:** Saturated residual derivative of P.
5. **Parameters/index:** deriv(P δ)(r)=max(−δ,min(r,δ)); inner min precedes outer max.
6. **Conclusion mode:** Exact derivative identity.
7. **Boundary:** Includes endpoints, zero threshold, and unbounded residuals. No bound on |r| required; negative δ excluded.

## N07

1. **Space:** Function P δ on all ℝ.
2. **Quantifiers/information:** Every nonnegative δ; deterministic convexity.
3. **Assumptions:** δ≥0.
4. **Algorithm identity:** Convexity of scalar loss, not any optimizer property.
5. **Parameters/index:** Set.univ, without restriction to the quadratic interval.
6. **Conclusion mode:** ConvexOn ℝ univ (P δ).
7. **Boundary:** δ=0 gives a constant convex function; no strict convexity, strong convexity, or negative-threshold conclusion.

## N08

1. **Space:** Scalar derivative at real residual r.
2. **Quantifiers/information:** Every δ≥0 and r.
3. **Assumptions:** Nonnegative threshold only.
4. **Algorithm identity:** Uniform magnitude bound for the actual scalar derivative.
5. **Parameters/index:** |deriv(P δ)(r)|≤δ, exact constant one times threshold.
6. **Conclusion mode:** Non-strict global derivative bound.
7. **Boundary:** δ=0 included; r need not be bounded. No bound on the magnitude of P itself is asserted.

## N09

1. **Space:** Real δ,r, deriv and real sign.
2. **Quantifiers/information:** Every δ≥0,r.
3. **Assumptions:** δ nonnegative.
4. **Algorithm identity:** Alternative residual/sign representation of the same scalar derivative.
5. **Parameters/index:** deriv(P δ)(r)=r if |r|≤δ, otherwise δ sign(r).
6. **Conclusion mode:** Exact equality; inner region includes equality.
7. **Boundary:** r=0 is in the inner branch for δ≥0. At δ=0 all derivatives are zero. No arbitrary choice of sign or subgradient is involved.

## N10

1. **Space:** Complete real inner-product E; z,x∈E, real δ,y.
2. **Quantifiers/information:** Every such E, δ≥0, y,z,x; deterministic gradient at x.
3. **Assumptions:** CompleteSpace retained as in constant type; δ≥0, no feature/label bound.
4. **Algorithm identity:** F(δ,z,y)(w)=P(δ,⟨z,w⟩−y).
5. **Parameters/index:** Let r_x=⟨z,x⟩−y. Candidate vector is deriv(P δ)(r_x) • z.
6. **Conclusion mode:** HasGradientAt F of that vector at x.
7. **Boundary:** Includes δ=0,z=0 and arbitrary y,x. No finite-dimensionality, constrained domain, or loss smoothness constant required beyond the stated construction.

## N11

1. **Space:** Complete real inner-product E and F(δ,z,y).
2. **Quantifiers/information:** Every δ≥0,y,z, deterministically.
3. **Assumptions:** Ambient classes including completeness; δ≥0.
4. **Algorithm identity:** Global convexity of the feature-residual loss.
5. **Parameters/index:** ConvexOn over Set.univ in E.
6. **Conclusion mode:** ConvexOn ℝ univ (w↦P(δ,⟨z,w⟩−y)).
7. **Boundary:** No bounded feature, label, or parameter domain. No strict convexity or uniqueness; δ=0 and z=0 permitted.

## N12

1. **Space:** Complete real inner-product E, loss gradient at x.
2. **Quantifiers/information:** Every δ≥0,y,z,x; deterministic pointwise bound.
3. **Assumptions:** δ≥0; no restriction on residual or y.
4. **Algorithm identity:** Gradient of exactly F(δ,z,y), not a freely selected vector.
5. **Parameters/index:** ‖∇F(δ,z,y)(x)‖≤δ‖z‖.
6. **Conclusion mode:** Norm upper bound independent of x and y.
7. **Boundary:** δ=0 or z=0 yields zero upper bound. Completeness remains in supplied type; no finite dimension or parameter norm bound is present.

## N13

1. **Space:** Complete real inner-product E, x∈E and fixed full-space V.
2. **Quantifiers/information:** Every ambient x, deterministically.
3. **Assumptions:** Ambient classes only.
4. **Algorithm identity:** Actual nearest-point projection of the shared project on V.
5. **Parameters/index:** project(V,x)=x with no radius/clipping parameter.
6. **Conclusion mode:** Exact projection identity.
7. **Boundary:** Does not assert identity for other domains. Full-space carrier is essential; no constrained-ball replacement is allowed.

## N14

1. **Space:** Complete real inner-product E; F(δ,z,y) and full-space V.
2. **Quantifiers/information:** Every δ≥0,y,z.
3. **Assumptions:** Nonnegative δ and the ambient classes.
4. **Algorithm identity:** RegularLoss of the supplied feature-residual loss for the shared update interface.
5. **Parameters/index:** RegularLoss V (F δ z y), without numeric regularity constant.
6. **Conclusion mode:** Membership in the named imported regularity predicate.
7. **Boundary:** The packet does not expand RegularLoss's definition in this pass, so no independent body-level characterization is certified. Global convexity and the gradient claim are separately displayed headers, not a license to invent missing predicate fields. δ=0 and arbitrary z,y included; no bounded domain or label hypothesis.

## N15

1. **Space:** Complete real inner-product E, current x, feature z, label y, real η and nonnegative δ.
2. **Quantifiers/information:** Every such tuple; current loss used for a step, and in iteration that step supplies the next state.
3. **Assumptions:** δ≥0; no η>0 assumption in this identity.
4. **Algorithm identity:** Shared step on full-space V with exactly F(δ,z,y).
5. **Parameters/index:** With r=⟨z,x⟩−y,
   \[\operatorname{step}(V,\eta,F(\delta,z,y),x)=x-\eta\,\psi_\delta(r)\,z.\]
   The nested scalar actions in the display and supplied constant type have the same real scalar multiplication interpretation.
6. **Conclusion mode:** Exact unclipped-vector update; only residual derivative is saturated.
7. **Boundary:** η=0 and η<0 included, though later regret claims require positive η. δ=0 or z=0 produces x. No projection onto a bounded parameter set, sign restriction on y, or feature bound is needed here.

## N16

1. **Space:** Complete real inner-product E; sequences z_t∈E,y_t∈ℝ; arbitrary initialization x₀ and comparator u; horizon T.
2. **Quantifiers/information:** For every δ≥0,Z≥0,η>0 and every sequence/pair/horizon satisfying the prefix feature bound. Fixed η is used throughout this same run; current loss only updates the next state.
3. **Assumptions:** ∀t<T, ‖z_t‖≤Z. No label bound, bounded parameter domain, or stochastic hypothesis.
4. **Algorithm identity:** Constant-step iterate of F(δ,z_t,y_t) on full-space V and its comparator regret R_T^η(u).
5. **Parameters/index:** Sum uses rounds 0,…,T−1 and terminal state x_T^η; T cast to real in the energy term.
6. **Conclusion mode:**
   \[
   R_T^\eta(u)\le\frac{\|x_0-u\|^2}{2\eta}
    +\frac\eta2 T(\delta Z)^2
    -\frac{\|x_T^\eta-u\|^2}{2\eta}.
   \]
   Initial distance and negative terminal residual are both retained exactly.
7. **Boundary:** T=0 allowed with empty regret and canceling distances. δ=0,Z=0 allowed; no positive lower bound on them. Feature bound needed only before T. η≤0 excluded. No uniform supremum over unbounded comparators is concluded, since the bound depends on u.

## N17

1. **Space:** Same Hilbert setting and loss sequences, but horizon-tuned η_T=1/√T.
2. **Quantifiers/information:** Every δ≥0,Z≥0,z,y,x₀,u and T>0 satisfying the horizon feature bound; each T defines its own constant-step trajectory.
3. **Assumptions:** T>0 and ∀t<T, ‖z_t‖≤Z, plus δ,Z≥0. Labels unrestricted.
4. **Algorithm identity:** Regret of the shared full-space procedure with step 1/√T throughout the T-round run; not a schedule changing each round.
5. **Parameters/index:** Average regret divides by the same real-cast T. Denominator on the bound is 2√T.
6. **Conclusion mode:**
   \[\frac{R_T^{1/\sqrt T}(u)}T\le
    \frac{\|x_0-u\|^2+(\delta Z)^2}{2\sqrt T}.\]
7. **Boundary:** T=0 excluded; δ=0 or Z=0 included. This bound omits the nonpositive terminal term but does not assert exact equality or two-sided convergence. No anytime single-run guarantee, label bound, or bounded comparator domain.

## N18

1. **Space:** Complete real inner-product E and fixed x₀,u; arbitrary real δ,Z.
2. **Quantifiers/information:** Every δ,Z∈ℝ and x₀,u, followed by natural T tending to infinity.
3. **Assumptions:** No δ≥0 or Z≥0 premise. No sequences, feature bounds or algorithmic premises.
4. **Algorithm identity:** Pure scalar sequence of upper-bound expressions; no iterate or regret occurs in the target.
5. **Parameters/index:** K=‖x₀−u‖²+(δZ)² is fixed; expression K/(2√T).
6. **Conclusion mode:**
   \[\lim_{T\to\infty,\,T\in\mathbb N}\frac{\|x_0-u\|^2+(\delta Z)^2}{2\sqrt T}=0.\]
7. **Boundary:** Includes negative δ or Z because this is an algebraic asymptotic statement, not loss regularity. Finite early indices including zero do not affect the limit; no positive-T premise is listed. Does not itself claim any regret sequence converges to zero.

## N19

1. **Space:** Complete real inner-product E; fixed δ,Z, sequences z,y, initialization x₀, comparator u, and positive real ε.
2. **Quantifiers/information:** For every δ≥0,Z≥0 and sequences/pair with a global feature bound, for every ε>0, eventually all sufficiently large natural T satisfy the comparison. The cutoff may depend on these fixed inputs and ε.
3. **Assumptions:** ∀t∈ℕ, ‖z_t‖≤Z; δ,Z≥0; ε>0. The feature condition is global here, unlike N16–N17's finite-prefix hypotheses. Labels remain arbitrary.
4. **Algorithm identity:** The family of full-space runs each using its own constant η_T=1/√T and the same loss sequence prefix and initialization.
5. **Parameters/index:** Eventual quantifier is Filter.atTop on natural horizons, not almost-everywhere probability. Comparison is average regret R_T^{1/√T}(u)/T with ε.
6. **Conclusion mode:**
   \[\forall\varepsilon>0\ \exists T_0\ \forall T\ge T_0,
     \quad R_T^{1/\sqrt T}(u)/T<\varepsilon.\]
   Strict upper inequality, no absolute value or lower bound.
7. **Boundary:** Does not assert regret/T tends to zero in a two-sided sense; negative values are not excluded. No uniformity over all u, all sequences with no bound, or all horizons is stated. T=0 can be avoided by the eventual cutoff. δ=0,Z=0 remain included. No upgrade to a single trajectory with step 1/√t or an expected-regret claim.

## Scope limits

All 19 targets and the three supplied neutral definitions have seven-slot coverage. The separately supplied constant types preserve completeness even in vector claims whose formulas might admit a broader theorem. Supplied notation is not independently inspected imported definitions. N14 is explicitly left as the named RegularLoss assertion because its fields are not reproduced here. Scalar zero-threshold behavior, unrestricted η in the exact update, unrestricted δ/Z in N18, the negative terminal term, and one-sided eventual regret conclusion are retained. No source fidelity or compilation follows from reconstruction.
