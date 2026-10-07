# Neutral reconstruction of Q01-Q12

Actor: `/root/osd_blind`. Requested GPT-6 Astra / medium. Runtime model and effort are unverified (`runtime_model_attested=false`). This is neither a human review nor a claim of externally independent review.

Inherited history: this decoder previously reconstructed neutral packets in `online-osd-public-20261007` (v1/v2), `online-osd-policy-public-20261007` (v1), and `online-guessing-osd-policy-20261007` (v2). It is a reused decoder with that context, not a first-exposure decoder. For the present task, only `online-guessing-public-20261007/blind-packet-v1.md` was read. No repository, external source, network, other packet, or prior verdict was inspected. These statements are interpreted from the current packet without identifying or accepting an external source.

## Exact shared interpretation

All variables below are real scalars unless explicitly natural numbers, real sequences, or functions. The ambient space is the usual finite-dimensional real Euclidean line. Let A=[0,1] with its nonempty closed convex domain structure, and let Pi_A be its actual unique nearest-point projection. Define
\[
b_y(x)=\operatorname{embed}(|x-y|),\qquad a(x)=\operatorname{embed}(|x|),
\]
where the embedding is into the extended reals. These losses are finite everywhere. `toReal` is a totalized conversion, not a faithful interpretation of infinity, but finite absolute losses do not invoke an infinite-value fallback.

For an extended-real f, the GLOBAL support set is
\[
S(f,x)=\{g\in\mathbb R:\ \forall v\in\mathbb R,\ f(x)+\operatorname{embed}(g(v-x))\le f(v)\}.
\]
The universal v ranges over the entire real line, including outside A. In real dimension one the supplied inner product is multiplication. For b the equivalent support condition is |x-y|+g(v-x)<=|v-y| for every real v. It is not a support inequality merely on A or its interior.

Proper(f) means f is nowhere minus infinity and is equal to some embedded real at some ambient point. W(V,f) means Proper(f) AND nonemptiness of S(f,x) at every x in the carrier of V. It does not mean f is merely proper or finite at a single feasible point. No additional global convexity premise is to be inserted.

The exact fixed mathematical choice is q(f,x): classical choice of an element of S(f,x) when that set is nonempty, otherwise zero. It is not a freely selected policy, an executable oracle, a specified tie-breaking numerical routine, or a minimum-norm selection. Its only explicit inputs are the current whole loss function and current point. In particular the closed interval at a tie does not imply q=0 there.

The aliases specify actual operations:
\[
s(V,\eta,f,x)=\Pi_V(x-\eta q(f,x)),\qquad
z(V,\eta,F,a,0)=a,
\]
\[
z(V,\eta,F,a,t+1)=s(V,\eta_t,F_t,z(V,\eta,F,a,t)).
\]
Write x_t=z(A,eta,(s->b_{y_s}),a,t). Thus x_0=a is the argument called x1 in Lean. The first charged round has Lean index zero. Current x_t is formed from earlier updates before F_t is used to choose q(F_t,x_t) and produce x_{t+1}. The recursion takes no comparator or future loss as explicit input. Whole current-function access is not finite-query access. Schedule eta and initial a remain externally chosen parameters; the types and strict-prefix claim do not certify their independence from future data. No probability law, filtration, measurability, or anytime execution claim is provided.

The seven slots used separately for every target are: objects/structure; quantifiers and information scope; hypotheses; exact operation; natural-language and LaTeX conclusion; constants/indices; boundaries and limits.

## Q01

1. **Objects/structure.** Arbitrary y,x in R; global extended-real support sets of translated and untranslated absolute loss.
2. **Quantifiers/scope.** For every pair y,x, without any membership restriction to A, and as equality of WHOLE sets of all real g.
3. **Hypotheses.** None.
4. **Operation.** Translate the query from x to x-y while replacing b_y by a(v)=embed(|v|). Both sides still test every ambient comparison point.
5. **Conclusion.** Translation preserves the full support set:
   \[
   \forall y,x\in\mathbb R,\quad S(b_y,x)=S(a,x-y).
   \]
6. **Constants/indices.** Exact equality, not an inclusion or equality of a chosen support; shift is x-y with this sign. No time index.
7. **Boundaries/limits.** Includes x=y, arbitrary negative/positive values, and points outside [0,1]. It does not assert equality of the two loss functions without translation or identify a particular chosen support.

## Q02

1. **Objects/structure.** Real y,x and the global support set of b_y at x.
2. **Quantifiers/scope.** Every y,x satisfying y<x; equality concerns every possible supporting scalar g.
3. **Hypotheses.** Strict y<x only.
4. **Operation.** Evaluate the full support set on the side where x exceeds y.
5. **Conclusion.** The unique support is positive one:
   \[
   \forall y,x\in\mathbb R,\quad y<x\Longrightarrow S(b_y,x)=\{1\}.
   \]
6. **Constants/indices.** Singleton value +1 exactly; no norm-only relaxation or time parameter.
7. **Boundaries/limits.** Tie x=y is excluded. No feasibility or outcome-range condition is required. The statement is stronger than merely 1 belonging to the support set.

## Q03

1. **Objects/structure.** Any real y, with query exactly y.
2. **Quantifiers/scope.** For all y, equality of the entire global support set at the tie point.
3. **Hypotheses.** No extra assumptions; tie is built into the query.
4. **Operation.** Evaluate S(b_y,y).
5. **Conclusion.** The support set is the CLOSED interval of all scalars between minus and plus one:
   \[
   \forall y\in\mathbb R,\quad S(b_y,y)=[-1,1]=\{g\in\mathbb R:-1\le g\le1\}.
   \]
6. **Constants/indices.** Both endpoints -1 and +1 are included; equality, not just an upper norm bound.
7. **Boundaries/limits.** No restriction y in [0,1]. This allows every intermediate value, not only {-1,0,1}; it does not require the canonical q to choose zero or either endpoint.

## Q04

1. **Objects/structure.** Arbitrary real y,x and S(b_y,x).
2. **Quantifiers/scope.** Every y,x with x<y, over the complete support set.
3. **Hypotheses.** Strict x<y only.
4. **Operation.** Evaluate global supports on the side below the loss center y.
5. **Conclusion.** The only support is negative one:
   \[
   \forall y,x\in\mathbb R,\quad x<y\Longrightarrow S(b_y,x)=\{-1\}.
   \]
6. **Constants/indices.** Exact singleton -1; sign is opposite Q02.
7. **Boundaries/limits.** Ties excluded, but arbitrary infeasible or unbounded y,x permitted. Equality is not merely membership of -1.

## Q05

1. **Objects/structure.** All real y,x, with the global support set of absolute loss.
2. **Quantifiers/scope.** Universal complete piecewise classification of the WHOLE set, with first test y<x, then x=y.
3. **Hypotheses.** None beyond real scalar types.
4. **Operation.** Select the appropriate branch of the nested conditional; when both earlier tests fail, real order gives x<y.
5. **Conclusion.**
   \[
   \forall y,x\in\mathbb R,\quad
   S(b_y,x)=\begin{cases}
   \{1\},&y<x,\\
   [-1,1],&x=y,\\
   \{-1\},&x<y.
   \end{cases}
   \]
   The loss has the exact singleton supports away from the tie and the closed tie interval.
6. **Constants/indices.** Values and interval endpoints are exactly +/-1; no time or rate parameters. The displayed third condition unpacks the conditional's else branch.
7. **Boundaries/limits.** Exhausts all real x,y, including ties and points outside A. Does not prescribe canonical tie selection or replace the ambient support with a domain-relative subdifferential.

## Q06

1. **Objects/structure.** Real y, interval domain A, finite extended-real b_y, property W.
2. **Quantifiers/scope.** For every real y, even if y is outside A; the support-existence part quantifies over every x in A.
3. **Hypotheses.** None.
4. **Operation.** Apply the exact property W(A,b_y), expanding both properness and feasible-point support existence.
5. **Conclusion.** Absolute loss is proper and globally supported at every feasible query:
   \[
   \forall y\in\mathbb R,\quad W(A,b_y),
   \]
   i.e.
   \[
   \forall y,\quad
   [(\forall x\in\mathbb R,\ b_y(x)\ne-\infty)\land
   (\exists x\in\mathbb R,\exists r\in\mathbb R,\ b_y(x)=\operatorname{embed}(r))]
   \land[\forall x\in[0,1],\exists g\in\mathbb R,\ g\in S(b_y,x)].
   \]
6. **Constants/indices.** Feasible interval endpoints exactly 0,1; no horizon, step size, or uniform norm claim within W itself.
7. **Boundaries/limits.** Feasible endpoints included. Properness's finite witness is ambient, not explicitly constrained to A. This statement does not add an oracle-computability claim.

## Q07

1. **Objects/structure.** Arbitrary y,x,g in R with ambient support membership.
2. **Quantifiers/scope.** For every such triple, not just the canonical chosen scalar and not just feasible queries.
3. **Hypotheses.** g in S(b_y,x).
4. **Operation.** Take the norm of that actually supporting scalar.
5. **Conclusion.** Every global support has magnitude at most one:
   \[
   \forall y,x,g\in\mathbb R,\quad g\in S(b_y,x)\Longrightarrow\|g\|=|g|\le1.
   \]
6. **Constants/indices.** Exact upper constant 1; no horizon or schedule dependence.
7. **Boundaries/limits.** At x=y both endpoint supports attain equality and intermediate supports are allowed. Domain boundaries do not add unbounded normal directions because support tests all real comparisons. No claim is made for nonmembers.

## Q08

1. **Objects/structure.** Arbitrary real y and feasible real x; exact fixed classical selector q.
2. **Quantifiers/scope.** For every y,x with x in [0,1]. This target is restricted to feasible queries even though other support descriptions are ambient.
3. **Hypotheses.** 0<=x<=1. No y in [0,1] premise.
4. **Operation.** Evaluate q(b_y,x), the actual current-function choice from the nonempty support set.
5. **Conclusion.** The canonical selected scalar has norm at most one:
   \[
   \forall y,x\in\mathbb R,\quad x\in[0,1]\Longrightarrow\|q(b_y,x)\|\le1.
   \]
6. **Constants/indices.** Constant 1; no time index, positivity requirement, or explicit tie-breaking value.
7. **Boundaries/limits.** Includes x=0, x=1 and x=y. It does not assert q=0 at a tie, executable evaluation, or this target's conclusion without its explicit feasible-query premise. Nonemptiness means the fallback is not the legal-selection mechanism here.

## Q09

1. **Objects/structure.** Arbitrary real eta,y,x; domain A and actual s defined through q and projection.
2. **Quantifiers/scope.** Universal over these scalars, with no feasible-query or step-size-sign restriction.
3. **Hypotheses.** None.
4. **Operation.** Subtract eta times the actual q(b_y,x), then use the actual nearest-point projection to A.
5. **Conclusion.** The step equals clipping of that exact scalar update:
   \[
   \forall\eta,y,x\in\mathbb R,\quad
   s(A,\eta,b_y,x)=\min(\max(x-\eta q(b_y,x),0),1).
   \]
6. **Constants/indices.** Lower clipping endpoint 0 then upper endpoint 1; subtraction sign and multiplier eta are literal. No time index.
7. **Boundaries/limits.** Valid at eta=0 and negative eta, and outside A. At eta=0 it projects x, so the result equals x only when x is feasible. It is a recursion identity rather than a regret inequality.

## Q10

1. **Objects/structure.** Two real schedules eta,eta':N->R, two real outcome sequences y,y':N->R, a common real initial a, and natural t.
2. **Quantifiers/scope.** Fix all six inputs, then assume agreement on EVERY s<t. The same canonical q, same A and same initial a are used on both sides; a need not be feasible.
3. **Hypotheses.** For all s<t, eta_s=eta'_s, and for all s<t, y_s=y'_s. Outcome equality implies equality of the corresponding whole loss functions b_{y_s} and b_{y'_s}; the statement is not about only observed scalar loss values.
4. **Operation.** Run the actual recursion with each schedule/outcome sequence, comparing the points before the time-t current losses are used.
5. **Conclusion.** Strict-prefix agreement gives exactly equal current iterates:
   \[
   \forall\eta,\eta',y,y',a,t,\quad
   [(\forall s<t,\eta_s=\eta'_s)\land(\forall s<t,y_s=y'_s)]
   \Longrightarrow
   z(A,\eta,(s\mapsto b_{y_s}),a,t)=z(A,\eta',(s\mapsto b_{y'_s}),a,t).
   \]
6. **Constants/indices.** Prefix is 0,...,t-1, not including t; no agreement at t or later is required. At t=0 both premises are vacuous and both outputs equal a.
7. **Boundaries/limits.** No rate positivity, outcome bounds, or initial feasibility. Does not compare independently chosen policies, constrain future-dependent external initialization/schedule choice, or establish a probabilistic filtration or finite-query oracle. Current q at time t can differ when current outcomes differ despite equal current outputs.

## Q11

1. **Objects/structure.** Real outcome sequence y, feasible initial a, positive natural horizon T; each real comparator u in A.
2. **Quantifiers/scope.** Fix y,a with feasibility, then T>0 and outcome feasibility for t<T; conclusion is for ALL u in [0,1] on ONE common actual tuned run. The comparator is not an input to that recursion.
3. **Hypotheses.** a in [0,1], T>0, and y_t in [0,1] for every t<T. No independently assumed legal-feedback, norm-bound, or one-step performance premise appears; the recursion is the specified canonical q.
4. **Operation.** Use the constant schedule eta_s^(T)=1/sqrt(T) for all s and let x_t^(T)=z(A,eta^(T),(s->b_{y_s}),a,t). Every output in the conclusion belongs to this same tuned run.
5. **Conclusion.** Its T-round signed absolute-loss excess is bounded uniformly over feasible fixed comparators:
   \[
   \forall y,a,T,\quad
   [a\in[0,1]\land T>0\land(\forall t<T,y_t\in[0,1])]
   \Longrightarrow\forall u\in[0,1],\quad
   R_T^{(T)}(u):=\sum_{t=0}^{T-1}(|x_t^{(T)}-y_t|-|u-y_t|)\le\sqrt T.
   \]
6. **Constants/indices.** Exact leading constant 1; non-strict inequality. Natural T is coerced to real for sqrt(T). Constant-in-time rate 1/sqrt(T), not 1/sqrt(t). T terms end at x_{T-1}^(T); x_T^(T) is the subsequent endpoint and is not charged.
7. **Boundaries/limits.** T=0 excluded despite a syntactically meaningful totalized division. T=1 gives rate 1 and upper bound 1. Feasible endpoints included; no constraint on outcomes beyond the prefix. Negative regret is allowed. No claim of absolute regret, best-comparator attainment, expectation, or anytime guarantee is made.

## Q12

1. **Objects/structure.** One real sequence y, feasible real initial a, fixed feasible comparator u, and positive real epsilon; natural T varies eventually.
2. **Quantifiers/scope.** First quantify y,a and require initialization and ALL outcomes feasible; then fix u with feasibility and epsilon>0; then eventuality along natural atTop. Literal order allows the threshold to depend on these fixed parameters; no stronger uniform quantifier order is asserted.
3. **Hypotheses.** a in [0,1], every y_t in [0,1], u in [0,1], and epsilon>0. No external policy-law or additional per-horizon legality hypothesis is present because the definition uses canonical q.
4. **Operation.** For each T construct its own run with eta_s^(T)=1/sqrt(T). The loss sequence and initialization are common across the family, but rates and hence later outputs can differ. This is not a growing prefix of a single fixed-rate or decreasing-rate trajectory.
5. **Conclusion.** Eventually the signed average excess is below each fixed positive epsilon:
   \[
   \forall y,a,u,\varepsilon,\quad
   [a\in[0,1]\land(\forall t\in\mathbb N,y_t\in[0,1])\land u\in[0,1]\land\varepsilon>0]
   \Longrightarrow
   \exists N\in\mathbb N,\ \forall T\ge N,\quad
   \frac{\sum_{t=0}^{T-1}(|x_t^{(T)}-y_t|-|u-y_t|)}{T}<\varepsilon.
   \]
   This unpacks the eventual natural-number atTop quantifier.
6. **Constants/indices.** The SAME T determines schedule 1/sqrt(T), number of summands, and denominator (coerced to real). The strict <epsilon conclusion is one-sided. Positive-horizon finite bounds have average upper scale 1/sqrt(T).
7. **Boundaries/limits.** Epsilon=0 excluded. T=0 may be syntactically defined by totalized operations but is immaterial to eventuality; no zero-horizon performance inference is needed. A signed average remaining negative satisfies the claim, so this is not a two-sided convergence-to-zero or absolute-value statement. It is not an anytime claim, stochastic result, or proof of external parameter independence. Comparator/outcome/initial endpoints are allowed.

## Uncertainty and evidential boundary

No ambiguity in the supplied mathematical aliases prevents this reconstruction. The exact canonical value at a tie is unspecified beyond membership in [-1,1]; its computational behavior is not supplied. Requested runtime model/effort are not attested. The packet's typed proposition descriptions and supplied context do not themselves constitute proofs of Q01-Q12. This report supplies neutral semantics only, with no source-fidelity verdict, source acceptance, target-proof validation, chapter/Goal completion, or external/human independence claim.