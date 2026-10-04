# Source-blind reconstruction of twelve statements

Only blind-packet-v1.md from this run was read. This report decodes the supplied mathematical statements and interfaces. It does not verify proofs, compilation, literature identity, source fidelity, or whole-package completion, and is not an independent human review.

## Common semantics

All scalar points and supports lie in R. Define ell_y(x)=coe(|x-y|) in EReal. It is finite everywhere. Its actual global subdifferential is
\[
\partial\ell_y(x)=\{g\in\mathbb R:\forall z\in\mathbb R,
 |x-y|+g(z-x)\le |z-y|\}.
\]
This real form is justified by the displayed finite coercions; the original definition compares EReal values with the real inner product embedded. The test points z are all reals, not just feasible points.

Properness means no negative-infinite values and at least one actual finite value. SubdifferentiableOn V f conjoins properness with support existence at every point of the carrier. The actual feasible carrier here is C=[0,1], a nonempty closed convex set. Its project operator is the chosen true nearest point in C.

Write G(y,x)=currentSubgradient(ell_y,x). It is the fixed classical current-function/current-point choice from the nonempty support set, with zero fallback only when that set is empty. Classical choice does not specify a numerical tie-breaking rule. In particular, at x=y no claim here requires G to be zero. On the supplied loss family the displayed full support characterization is always nonempty, so the fallback does not describe its supported cases.

For a schedule a : N -> R and observations y : N -> R, write
\[
X_0^{a,y}=x_1,\qquad
X_{t+1}^{a,y}=P_C(X_t^{a,y}-a_tG(y_t,X_t^{a,y})).
\]
The parameter spelled x1 is the zero-indexed initial point. The state X_t uses inputs with indices strictly less than t, then the current observation y_t defines the loss/support used to form X_{t+1}. The selector uses the whole current function and point, not an executable local-value oracle. The prefix statements do not constrain the external generation of the initial point or schedule.

## result_1

1. **Objects:** Arbitrary real y,x, the translated absolute loss, and a(z)=coe(|z|).
2. **Quantifiers:** For every y in R and every x in R.
3. **Hypotheses:** None beyond the scalar context.
4. **Conclusion:** The full set equality partial ell_y(x)=partial a(x-y). Equivalently, every real g satisfies the left global inequalities if and only if it satisfies all inequalities |x-y|+g(w-(x-y))<=|w| for every real w.
5. **Information:** This is a translation identity between entire support sets, not an algorithmic step or a selected-vector identity alone.
6. **Boundaries:** It includes x=y and all real values, without interval restrictions.
7. **Scope:** Both inclusions are asserted; no translated gradient variable, derivative hypothesis, or loss restriction is introduced.

## result_2

1. **Objects:** Real y,x and the entire global support set at x.
2. **Quantifiers:** For all y,x with y<x.
3. **Hypotheses:** Strict inequality y<x only.
4. **Conclusion:** partial ell_y(x)={1}: g is a global support exactly when g=1. Thus 1 belongs and every other real number is excluded.
5. **Information:** A pointwise complete characterization; the canonical choice consequently has no choice among different values in this branch.
6. **Boundaries:** Equality x=y is excluded; x,y need not be feasible or bounded.
7. **Scope:** No differentiability or probability assumption is supplied or needed as a premise of the stated claim.

## result_3

1. **Objects:** Arbitrary real y and the support set at the equal query x=y.
2. **Quantifiers:** For every y in R.
3. **Hypotheses:** Evaluation is at y itself; no other restrictions.
4. **Conclusion:** partial ell_y(y)=[-1,1]. Equivalently every g is a global support if and only if -1<=g<=1.
5. **Information:** Every point of this entire closed interval belongs; no single preferred support is asserted.
6. **Boundaries:** Both -1 and 1 are included, as is zero. No feasible-interval condition on y occurs.
7. **Scope:** The classical selector may choose any member of this set consistently with its definition. The header does not select zero or assert a unique derivative.

## result_4

1. **Objects:** Real y,x and the entire global support set at x.
2. **Quantifiers:** For all x,y with x<y.
3. **Hypotheses:** Strict inequality x<y only.
4. **Conclusion:** partial ell_y(x)={-1}, including membership of -1 and exclusion of every other g.
5. **Information:** Complete scalar branch characterization, rather than merely a norm bound.
6. **Boundaries:** The equal case is excluded; the values need not lie in [0,1].
7. **Scope:** This branch concerns all ambient global supports, not only feasible-direction supports.

## result_5

1. **Objects:** Arbitrary real y,x and partial ell_y(x).
2. **Quantifiers:** For every y,x in R, with no extra assumptions.
3. **Hypotheses:** The branch conditions are evaluated in order: y<x; otherwise x=y; otherwise x<y by real trichotomy.
4. **Conclusion:**
   \[
   \partial\ell_y(x)=
   \begin{cases}\{1\},&y<x,\\[-1,1],&x=y,\\\{-1\},&x<y.\end{cases}
   \]
   Each branch is full set equality, meaning membership if and only if the displayed singleton or interval condition holds.
5. **Information:** It characterizes every true global support, not an arbitrary assumed bounded response.
6. **Boundaries:** The equality case includes both interval endpoints and is nonempty. All three branches are nonempty and cover all real pairs.
7. **Scope:** No support outside [-1,1] belongs, but the equality branch does not determine a unique canonical numerical value.

## result_6

1. **Objects:** Real y, ell_y and the actual Domain with carrier [0,1].
2. **Quantifiers:** For every real y, including y outside [0,1].
3. **Hypotheses:** No restriction on y.
4. **Conclusion:** ell_y is proper, and for every x in [0,1] its ambient global support set is nonempty. Properness expands to absence of negative infinity at every real point plus existence of a real-valued witness somewhere.
5. **Information:** This is admissibility for the supplied feasible domain; it has no temporal content.
6. **Boundaries:** Feasible endpoints 0 and 1 are included. Support tests remain global over R. Loss finiteness also follows directly from its finite real coercion definition.
7. **Scope:** It does not weaken supports to feasible-only inequalities, and does not require observations to be feasible.

## result_7

1. **Objects:** Arbitrary real y,x,g.
2. **Quantifiers:** For every y,x and every g belonging to partial ell_y(x).
3. **Hypotheses:** Actual global-support membership, with no restriction on x or y.
4. **Conclusion:** norm(g)=|g|<=1.
5. **Information:** Bounds every genuine support, not just the chosen one.
6. **Boundaries:** Equality in the bound is allowed; at x=y any g in [-1,1] is covered. No strictness or positive lower bound is asserted.
7. **Scope:** It does not say that an arbitrary vector is a support merely because its norm is at most one in the strict branches.

## result_8

1. **Objects:** Arbitrary real y,x and the actual selected G(y,x).
2. **Quantifiers:** For every y in R and x in [0,1].
3. **Hypotheses:** Feasibility of x; y is unrestricted.
4. **Conclusion:** |G(y,x)|<=1.
5. **Information:** The bound is for the fixed current-choice selector applied to the actual loss/query, not a freely specified proxy vector.
6. **Boundaries:** Endpoints of [0,1] and x=y are covered. No tie-break value at equality is imposed.
7. **Scope:** The displayed header carries a feasible-query premise, even though other supplied mathematical statements cover all real supports.

## result_9

1. **Objects:** Real eta,y,x and the actual projected step for ell_y.
2. **Quantifiers:** For every real eta,y,x.
3. **Hypotheses:** None: eta need not be positive and x need not be feasible.
4. **Conclusion:**
   \[
   \operatorname{step}(C,\eta,\ell_y,x)
       =\min\{\max\{x-\eta G(y,x),0\},1\}.
   \]
5. **Information:** The actual nearest-point projection equals clipping the actual selected-support update to [0,1]. It is not a redefinition with an externally chosen sign at equality.
6. **Boundaries:** Zero and negative eta are allowed. Clipping includes both endpoints. At eta=0 it clips x, which equals x only if x is feasible.
7. **Scope:** An exact update identity, without a regret bound or a positivity restriction silently added.

## result_10

1. **Objects:** Two real schedules a,a', two real observation sequences y,y', the same initial x1 in R, and t in N.
2. **Quantifiers:** For every such pair of input sequences and schedules, every common initial point, and every t.
3. **Hypotheses:** For every s<t, a_s=a'_s and y_s=y'_s. No initial-feasibility, observation-range, or step-positivity assumption occurs.
4. **Conclusion:** X_t^{a,y}=X_t^{a',y'}.
5. **Information:** Exact strict-prefix invariance. Current and future inputs at indices >=t may differ. At t=0 both sides equal the common x1 under vacuous prefix premises.
6. **Boundaries:** This does not compare different initial points. At t=1 only the index-0 schedule and observation must agree. Observations outside [0,1] and arbitrary real steps are permitted.
7. **Scope:** Establishes structural input ordering for this recursion. It does not impose statistical independence, an executable oracle, or causal external selection of x1 and schedules.

## result_11

1. **Objects:** A real observation sequence y, feasible initial x1, natural horizon T, and the single constant-step run with a_s^{(T)}=1/sqrt(T). Write X_t^{(T)} for that run.
2. **Quantifiers:** For every y,x1,T satisfying the hypotheses, the conclusion holds for every comparator u in [0,1] on the same run.
3. **Hypotheses:** x1 in [0,1], T>0, and y_t in [0,1] for every t<T. No condition is imposed on later observations.
4. **Conclusion:**
   \[
   \forall u\in[0,1],\quad
   \sum_{t=0}^{T-1}(|X_t^{(T)}-y_t|-|u-y_t|)\le\sqrt T.
   \]
5. **Information:** For this horizon the step is constant throughout the run. The first loss uses X_0=x1. Supports and states arise from the actual current-choice recursion, with past observations determining X_t and y_t used for the subsequent update. No comparator enters the trajectory.
6. **Boundaries:** T=0 is excluded, so sqrt(T)>0 and the chosen step is positive. Comparators may be endpoints. All summands are ordinary finite real absolute losses without toReal ambiguity.
7. **Scope:** A finite-horizon cumulative upper bound uniform over feasible comparators for one prescribed-horizon run. Changing T generally changes every step size and thus the run; this is not an anytime schedule a_t=1/sqrt(t).

## result_12

1. **Objects:** One fixed infinite real observation sequence y, one fixed feasible x1, one fixed feasible comparator u, and any positive real epsilon. For each horizon T use its own constant-step run X^{(T)} with a_s^{(T)}=1/sqrt(T).
2. **Quantifiers:** For every y,x1 with the hypotheses, every u in [0,1], and every epsilon>0, there exists a natural N such that for every natural T>=N the inequality below holds. This expands eventually atTop on N.
3. **Hypotheses:** x1 in [0,1], y_t in [0,1] for every t in N, u in [0,1], epsilon>0. The sequence-range premise is for all times, unlike a single finite prefix.
4. **Conclusion:**
   \[
   \exists N\in\mathbb N\;\forall T\ge N,\qquad
   \frac1T\sum_{t=0}^{T-1}
       (|X_t^{(T)}-y_t|-|u-y_t|)<\varepsilon.
   \]
   Here T in the real division is coerced to R. The inequality is strict and one-sided.
5. **Information:** Across T this is a family of separately prescribed-horizon trajectories with the same observations, initial point, and comparator. It is not the prefix-average of a single fixed schedule. The threshold appears after y,x1,u,epsilon and may depend on them; no stronger uniform-threshold quantifier is stated.
6. **Boundaries:** There is no pointwise T>0 premise because the conclusion is eventual; a threshold may exclude T=0 and every other finite exceptional set. The packet does not need a T=0 numerical convention to interpret the eventual property. Negative average regret is permitted.
7. **Scope:** This is eventual upper control below every positive epsilon. It is not convergence of signed average regret to zero, not a bound on its absolute value, and not an absolute Big-O statement. It provides no lower control and no quantitative threshold formula.

## Completeness and evidence boundary

The supplied interfaces identify the feasible set, real scalar operations, global support meaning, finite loss coercion, classical selection, actual projection, recursion, range indexing and eventual filter sufficiently to interpret these twelve statements. No additional imported-meaning gap prevents their reconstruction. This does not establish that the theorem headers are proved or compiled. The package includes no source identity or proof bodies, and none were sought.

Only this new report and its receipt were written. The recorded requested model and medium effort describe the assignment; runtime identity was not independently attested.
