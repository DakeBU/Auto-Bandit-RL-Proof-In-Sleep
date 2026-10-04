# Source-blind reconstruction: causality v1

Only blind-packet-causality-v1.txt was read. This is a distinct automated decoding of eight statement headers and supplied interfaces, not a proof check, compilation result, source comparison, human review, or whole-package acceptance.

## Shared exact semantics and notation

All claims are universally quantified over finite-dimensional real inner-product spaces E, with the displayed normed additive group structure, and all their displayed parameters satisfying their hypotheses. A Domain V supplies a nonempty, closed, real-convex set C=V.carrier. Its actual projection P_C(z) is a classical nearest-point choice with P_C(z) in C and norm(z-P_C(z))=inf_{w in C} norm(z-w). Completeness is supplied by finite-dimensionality.

For f : E -> EReal, properness means that f never equals negative infinity and that there exist y0 in E and r in R with f(y0)=coe(r). The finite witness need not lie in C. Define
\[
\partial f(x)=\{g\in E:\forall y\in E,
 f(x)+\operatorname{coe}(\langle g,y-x\rangle)\le f(y)\}.
\]
These are global ambient supporting inequalities. Write S_C(f) for properness together with nonemptiness of partial f(x) at every x in C. It contains no explicit global convexity or differentiability assumption on f.

Let G(f,x) be the displayed currentSubgradient: a local-classical, noncomputable choice from partial f(x) when nonempty, otherwise zero. Set
\[
X_0=x_1,\qquad X_{t+1}=P_C(X_t-\eta_t G(f_t,X_t)),
\qquad f_t=\operatorname{loss}(t),\quad g_t=G(f_t,X_t).
\]
The parameter spelled x1 is the zero-indexed initial point. Unless another run is explicitly marked, X uses V, eta, loss, and x1. Write q^R(x)=toReal(q(x)). toReal(coe(r))=r, but toReal sends both infinities to zero; it is not itself evidence of finiteness.

The regret definition is R_T(u)=sum_{t=0}^{T-1}(f_t^R(X_t)-f_t^R(u)). It has no built-in feasibility, finite-value, positive-step, or loss-regularity premises. T=0 gives zero. None of the eight headers asserts a cumulative bound for this quantity.

## 1. currentSubgradient_mem

1. **Objects:** Any shared E and V, f : E -> EReal, x in E, and G(f,x).
2. **Quantifiers:** For every such f and x, under the following hypotheses.
3. **Hypotheses:** S_C(f) and x in C; no step size or sequence occurs.
4. **Conclusion:** G(f,x) belongs to partial f(x), i.e. for every ambient y, f(x)+coe(<G(f,x),y-x>)<=f(y).
5. **Information/indexing:** This is a current-function/current-point algorithmic selection fact, not a temporal or performance inequality.
6. **Boundaries:** No comparator, differentiability, norm bound, or nonzero support is required. The hypothesis ensures the nonempty branch, so the unsupported zero fallback is not used here. Zero is allowed when it is a true support.
7. **Scope:** It validates the selected vector under these premises, not arbitrary fallback cases or an executable oracle.

## 2. finite_loss

1. **Objects:** Any shared E and V, function f and point x.
2. **Quantifiers:** For every f and every x satisfying the next conditions.
3. **Hypotheses:** S_C(f) and x in C.
4. **Conclusion:** f(x)=coe(f^R(x)), an equality in EReal. Thus f^R(x) is an actual finite real witness for f(x).
5. **Information/indexing:** This is a value/representation fact at one point, with no sequence or performance bound.
6. **Boundaries:** Properness rules out negative infinity. A global support at x can be compared with properness's finite witness y0, ruling out positive infinity at x. Positive infinity outside C is not excluded. The finite comparison witness need not be feasible.
7. **Scope:** The claim establishes finiteness at feasible x under S_C(f); it does not infer finiteness merely from applying toReal or from properness alone at arbitrary points.

## 3. iterate_mem

1. **Objects:** Any shared V, arbitrary eta : N -> R, arbitrary loss : N -> E -> EReal, initial x1, and natural t.
2. **Quantifiers:** For every entire schedule and loss sequence, every feasible initial point, and every t in N.
3. **Hypotheses:** Only x1 in C beyond the shared Domain and space assumptions. No positivity or subdifferentiability premise is present.
4. **Conclusion:** X_t belongs to C.
5. **Information/indexing:** This is an algorithmic feasibility invariant, including X_0=x1. Successors use the actual feasible projection even when the selector uses its fallback.
6. **Boundaries:** t=0 is covered. Step sizes can be zero or negative; losses can have empty support sets and infinite values. Initial feasibility is required for this all-t statement.
7. **Scope:** Feasibility does not establish that the selected vector is a support, that losses are finite, or that any performance bound holds.

## 4. iterate_prefix

1. **Objects:** One V and one shared initial x1, two schedules eta and eta', two loss sequences loss and loss', and t in N.
2. **Quantifiers:** For every such pair of schedules and sequences and every t.
3. **Hypotheses:** For every s<t, eta_s=eta'_s and loss_s=loss'_s. The latter is equality of the entire functions E -> EReal, not equality only at previously queried points. No initial-feasibility, positivity, or loss-regularity hypothesis appears.
4. **Conclusion:** X_t(V,eta,loss,x1)=X_t(V,eta',loss',x1).
5. **Information/indexing:** The iterate at time t depends on the strict prefix s<t with fixed V and x1. Neither loss_t nor eta_t must agree. At t=0 the hypotheses are empty and both iterates equal x1. This header explicitly states a prefix-invariance property.
6. **Boundaries:** Later schedules and losses may differ arbitrarily. This does not compare different feasible sets or different initial points. At t=1 only the index-0 update is constrained.
7. **Scope:** This is a structural causality fact about the recursion. It does not constrain how external x1 or eta were generated, guarantee independence from future data embedded in those inputs, or establish an oracle model using only observed values. G receives the full current function.

## 5. iterate_support

1. **Objects:** Shared V, arbitrary schedule and loss sequence, x1, and a selected natural t.
2. **Quantifiers:** For every schedule, sequence, feasible initial point, and t satisfying the current-loss condition.
3. **Hypotheses:** x1 in C and S_C(f_t). No condition on any other loss f_s or on any step size appears.
4. **Conclusion:** g_t belongs to partial f_t(X_t), hence its inequality holds against every ambient test point y.
5. **Information/indexing:** X_t is the point formed from the earlier updates; the support is for the current loss at that point. This is an algorithmic support-validity fact.
6. **Boundaries:** Prior losses may have used zero fallback and arbitrary real steps; their projected iterates remain feasible. t=0 is included. Current support validity does not need eta_t>0.
7. **Scope:** It validates the selected current support only under the current loss condition; it is not a bound on that support or on regret.

## 6. iterate_finite_loss

1. **Objects:** Shared V, schedule, loss sequence, initial point, t, and comparator u in E.
2. **Quantifiers:** For every such data and every feasible u.
3. **Hypotheses:** x1 in C, S_C(f_t), and u in C. No positivity and no other-round loss conditions are stated.
4. **Conclusion:** Both EReal equalities hold: f_t(X_t)=coe(f_t^R(X_t)) and f_t(u)=coe(f_t^R(u)).
5. **Information/indexing:** This establishes actual finite witnesses for both terms in the current round's difference, evaluated using the same loss f_t. It is a representation fact, not a performance inequality.
6. **Boundaries:** t=0 is included. The comparator need not equal an iterate. Infinite loss values elsewhere remain allowed. Both finite equalities are required; merely projecting both values to R would not provide them.
7. **Scope:** The claim is at a selected t. Applying it at every round of a horizon would require the current-loss premise for every such round; no blanket all-loss condition is hidden in this header.

## 7. one_step_chain

1. **Objects:** Shared V, schedule, loss sequence, feasible initial point, selected t, comparator u, actual g_t and actual next iterate X_{t+1}.
2. **Quantifiers:** For every such data satisfying the next conditions, with the selected g_t fixed by the definition rather than a separately quantified arbitrary support.
3. **Hypotheses:** x1 in C, eta_t>0, S_C(f_t), and u in C. Only the current step must be positive and only the current loss must satisfy S_C.
4. **Conclusion:** The exact conjunction is
   \[
   \eta_t(f_t^R(X_t)-f_t^R(u))\le\eta_t\langle g_t,X_t-u\rangle
   \]
   and
   \[
   \eta_t\langle g_t,X_t-u\rangle
   \le\frac{\|X_t-u\|^2}{2}
      -\frac{\|X_{t+1}-u\|^2}{2}
      +\frac{\eta_t^2}{2}\|g_t\|^2.
   \]
5. **Information/indexing:** This is a single-step performance comparison for the actual algorithm. X_{t+1}=P_C(X_t-eta_t g_t); the negative distance is to the true next iterate, not an independently assigned point. The current loss is evaluated before this update.
6. **Boundaries:** Eta_t=0 and negative eta_t are excluded here; earlier step sizes remain unrestricted. The finite-value hypotheses justify a genuine loss difference. t=0 is included with X_0=x1.
7. **Scope:** The claim exposes both stages of the inequality chain. It asserts no cumulative regret, telescoping across varying eta, uniform support bound, or convergence rate.

## 8. one_step

1. **Objects:** The same algorithmic objects X_t, X_{t+1}, g_t and comparator u for a selected round t.
2. **Quantifiers:** For every V, schedule, loss sequence, initial point, t, and comparator satisfying the listed conditions.
3. **Hypotheses:** Exactly x1 in C, eta_t>0, S_C(f_t), and u in C, beyond shared structure.
4. **Conclusion:**
   \[
   f_t^R(X_t)-f_t^R(u)
   \le\frac{\|X_t-u\|^2-\|X_{t+1}-u\|^2}{2\eta_t}
      +\frac{\eta_t}{2}\|g_t\|^2.
   \]
   The entire difference of squared distances is divided by 2 eta_t. The support correction is eta_t/2 times its squared norm.
5. **Information/indexing:** This is the scalar single-round performance bound for the actual chosen-support update, now without the intermediate inner product. It compares the current loss at X_t with the same loss at u.
6. **Boundaries:** Positive eta_t makes the denominator nonzero. No global norm bound, constant-step premise, or condition on earlier losses is stated. Zero-dimensional E reduces all vectors and distances to zero, and the finite difference is zero.
7. **Scope:** It is a one-step upper bound only. A regret theorem would require further quantified round hypotheses and an explicit summation argument; no such theorem is among these eight statements.

## Common boundaries and evidence limits

C is nonempty but may be a singleton or lower-dimensional. No interior assumption is imposed. E may have dimension zero; then C is its only point, and proper losses are finite there. Closedness and convexity are assumptions on C, not unstated global regularity of loss functions. There is no bounded-domain, bounded-support, globally finite-loss, differentiability, or global-convexity premise on the arbitrary losses. The selector is classical and noncomputable; no deterministic executable selection algorithm or numerical accuracy specification is supplied.

The first six headers are selection, finite-value, feasibility, and strict-prefix facts. The last two are current-round performance statements. Regret is only defined in the supplied context. The packet provides enough semantic interfaces to interpret these eight statements; it provides no theorem bodies or evidence that any header compiles or is proved. Source identities and a source-fidelity verdict are absent. Apparent relationships between the statements are mathematical context, not an inspected proof-term dependency graph.

Only this new report and its matching receipt were written. No older files were read or changed. Requested model and effort in the receipt record the assignment, not independent runtime verification.
