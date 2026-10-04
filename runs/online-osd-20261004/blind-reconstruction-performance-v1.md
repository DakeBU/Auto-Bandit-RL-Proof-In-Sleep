# Source-blind reconstruction: performance v1

Only blind-packet-performance-v1.txt was read. This is a distinct automated interpretation of six theorem headers, not proof verification, compilation, source comparison, independent human review, or whole-package acceptance.

## Shared objects and notation

All statements universally quantify over a finite-dimensional real inner-product space E with the displayed normed additive group structure. A Domain V has a nonempty, closed, real-convex carrier C. Its actual projection P_C(z) is a classical nearest-point choice in C, satisfying norm(z-P_C(z))=inf_{w in C} norm(z-w).

Properness of f : E -> EReal means that f never takes negative infinity and has at least one actual finite value f(y0)=coe(r), r real. Its subdifferential is the actual global supporting set
\[
\partial f(x)=\{g:\forall y\in E,
 f(x)+\operatorname{coe}(\langle g,y-x\rangle)\le f(y)\}.
\]
Write S_C(f) for properness plus nonemptiness of partial f(x) at every x in C. No global convexity or differentiability assumption on f is explicitly added.

Let G(f,x) denote the packet's currentSubgradient: a noncomputable classical choice from partial f(x) if nonempty, zero otherwise. For a specified schedule a, define
\[
X_0^a=x_1,\quad g_t^a=G(f_t,X_t^a),\quad
X_{t+1}^a=P_C(X_t^a-a_tg_t^a),\qquad f_t=\operatorname{loss}(t).
\]
Every occurrence of a trajectory and a selected support in each bound below uses the same indicated schedule, loss sequence, initial point, and selector. No theorem swaps to an externally prescribed gradient sequence. The initial parameter spelled x1 is X_0; T losses have indices 0,...,T-1 and the terminal state is X_T.

Write
\[
R_T^a(u)=\sum_{t=0}^{T-1}
  [\operatorname{toReal}(f_t(X_t^a))-\operatorname{toReal}(f_t(u))].
\]
The bare definition uses toReal unconditionally, and toReal sends both infinities to zero. In all six headers, feasible initialization, a feasible comparator, and S_C(f_t) for every t<T provide the premises needed for genuine finite losses: projection ensures feasibility of the iterates, support at each feasible point can be compared with properness's finite witness to exclude positive infinity, and properness excludes negative infinity. These are semantic consequences requiring reasoning; the headers do not separately provide equations f_t(v)=coe(r) or cite a finite-loss lemma. No such proof was inspected. Once those consequences are established, R is the sum of actual finite loss differences.

## 1. regret_fixed: exact constant-step endpoint bound

1. **Objects:** V, real eta, loss sequence, initial x1, natural horizon T, comparator u, and the trajectory with a_t=eta for all t.
2. **Quantifiers:** For every such data, including every T in N and every feasible u.
3. **Hypotheses:** eta>0, x1 in C, S_C(f_t) for every t<T, and u in C. There is no domain-diameter or support-norm bound.
4. **Conclusion:**
   \[
   R_T^{\eta}(u)\le
   \frac{\|x_1-u\|^2}{2\eta}
   +\frac\eta2\sum_{t=0}^{T-1}\|g_t^{\eta}\|^2
   -\frac{\|X_T^{\eta}-u\|^2}{2\eta}.
   \]
5. **Indices/information:** The actual support at X_t is for the current f_t. The terminal term uses X_T, not X_{T-1}. Eta is one externally supplied constant for this trajectory; no rule specifies how it was chosen.
6. **Boundaries:** T=0 is allowed: the loss assumption is vacuous, the support sum and regret are zero, and the initial and terminal terms cancel because X_0=x1. Eta=0 is excluded. An unbounded C is allowed.
7. **Scope:** This is a cumulative upper bound retaining the negative terminal residual. It is not an equality, a uniform gradient estimate, an optimized rate, or a bound for a different trajectory.

## 2. regret_fixed_coarse: constant-step coarse bound

1. **Objects:** The same types of data, with the constant eta trajectory and its actual supports.
2. **Quantifiers:** Every positive eta, every natural T, every loss sequence satisfying the next hypotheses, and every feasible comparator.
3. **Hypotheses:** eta>0, x1 in C, S_C(f_t) for all t<T, u in C. No bounded-domain assumption occurs.
4. **Conclusion:**
   \[
   R_T^{\eta}(u)\le
   \frac{\|x_1-u\|^2}{2\eta}
     +\frac\eta2\sum_{t=0}^{T-1}\|g_t^{\eta}\|^2.
   \]
5. **Indices/information:** The support sum remains over t<T on the same actual constant-step trajectory. There is no terminal-distance term in this statement.
6. **Boundaries:** T=0 is allowed and gives 0<=norm(x1-u)^2/(2 eta), with no cancellation asserted. Eta remains strictly positive. Zero supports are allowed.
7. **Scope:** This is a coarser upper bound with the terminal residual absent. The header does not assert a numerical rate without further control of the displayed support sum.

## 3. regret_variable_bound: explicit pairwise-distance bound

1. **Objects:** V, arbitrary real schedule eta_t, loss sequence, x1, positive natural horizon T, real D, comparator u, and their actual variable-step trajectory.
2. **Quantifiers:** For every such data and every feasible u satisfying all hypotheses. D is a supplied bound, not required to be a minimal diameter.
3. **Hypotheses:** x1 in C; T>0; eta_t>0 for every t<T; eta_{t+1}<=eta_t whenever t+1<T; S_C(f_t) for all t<T; and for every x,y in C, norm(x-y)<=D; u in C. D has no explicit positivity premise. Since C is nonempty, the pairwise condition implies D>=0.
4. **Conclusion:**
   \[
   R_T^{\eta}(u)\le
   \frac{D^2}{2\eta_{T-1}}
   +\sum_{t=0}^{T-1}\frac{\eta_t}{2}\|g_t^{\eta}\|^2
   -\frac{\|X_T^{\eta}-u\|^2}{2\eta_{T-1}}.
   \]
5. **Indices/information:** Both endpoint denominators use the last used step eta_{T-1}; the terminal state is X_T. The weight in each support term is its own eta_t. No condition is imposed on eta_T or later steps; monotonicity is only within the finite used prefix.
6. **Boundaries:** T=0 is excluded, so natural subtraction T-1 names a used index and its denominator is positive. At T=1 the monotonicity condition is vacuous. D=0 is allowed and forces C to be a singleton; selected ambient supports can still have nonzero norms. There is no bounded-support hypothesis.
7. **Scope:** This is a bound for a positive, nonincreasing used step prefix with an explicit all-pairs distance bound. It retains the exact displayed terminal residual and does not state an arbitrary-schedule result.

## 4. regret_variable: metric-diameter form

1. **Objects:** The same variable-step data, with Metric.diam C replacing a separately supplied D.
2. **Quantifiers:** Every V with bounded carrier, every schedule/loss sequence, feasible initialization, positive T, and feasible u satisfying the prefix hypotheses.
3. **Hypotheses:** Bornology.IsBounded C; x1 in C; T>0; positive eta_t for t<T; nonincreasing adjacent used steps; S_C(f_t) for all t<T; u in C.
4. **Conclusion:**
   \[
   R_T^{\eta}(u)\le
   \frac{(\operatorname{Metric.diam}C)^2}{2\eta_{T-1}}
   +\sum_{t=0}^{T-1}\frac{\eta_t}{2}\|g_t^{\eta}\|^2
   -\frac{\|X_T^{\eta}-u\|^2}{2\eta_{T-1}}.
   \]
5. **Indices/information:** The same eta_{T-1}/X_T distinction and same actual supports apply. Boundedness is an extra carrier property beyond the nonempty/closed/convex Domain fields.
6. **Boundaries:** The diameter is not a radius or an initial-comparator distance. For a nonempty bounded metric set its usual mathematical interpretation is the supremum of all pairwise distances. The packet names Metric.diam but does not expand its imported definition or conventions outside this bounded setting; none are inferred here. A singleton has diameter zero. T=0 remains excluded.
7. **Scope:** This is the bounded-carrier metric-diameter version of the displayed variable-step form. The exact imported implementation/definition of Metric.diam is not supplied, so that dependency cannot be audited from the packet alone.

## 5. regret_tuned_distance: comparator-distance tuning

1. **Objects:** V, loss sequence, feasible x1, T, positive real D and G, one feasible comparator u, and the constant schedule a_t=D/(G sqrt(T)), with T coerced to a real inside sqrt.
2. **Quantifiers:** For every such data and every u satisfying the distance and trajectory-bound conditions below. This header fixes u as an argument rather than placing all comparators in its conclusion.
3. **Hypotheses:** T>0, D>0, G>0; S_C(f_t) for all t<T; norm(x1-u)<=D; and for every t<T, norm(g_t^a)<=G on exactly the tuned trajectory a_t=D/(G sqrt(T)). Initial point and comparator must be feasible.
4. **Conclusion:**
   \[
   R_T^a(u)\le DG\sqrt{T},\qquad a_t=\frac D{G\sqrt T}.
   \]
5. **Indices/information:** The gradient premise is about the actually selected supports on this schedule, not all supports at all feasible points, not another run, and not merely a symbolic bound on a placeholder gradient. D may be chosen in relation to this comparator, so changing D changes the trajectory. The schedule uses the horizon and supplied D,G externally.
6. **Boundaries:** T,D,G are strictly positive, so sqrt(T), G sqrt(T), and the tuned step are positive. T=0, D=0, and G=0 are excluded even if a limiting case might admit a different result. No all-pairs diameter bound or bounded-carrier premise is required.
7. **Scope:** This is a comparator-distance-based tuned cumulative bound. It does not prove the actual-support norm premise from Lipschitzness or supply a comparator-independent way to choose D. Noncomputable support selection remains part of the algorithm.

## 6. regret_tuned: one tuned trajectory, all feasible comparators

1. **Objects:** V, loss sequence, feasible x1, positive T,D,G, and one constant tuned schedule a_t=D/(G sqrt(T)).
2. **Quantifiers:** After fixing V, loss, x1, T, D, G and all hypotheses, the conclusion quantifies over every u in C. Thus the same tuned trajectory and the same constants serve all comparators.
3. **Hypotheses:** T>0, D>0, G>0; all pairwise feasible distances are <=D; S_C(f_t) for every t<T; and norm(g_t^a)<=G for every t<T along exactly this tuned trajectory. x1 is feasible.
4. **Conclusion:**
   \[
   \forall u\in C,\quad R_T^a(u)\le DG\sqrt T,
   \qquad a_t=\frac D{G\sqrt T}.
   \]
5. **Indices/information:** No u enters the selector, schedule, or support-bound premise. The all-pairs D bound provides initial-distance control for every feasible comparator simultaneously; this does not retune separately after selecting each u.
6. **Boundaries:** T,D,G remain strictly positive; a singleton carrier is allowed but D must still be a chosen positive upper bound. The actual selected support norm can be zero while G is positive. Loss assumptions are only for t<T. No condition on future losses is imposed.
7. **Scope:** This is a uniform-over-feasible-comparators cumulative upper bound for one fixed tuned run. It is not a lower bound, optimality/minimax claim, computable-oracle guarantee, or justification of the support-bound assumption. The explicit real D is an upper bound on diameter, not necessarily Metric.diam C itself.

## Common information and evidence boundaries

The recursion queries the current function at X_t and uses its chosen support to form X_{t+1}. G takes only the current whole function and point as explicit inputs, with no comparator or future loss parameter. Nevertheless it uses a global support set and classical choice. These headers do not state a prefix-invariance theorem, constrain how an external initialization or step schedule was obtained, or establish an executable local-information model. Horizon-dependent tuning is explicit in the final two statements.

There is no hidden support-existence assumption outside C and no global loss differentiability, boundedness, or convexity premise. E may be zero-dimensional, C may be lower-dimensional, and all actual finite differences vanish in the one-point ambient case. Different schedules generally define different trajectories; each theorem's loss sum and gradient premise remain bound to its own specified trajectory.

The only unexpanded quantity needed for a literal imported-definition audit is Metric.diam (and the named standard boundedness predicate); their ordinary bounded-metric-set interpretation is stated separately above. All six numerical formulas, their visible quantifiers, and their explicit assumptions are provided. No proof body, source identity, compilation evidence, or proof-term dependency graph is provided or inferred. Only this new report and matching receipt were written; older files were not read or modified.
