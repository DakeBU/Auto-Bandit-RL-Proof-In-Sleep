# Source-blind reconstruction: performance v2

Only blind-packet-performance-v2.txt was read. This is a distinct automated reconstruction of six statement headers and their supplied interfaces. It is not a proof, compilation result, source comparison, source acceptance, human review, or whole-package acceptance.

## Shared exact interpretation

Every statement concerns an arbitrary finite-dimensional real inner-product space E with its normed additive group structure. A Domain V supplies a nonempty closed real-convex carrier C. Its actual operator P_C is a classical nearest-point choice: P_C(z) is in C and norm(z-P_C(z))=inf_{w in C} norm(z-w).

Properness of f : E -> EReal means f never equals negative infinity and there exist y0 in E and r in R with f(y0)=coe(r). Define
\[
\partial f(x)=\{g\in E:\forall y\in E,
 f(x)+\operatorname{coe}(\langle g,y-x\rangle)\le f(y)\}.
\]
Every support is global in the ambient space. Write S_C(f) for properness together with a nonempty support set at every point of C. No extra global convexity or differentiability assumption on f is stated.

Let G(f,x) be the actual currentSubgradient: noncomputable classical choice from partial f(x) when nonempty, and zero otherwise. For a schedule a, define
\[
X_0^a=x_1,\quad g_t^a=G(f_t,X_t^a),\quad
X_{t+1}^a=P_C(X_t^a-a_tg_t^a),\quad f_t=\operatorname{loss}(t).
\]
The parameter called x1 is indexed zero. The used losses are t=0,...,T-1; the terminal state is X_T. For every theorem below, its regret and support norms use the same specified trajectory, selector, loss sequence, and initial point. Define
\[
R_T^a(u)=\sum_{t=0}^{T-1}
 [\operatorname{toReal}(f_t(X_t^a))-\operatorname{toReal}(f_t(u))].
\]

The bare regret definition does not assert finiteness: EReal.toReal sends both infinite endpoints to zero. Each header supplies feasible initialization, feasible comparator(s), and S_C(f_t) for all t<T. Through projection these imply feasible iterates; global support at a feasible point can be compared with properness's finite y0 to exclude positive infinity, and properness excludes negative infinity. Thus actual finite real witnesses for both loss values are semantic consequences of the hypotheses. They are not explicitly separately quantified witnesses or finite-value equalities in these headers. Establishing them in a proof requires the relevant reasoning; no proof was inspected.

## Actual diameter and boundedness semantics

The packet explicitly defines
\[
\operatorname{ediam}(C)=\sup_{x\in C}\sup_{y\in C}\operatorname{edist}(x,y)
 \quad\text{in }[0,+\infty],\qquad
\operatorname{diam}(C)=\operatorname{ENNReal.toReal}(\operatorname{ediam}(C)).
\]
Here ENNReal.toReal(+infinity)=0. Bornology.IsBounded(C) is defined as IsCobounded(complement(C)), where IsCobounded means membership in the cobounded filter. In the present metric space its supplied equivalent interpretation is: for any fixed center c there exists a real radius r such that C is contained in the closed ball centered at c of radius r. The packet states that boundedness implies ediam(C) is finite and gives norm(x-y)<=diam(C) for all x,y in C.

Boundedness is therefore essential to using this real diameter as a pairwise-distance upper bound. Merely having a real-valued diam(C) is insufficient: when ediam(C)=+infinity, its toReal image is zero, not an infinite usable bound. The boundedness premise prevents that collapse. This ENNReal diameter conversion and the EReal loss conversion are distinct operations with analogous finite-value precautions. The explicit D hypotheses in other headers directly bound every pairwise distance and do not require D to equal the exact diameter.

## 1. regret_fixed

1. **Objects:** V, a real constant eta, loss sequence, initial x1, natural horizon T, comparator u, and constant schedule a_t=eta.
2. **Quantifiers:** For every such data, every T in N, and every feasible comparator under the following premises.
3. **Hypotheses:** eta>0; x1 in C; S_C(f_t) for every t<T; u in C. No boundedness or support-norm bound is assumed.
4. **Conclusion:**
   \[
   R_T^{\eta}(u)\le\frac{\|x_1-u\|^2}{2\eta}
     +\frac\eta2\sum_{t=0}^{T-1}\|g_t^{\eta}\|^2
     -\frac{\|X_T^{\eta}-u\|^2}{2\eta}.
   \]
5. **Indices/information:** The terminal residual uses X_T, after all T updates; the support sum uses the actual current choices at indices t<T. Eta is one externally supplied constant.
6. **Boundaries:** T=0 is included: regret and sum vanish and the initial/terminal terms cancel. Eta=0 and negative eta are excluded. C may be unbounded.
7. **Scope:** A cumulative upper bound with its terminal residual retained; no optimized rate, equality, or uniform gradient estimate is asserted.

## 2. regret_fixed_coarse

1. **Objects:** The same constant-step data and its actual selected-support trajectory.
2. **Quantifiers:** Every positive eta, every T in N, every qualifying loss sequence and initialization, and every feasible comparator.
3. **Hypotheses:** eta>0, x1 in C, S_C(f_t) for all t<T, u in C; no diameter or gradient bound.
4. **Conclusion:**
   \[
   R_T^{\eta}(u)\le\frac{\|x_1-u\|^2}{2\eta}
      +\frac\eta2\sum_{t=0}^{T-1}\|g_t^{\eta}\|^2.
   \]
5. **Indices/information:** The same current-choice support sum remains, but the terminal residual is absent.
6. **Boundaries:** T=0 gives 0<=norm(x1-u)^2/(2 eta), not endpoint cancellation. The denominator is positive.
7. **Scope:** This is the coarse constant-step upper bound, not a rate without further control of its displayed norm sum.

## 3. regret_variable_bound

1. **Objects:** V, schedule eta : N -> R, loss sequence, x1, natural T, real D, u, and the variable-step trajectory.
2. **Quantifiers:** For every such data and every feasible u under the following assumptions. D is a real upper bound on all pairwise distances.
3. **Hypotheses:** x1 in C; T>0; eta_t>0 for all t<T; eta_{t+1}<=eta_t whenever t+1<T; S_C(f_t) for all t<T; norm(x-y)<=D for every x,y in C; u in C. D>0 is not separately assumed. Nonempty C and the pairwise premise imply D>=0.
4. **Conclusion:**
   \[
   R_T^{\eta}(u)\le\frac{D^2}{2\eta_{T-1}}
      +\sum_{t=0}^{T-1}\frac{\eta_t}{2}\|g_t^{\eta}\|^2
      -\frac{\|X_T^{\eta}-u\|^2}{2\eta_{T-1}}.
   \]
5. **Indices/information:** Both endpoint denominators use eta_{T-1}, the last used step. The terminal state is X_T. Each support term has its own eta_t weight. No positivity or monotonicity outside the used prefix is required.
6. **Boundaries:** T=0 is excluded, so T-1 is a valid used index and its step is positive. At T=1 the adjacent monotonicity condition is vacuous. D=0 is permitted and forces the feasible set to be a singleton, without forcing all ambient selected supports to be zero.
7. **Scope:** A variable-step cumulative bound under nonincreasing positive used steps and an explicit distance bound, retaining the negative terminal residual. D need not be the least bound.

## 4. regret_variable

1. **Objects:** V, bounded carrier C, variable schedule, loss sequence, x1, T, u, and the actual real diameter delta=Metric.diam(C) defined above.
2. **Quantifiers:** Every such bounded V and all data satisfying the used-prefix conditions, for every feasible u.
3. **Hypotheses:** Bornology.IsBounded(C); x1 in C; T>0; eta_t>0 for all t<T; eta_{t+1}<=eta_t whenever t+1<T; S_C(f_t) for all t<T; u in C.
4. **Conclusion:**
   \[
   R_T^{\eta}(u)\le\frac{\delta^2}{2\eta_{T-1}}
      +\sum_{t=0}^{T-1}\frac{\eta_t}{2}\|g_t^{\eta}\|^2
      -\frac{\|X_T^{\eta}-u\|^2}{2\eta_{T-1}}.
   \]
5. **Indices/information:** Delta is the real image of the extended supremum of pairwise distances, not a radius or an initial-comparator distance. The same last-step/terminal-state indexing is retained.
6. **Boundaries:** Boundedness makes ediam finite and delta a true upper bound for all pairs. It cannot be discarded merely because Metric.diam has real type; unbounded extended diameter maps to zero. A singleton has diameter zero. T=0 is excluded; T=1 has no nontrivial adjacent monotonicity condition.
7. **Scope:** This is the bounded-carrier diameter form, not a statement about arbitrary closed convex carriers. The packet now supplies the relevant imported metric interpretation directly.

## 5. regret_tuned_distance

1. **Objects:** V, loss sequence, x1, T, real D,G, one comparator u, and the constant schedule a_t=D/(G sqrt(T)), with T coerced to R.
2. **Quantifiers:** For every such data and each feasible u satisfying the distance condition. The comparator is an argument before the conclusion.
3. **Hypotheses:** x1 in C; T>0; D>0; G>0; S_C(f_t) for all t<T; u in C; norm(x1-u)<=D; and norm(g_t^a)<=G for every t<T on exactly this tuned trajectory.
4. **Conclusion:**
   \[
   R_T^a(u)\le DG\sqrt T,\qquad a_t=D/(G\sqrt T).
   \]
5. **Indices/information:** The support-bound premise refers to the actual chosen supports on the same tuned run, not every support in the ambient space or a different trajectory. D can be chosen for the particular comparator distance; changing D changes the run. T,D,G enter the externally specified schedule.
6. **Boundaries:** T,D,G must all be strictly positive, making the step denominator and step positive. T=0, D=0, G=0 are excluded. No global carrier-diameter bound or boundedness premise is required.
7. **Scope:** A tuned comparator-distance upper bound. It does not derive the actual-support norm bound from Lipschitzness, or promise one comparator-independent run when D is changed between comparators.

## 6. regret_tuned

1. **Objects:** V, loss sequence, x1, positive T,D,G, one constant tuned schedule a_t=D/(G sqrt(T)), and its chosen-support trajectory.
2. **Quantifiers:** Fix V, loss, x1, T,D,G and their hypotheses first; the conclusion then states the bound for every u in C. This is one trajectory serving all feasible comparators.
3. **Hypotheses:** x1 in C; T>0; D>0; G>0; norm(x-y)<=D for all x,y in C; S_C(f_t) for all t<T; norm(g_t^a)<=G for every t<T on the same tuned trajectory.
4. **Conclusion:**
   \[
   \forall u\in C,\quad R_T^a(u)\le DG\sqrt T,
   \qquad a_t=D/(G\sqrt T).
   \]
5. **Indices/information:** The comparator does not enter the schedule, selector, or support-bound hypothesis. The pairwise D bound provides initial-distance control uniformly without changing the run after choosing u.
6. **Boundaries:** Even when C is a singleton, D must be a chosen positive bound; G may be positive when actual support norms vanish. The premises concern only t<T. No future-loss assumption is imposed.
7. **Scope:** A uniform-comparator cumulative upper bound for the specified tuned run, not a lower bound, minimax optimality result, or proof of the gradient-bound premise. D is an upper bound, not necessarily the exact metric diameter.

## Common scope and evidence boundary

The recursion forms X_t from earlier updates and uses the current function f_t to select g_t for X_{t+1}. The selector's explicit arguments contain no comparator, horizon, or future losses, but it receives the whole current function and uses a global classical support choice. No executable local-value oracle model, prefix theorem, or restriction on how external initial points and schedules are generated is supplied by these six headers. Horizon-dependent tuning is explicit in the final two.

The carrier is nonempty and may be lower-dimensional or a singleton. Zero-dimensional E is allowed. No extra loss differentiability, global loss convexity, global finite-value assumption, or bounded-support premise is hidden; the actual support bound appears only where written. The supplied v2 interfaces suffice to interpret the six statements, including metric diameter and boundedness. This does not verify any implementation or proof. Only the new v2 report and receipt were written; no older report, packet, receipt, source, or reviewer output was read or modified. Requested model/effort records the assignment, not independent runtime attestation.
