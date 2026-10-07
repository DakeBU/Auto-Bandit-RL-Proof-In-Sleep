# Independent source-blind reconstruction, v1

Actor: `/root/osd_blind`. Requested model: GPT-6 Astra; requested reasoning effort: medium; runtime model attested: false. Sole inspected input: `blind-packet-v1.md` in this run. No source text, repository/history, other files, proof bodies, literature identity, or prior verdict was inspected. This report decodes proposition descriptions, not proofs. It makes no source-acceptance, chapter-completion, or Goal-completion claim.

## Shared notation and exact context

Write V for the carrier of a nonempty closed convex subset of a real inner-product space E. The ambient packet assumes finite dimension for projection/iteration claims. The elaborated P02 and P03 actually require only the normed additive group and real inner-product structure, not finite dimension. The projection Pi_V(z) belongs to V and minimizes distance to z over V. The supplied projection comparison is ||Pi_V(z)-u|| <= ||z-u|| for u in V; it is not an assumption about a desired loss-performance inequality.

An extended-real function f is proper here exactly when f(x) is never minus infinity at any ambient x, and f(a) is a finite real value for at least one ambient a. Its support set at x is

\[
\partial f(x)=\{g\in E:\ \forall y\in E,\quad f(x)+\langle g,y-x\rangle\le f(y)\},
\]

with the inner product embedded in the extended reals. This tests every ambient y, not only V, its interior, or the effective domain. Define S_V(f) to mean properness plus nonemptiness of this global support set at every x in V. It does not assert a separately specified global convexity hypothesis. The supplied effective domain is {x : f(x) < +infinity}; properness excludes minus infinity there. Properness alone does not mean f is finite everywhere, or even everywhere on V. Properness together with a support at a query excludes +infinity at that query; P03 and P07 explicitly express the finite-value conclusions used for real loss differences.

Let c(f,x) be the packet's fixed classical choice of an element of the support set if it is nonempty, and zero otherwise. It has only f and x as arguments. It is a noncomputable mathematical choice, not an executable oracle, minimum-norm choice, specified tie-breaking implementation, or quantification over all possible legal selection policies. The zero fallback does not itself certify support membership when the set is empty.

To avoid shifting the packet's indexing, put x_0 = a, where a denotes the argument named x1 in the code, and

\[
g_t=c(f_t,x_t),\qquad x_{t+1}=\Pi_V(x_t-\eta_t g_t),\qquad
R_T(u)=\sum_{t=0}^{T-1}\bigl((f_t(x_t)).\mathrm{toReal}-(f_t(u)).\mathrm{toReal}\bigr).
\]

All x_t, g_t, and R_T in a formula refer to the same specified run unless explicitly comparing two runs. `toReal` is a total operation in the definitions; treating these summands as ordinary real loss differences requires the hypotheses establishing finiteness, not an unconditional identification of extended-real values with reals. The domain, initial value a, schedule, and loss sequence are externally supplied. Statements do not impose a probability model, filtration, measurability, stochastic adversary, executable feedback oracle, or simultaneous anytime guarantee.

For each proposition the seven semantic slots below are: (1) objects and ambient structure; (2) quantifier and information scope; (3) hypotheses; (4) specified operation or run; (5) conclusion; (6) exact constants and indices; (7) degeneracies and limits. These labels are an organizational schema for the reconstruction; the packet did not supply names for the seven slots.

## P01

1. **Objects/structure.** Finite-dimensional E, domain V, extended-real f, scalar eta, ambient points x,u and vector g.
2. **Scope.** Universal over all these objects under the hypotheses. The current query x is arbitrary in E: there is NO x in V hypothesis. Only comparator u must be feasible. This proposition accepts any actual global support g at x, rather than requiring c(f,x).
3. **Hypotheses.** S_V(f), eta > 0, u in V, and g in partial f(x). Properness plus the assumed support makes f(x) finite even for an infeasible x; feasibility and S_V(f) make f(u) finite.
4. **Operation/run.** Set x_plus = Pi_V(x-eta g). This is a concrete projected single step, with no supplied single-step loss bound as premise.
5. **Conclusion.** Both links of the following chain hold:
   \[
   \eta(f(x)^{\rm r}-f(u)^{\rm r})\le\eta\langle g,x-u\rangle
   \le\frac{\|x-u\|^2}{2}-\frac{\|x_+-u\|^2}{2}+\frac{\eta^2}{2}\|g\|^2,
   \]
   where superscript r denotes toReal of a finite value.
6. **Constants/indices.** Each potential has denominator 2, not 2 eta; the norm penalty has eta squared divided by 2. No horizon or recursion is present.
7. **Limits.** Eta = 0 and negative eta are outside the statement. No bounded-domain or bounded-support assumption is present. No restriction to interior queries or local support inequalities may replace the global support premise.

## P02

1. **Objects/structure.** Real inner-product E, V, f, and x. The elaborated type has no finite-dimensional requirement.
2. **Scope.** Every feasible x for each V,f satisfying S_V(f); not every ambient x.
3. **Hypotheses.** S_V(f) and x in V.
4. **Operation/run.** The fixed choice c(f,x), formed only from the current function and query.
5. **Conclusion.** c(f,x) belongs to partial f(x).
6. **Constants/indices.** No schedule, time, horizon, norm constant, or numerical bound.
7. **Limits.** No legality conclusion for an empty support set or an arbitrary infeasible query. This certifies the selected element; it does not supply a computable selection method or quantify over all policies.

## P03

1. **Objects/structure.** Real inner-product E, V, f, and x; finite dimension is absent from the actual elaborated type.
2. **Scope.** Every feasible x under S_V(f).
3. **Hypotheses.** S_V(f) and x in V, including ambient properness and existence of a global support at x.
4. **Operation/run.** Convert f(x) with toReal and embed the resulting real back into the extended reals.
5. **Conclusion.** f(x) = embed((f(x)).toReal), so f(x) is an actual finite real value.
6. **Constants/indices.** Equality, no approximation constant or time index.
7. **Limits.** Does not establish finiteness at every ambient point or from properness alone. The stated equality is not a general axiom about toReal at infinities.

## P04

1. **Objects/structure.** Finite-dimensional E, V, arbitrary schedule eta:N->R, arbitrary extended-real loss sequence, a, and t in N.
2. **Scope.** All times t, with the same external feasible initial value a.
3. **Hypotheses.** Only a in V beyond domain/ambient structure. No positivity, monotonicity, loss properness, or support-existence condition.
4. **Operation/run.** The fixed iteration x_0=a and projected choice update, including its zero fallback if needed.
5. **Conclusion.** x_t in V for every t.
6. **Constants/indices.** Initial feasibility covers t=0; projection covers every successor. The argument named x1 denotes x_0.
7. **Limits.** Arbitrary negative or zero schedules and pathological losses are allowed for this membership statement. Membership alone implies neither legal support selection nor finite losses nor regret performance.

## P05

1. **Objects/structure.** Finite-dimensional E, common V and initial a, two schedules eta,eta', two loss sequences f,f', and t in N.
2. **Scope.** Strict-prefix equality: for EVERY s<t, eta_s=eta'_s and f_s=f'_s as whole functions E->extended reals. Same a is used on both sides. No feasibility hypothesis on a.
3. **Hypotheses.** Exactly those two prefix agreements; no support, positivity, finiteness, or monotonicity assumptions.
4. **Operation/run.** Compare x_t(V,eta,f,a) with x_t(V,eta',f',a), using the same defined choice function and recursion.
5. **Conclusion.** The two time-t iterates are equal.
6. **Constants/indices.** The equality uses only indices 0,...,t-1; no agreement at t or later is required. At t=0 the premises are vacuous and both values are a.
7. **Limits.** This is a deterministic strict-prefix invariance statement for externally fixed inputs. It does not imply equivalence from equal observed scalar losses or equal gradients only, does not constrain a future-dependent external initial value, does not ensure the schedule was selected without future information, and is not a filtration/measurability theorem. Whole-function equality is stronger than an oracle transcript agreement. It does not compare distinct legal selection policies.

## P06

1. **Objects/structure.** Finite-dimensional E, V, schedule eta, losses f, feasible a, and t.
2. **Scope.** At any specified time t in the actual run; only the current loss is assumed S_V.
3. **Hypotheses.** a in V and S_V(f_t). Earlier losses and every schedule value remain unrestricted.
4. **Operation/run.** g_t=c(f_t,x_t) at the recursively generated feasible iterate.
5. **Conclusion.** g_t in partial f_t(x_t).
6. **Constants/indices.** Current function index t and current iterate index t coincide; no numerical bound or horizon.
7. **Limits.** Legality at t does not certify prior selections, bounded norm, finite computation, or performance. The result concerns this fixed choice, not every legal policy.

## P07

1. **Objects/structure.** Finite-dimensional E, V, schedule, losses, a,t and comparator u.
2. **Scope.** Any time t and feasible u in the same actual run.
3. **Hypotheses.** a in V, S_V(f_t), u in V; no positive schedule condition or assumptions on other losses.
4. **Operation/run.** Evaluate the current extended-real loss both at x_t and u and apply toReal.
5. **Conclusion.** Both equalities hold:
   \[
   f_t(x_t)=\operatorname{embed}((f_t(x_t)).\mathrm{toReal}),\qquad
   f_t(u)=\operatorname{embed}((f_t(u)).\mathrm{toReal}).
   \]
6. **Constants/indices.** A conjunction for two values of the same loss f_t, not a comparison with f_{t+1} or another run.
7. **Limits.** This establishes actual finiteness needed for real differences at t; it is not unconditional validity of toReal arithmetic and does not certify every ambient evaluation.

## P08

1. **Objects/structure.** Finite-dimensional E, V, schedule, losses, feasible initial a, t, feasible comparator u.
2. **Scope.** A single current round of the specified choice/recursion, not a universally supplied one-step inequality for arbitrary sequences.
3. **Hypotheses.** a in V, eta_t>0, S_V(f_t), u in V. No requirements on other learning rates or other losses.
4. **Operation/run.** g_t=c(f_t,x_t), x_{t+1}=Pi_V(x_t-eta_t g_t).
5. **Conclusion.** The conjunction
   \[
   \eta_t(f_t(x_t)^{\rm r}-f_t(u)^{\rm r})\le\eta_t\langle g_t,x_t-u\rangle,
   \quad
   \eta_t\langle g_t,x_t-u\rangle\le\frac{\|x_t-u\|^2}{2}-\frac{\|x_{t+1}-u\|^2}{2}+\frac{\eta_t^2}{2}\|g_t\|^2.
   \]
6. **Constants/indices.** Current t and successor t+1, potentials divided by 2, squared eta_t norm penalty.
7. **Limits.** Does not allow eta_t=0 and does not assume a diameter or norm bound. The intermediate inner-product inequality is part of the conclusion, not a hidden hypothesis.

## P09

1. **Objects/structure.** Same run objects and finite-dimensional structure as P08.
2. **Scope.** Each chosen t and feasible u in the actual run.
3. **Hypotheses.** a in V, eta_t>0, S_V(f_t), u in V, without assumptions on other rounds.
4. **Operation/run.** Actual g_t and actual next iterate x_{t+1}.
5. **Conclusion.**
   \[
   f_t(x_t)^{\rm r}-f_t(u)^{\rm r}\le
   \frac{\|x_t-u\|^2-\|x_{t+1}-u\|^2}{2\eta_t}+\frac{\eta_t}{2}\|g_t\|^2.
   \]
6. **Constants/indices.** Denominator 2 eta_t multiplies the whole difference of squared distances; norm penalty eta_t/2, not eta_t squared/2.
7. **Limits.** A real loss difference justified by current-loss finiteness, not merely a totalized conversion. No horizon bound or zero-step extension is stated.

## P10

1. **Objects/structure.** Finite-dimensional E, V, fixed real eta, losses, initial a, natural horizon T, and comparator u.
2. **Scope.** Every finite natural T, including zero; one feasible comparator. All iterates, gradients and regret use the constant schedule eta.
3. **Hypotheses.** eta>0, a,u in V, and S_V(f_t) for every t<T. No boundedness of V and no uniform support-norm bound.
4. **Operation/run.** x_{t+1}=Pi_V(x_t-eta c(f_t,x_t)) for this same constant-step run.
5. **Conclusion.**
   \[
   R_T(u)\le\frac{\|a-u\|^2}{2\eta}+\frac{\eta}{2}\sum_{t=0}^{T-1}\|g_t\|^2-\frac{\|x_T-u\|^2}{2\eta}.
   \]
6. **Constants/indices.** Negative terminal residual is retained exactly. T losses at t=0,...,T-1 produce x_T; the last update uses f_{T-1}.
7. **Limits.** At T=0 the sum and regret vanish, x_T=a, and initial and terminal terms cancel. Eta=0 remains excluded. No supplied per-round performance premise replaces the algorithm assumptions.

## P11

1. **Objects/structure.** Same fixed-step objects as P10 in finite-dimensional E.
2. **Scope.** Every natural T including zero, for each feasible u, using the constant-step run.
3. **Hypotheses.** eta>0, a,u in V, S_V(f_t) for t<T; no diameter or gradient bound.
4. **Operation/run.** Same actual constant-step recursion and its same-run g_t.
5. **Conclusion.**
   \[
   R_T(u)\le\frac{\|a-u\|^2}{2\eta}+\frac{\eta}{2}\sum_{t=0}^{T-1}\|g_t\|^2.
   \]
6. **Constants/indices.** Coefficients 1/(2 eta) and eta/2. Unlike P10, no terminal residual is retained in the statement.
7. **Limits.** T=0 gives 0 <= ||a-u||^2/(2 eta). This is not a uniform O(sqrt(T)) claim without further hypotheses and a step-size choice.

## P12

1. **Objects/structure.** Finite-dimensional E, V, variable schedule eta, losses, a, positive natural T, real D, comparator u.
2. **Scope.** Conditions are restricted to the played prefix: eta_t>0 for t<T and eta_{t+1}<=eta_t whenever t+1<T. The diameter condition quantifies over every pair of feasible points.
3. **Hypotheses.** a,u in V, T>0, those positivity/monotonicity conditions, S_V(f_t) for t<T, and ||x-y||<=D for all x,y in V. There is no separately stated D>0 assumption. Nonemptiness and the diameter premise imply D>=0.
4. **Operation/run.** Actual variable-step recursion with its same-run selected supports.
5. **Conclusion.**
   \[
   R_T(u)\le\frac{D^2}{2\eta_{T-1}}+\sum_{t=0}^{T-1}\frac{\eta_t}{2}\|g_t\|^2-\frac{\|x_T-u\|^2}{2\eta_{T-1}}.
   \]
6. **Constants/indices.** Both diameter and negative terminal terms use the LAST PLAYED rate eta_{T-1}, not eta_T. The sum keeps each eta_t inside; it is not a single constant factor. Natural subtraction T-1 is unambiguous here because T>0.
7. **Limits.** T=0 is excluded. At T=1 monotonicity is vacuous. D=0 is permitted if the domain permits the diameter premise, e.g. a singleton; positivity of all played rates remains. No schedule restriction at or after T is imposed.

## P13

1. **Objects/structure.** Finite-dimensional E and a bounded domain V, variable schedule, losses, feasible a,u, and T>0.
2. **Scope.** Each comparator u in V and each positive horizon with prefix conditions; the diameter is the metric diameter of the whole carrier.
3. **Hypotheses.** Bornological boundedness of V, a,u in V, T>0, eta_t>0 for t<T, eta_{t+1}<=eta_t when t+1<T, and S_V(f_t) for t<T.
4. **Operation/run.** Actual variable-step recursion and its selected g_t.
5. **Conclusion.**
   \[
   R_T(u)\le\frac{(\operatorname{diam}V)^2}{2\eta_{T-1}}+\sum_{t=0}^{T-1}\frac{\eta_t}{2}\|g_t\|^2-\frac{\|x_T-u\|^2}{2\eta_{T-1}}.
   \]
6. **Constants/indices.** Same last-played denominator and negative terminal residual as P12; uses actual Metric.diam, not a freely chosen upper-bound D.
7. **Limits.** No positive diameter is required; singleton diameter zero is allowed. Boundedness cannot be dropped merely because the formal diameter is a real-valued expression. T=0 is outside scope, and T=1 has no adjacent-rate comparisons.

## P14

1. **Objects/structure.** Finite-dimensional E, V, losses, feasible a, positive natural T, strictly positive real D,G, and a feasible comparator u.
2. **Scope.** A comparator-specific initial-distance condition. D need not bound the whole domain diameter. The support bound is for every played time of exactly the tuned run below, not all points or all supports.
3. **Hypotheses.** a,u in V, T>0, D>0, G>0, S_V(f_t) for t<T, ||a-u||<=D, and ||c(f_t,x_t)||<=G for t<T where x_t is computed using eta_star=D/(G sqrt(T)).
4. **Operation/run.** Constant learning rate eta_star with horizon T, D, G used in constructing this very trajectory. Gradient bound and regret refer to that same trajectory.
5. **Conclusion.**
   \[
   R_T(u;\eta_\star)\le DG\sqrt T,\qquad \eta_\star=\frac{D}{G\sqrt T}.
   \]
6. **Constants/indices.** Leading constant exactly 1. T is coerced to real in sqrt(T). Sum/regret uses t=0,...,T-1; no terminal residual appears in the bound.
7. **Limits.** T=0, D=0, and G=0 are excluded by strict assumptions; these cases must not be claimed by division conventions or limits. A run with actual zero gradients is still allowed if a positive G upper bound is supplied. D may be a positive distance upper bound even when ||a-u||=0. No global Lipschitz premise, arbitrary-policy norm bound, or bound transferred from a different run is asserted. The tuning uses a fixed horizon and supplies no anytime guarantee.

## P15

1. **Objects/structure.** Finite-dimensional E, V, losses, feasible initial a, positive T and strictly positive D,G.
2. **Scope.** After fixing V, losses, a,T,D,G and the common same-run assumptions, the conclusion is for EVERY u in V. One run and one D,G work for all those comparators.
3. **Hypotheses.** a in V, T>0, D>0, G>0, ||x-y||<=D for every x,y in V, S_V(f_t) for t<T, and ||c(f_t,x_t)||<=G for every t<T on the tuned run with eta_star=D/(G sqrt(T)).
4. **Operation/run.** The same constant tuned schedule and fixed choice recursion for all comparators; u is not an input to the iteration.
5. **Conclusion.**
   \[
   \forall u\in V,\quad R_T(u;\eta_\star)\le DG\sqrt T.
   \]
6. **Constants/indices.** Exact constant 1 and positive-horizon square root as P14, with t<T for the support bound. D is a uniform diameter upper bound, not necessarily the exact metric diameter.
7. **Limits.** Positive D,G,T remain required even if actual diameter or support norms are zero. Unlike P14, the distance assumption is replaced by an all-pairs diameter premise that supports a comparator-uniform conclusion for the same run. No minimizer existence, infimum attainment, executable oracle, all-policy guarantee, or probability/anytime claim is added.

## Evidence boundary

The packet contains fully elaborated proposition definitions and borrowed structural types, with unused-hypothesis warnings characteristic of proposition definitions. Elaboration of a proposition description is not construction of a proof of that proposition. The report therefore records only what P01-P15 say. Whether they are proved, imported into a public root, pass a combined project gate, or faithfully represent any external source is outside the inspected evidence and is not certified here.
