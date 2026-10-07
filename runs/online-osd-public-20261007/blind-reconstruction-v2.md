# Source-blind semantic reconstruction v2

Actor: `/root/osd_blind`. Requested settings: GPT-6 Astra / medium. Runtime model attestation: false. The only file read for this fresh reconstruction was `blind-packet-v2.md`. No source text, actual-name map, other review, prior verdict, repository/history, or target proof body was inspected. Prior v1 files are preserved. This is a reconstruction of proposition descriptions, not a proof or source-acceptance decision.

## Definitions, binders, and information order

Every one of P01-P15 has the compiled scoped binders `{E : Type*}`, `[NormedAddCommGroup E]`, `[InnerProductSpace R E]`, and `[instFD : FiniteDimensional R E]`. Thus this report retains a finite-dimensional real inner-product space for every proposition, including P02 and P03 even though their finite-dimensional binder receives an unused-variable warning. Such a warning does not remove that binder from the printed type.

Let V denote the carrier of the supplied domain. It is nonempty, closed, and convex. Write Pi_V for its actual nearest-point projection: Pi_V(z) belongs to V and its distance to z equals the infimum of distances from z to members of V. The packet also supplies the comparison ||Pi_V(z)-u|| <= ||z-u|| for u in V. These projection specifications are mathematical context, not an assumed loss-regret inequality.

For f:E->extended reals, properness means
\[
(\forall x\in E,\ f(x)\ne-\infty)\quad\land\quad(\exists a\in E,\exists r\in\mathbb R,\ f(a)=r).
\]
The finite witness need not be in V. Define the global support set by
\[
\partial f(x)=\{g\in E:\ \forall y\in E,\ f(x)+\operatorname{embed}(\langle g,y-x\rangle)\le f(y)\}.
\]
Every ambient y is tested. This is not a support condition restricted to feasible points, an interior, or the effective domain. Let S_V(f) mean properness together with nonemptiness of partial f(x) at every x in V. No separate global convexity assumption on f is added to this definition. The supplied effective domain is {x:f(x)<+infinity}; properness rules out minus infinity, but properness alone does not imply finiteness everywhere. A proper function with a global support at x must be finite at x: the ambient finite witness excludes a supported +infinity value. This explains the semantic role of the finite-value claims below, without certifying any target proof.

The fixed mathematical selector c(f,x) chooses by classical choice from partial f(x) if nonempty, and otherwise equals zero. It takes the current whole function f and point x only; it is neither a free policy parameter nor an executable oracle. Zero fallback gives no support-membership guarantee when the set is empty.

Rename the externally supplied argument `x1` to a, and preserve the code's zero-based indices:
\[
x_0=a,\quad g_t=c(f_t,x_t),\quad x_{t+1}=\Pi_V(x_t-\eta_t g_t),\quad
R_T(u)=\sum_{t=0}^{T-1}\bigl(f_t(x_t)^{\rm r}-f_t(u)^{\rm r}\bigr),
\]
where z^r means z.toReal. This conversion is defined for all extended-real inputs, but interpreting its subtraction as a real loss difference requires actual finiteness. All sums below are over the integer range 0,...,T-1; all quantities within one conclusion belong to the same specified run.

The definition's information order is: fix V, external schedule eta, external initial a, and loss sequence; recursively obtain x_t from the strict prefix; evaluate/select from the current function f_t at x_t; use eta_t and that selector to produce x_{t+1}. No f_t is used by the recursion to compute x_t, while f_t is used to compute g_t and x_{t+1}. The definitions do not restrict how external a or eta were chosen; in particular they do not rule out dependence of those external inputs on future losses. No probability, filtration, measurability, feedback implementation, or anytime policy is specified.

Each proposition below has seven slots: objects/binders; quantifier/information scope; hypotheses; algorithm or operation; conclusion; constants/indices; degeneracies/limits. These slot labels organize the decoding and are not additional mathematical assumptions.

## P01

1. **Objects/binders:** Finite-dimensional real inner-product E with all four common binders; domain V; f; real eta; ambient x,u,g.
2. **Scope:** In compiled order: V,f; S_V(f); eta and positivity; x,u and feasibility of u; g and its support membership. The query x is arbitrary in E, with no feasibility premise. The support g is arbitrary subject to actual membership, not restricted to c(f,x).
3. **Hypotheses:** S_V(f), eta>0, u in V, g in partial f(x). These support/properness hypotheses make the queried f(x) and comparator f(u) finite even though x need not be feasible.
4. **Operation:** Form x_plus=Pi_V(x-eta g), an actual projected step.
5. **Conclusion:** Both inequalities hold:
   \[
   \eta(f(x)^{\rm r}-f(u)^{\rm r})\le\eta\langle g,x-u\rangle,
   \qquad \eta\langle g,x-u\rangle\le\frac{\|x-u\|^2}{2}-\frac{\|x_+-u\|^2}{2}+\frac{\eta^2}{2}\|g\|^2.
   \]
6. **Constants/indices:** Half squared distances, negative next-distance residual, and eta squared/2 on the support norm. No time or horizon index.
7. **Degeneracies/limits:** Eta=0 is excluded. No diameter, support-norm bound, interior-query hypothesis, or supplied one-step performance premise is imposed. Ambient support cannot be replaced by feasible-only support in the reconstructed statement.

## P02

1. **Objects/binders:** All common binders, explicitly including finite dimension; V,f,x.
2. **Scope:** For every V,f satisfying S_V(f), and then every x in V.
3. **Hypotheses:** S_V(f) and feasible x.
4. **Operation:** The fixed selector c(f,x) based on the current function and point.
5. **Conclusion:** c(f,x) belongs to partial f(x).
6. **Constants/indices:** No numerical bound, schedule, or time index.
7. **Degeneracies/limits:** Does not certify an empty-set fallback, infeasible query, executable implementation, or arbitrary legal policy. The explicit finite-dimensional parameter is retained despite its warning.

## P03

1. **Objects/binders:** All common binders including finite dimension; V,f,x.
2. **Scope:** For all V,f with S_V(f), every feasible x.
3. **Hypotheses:** S_V(f) and x in V.
4. **Operation:** Convert f(x) to a real and embed that real back into the extended reals.
5. **Conclusion:** f(x)=embed(f(x)^r), i.e. actual finiteness at the feasible query.
6. **Constants/indices:** Exact equality, not approximation; no time index.
7. **Degeneracies/limits:** No everywhere-finite claim and no identification of infinity with its toReal image. Properness alone is insufficient. The scoped finite-dimensional parameter is not dropped.

## P04

1. **Objects/binders:** All common binders; V, schedule eta:N->R, loss sequence, initial a, and natural t.
2. **Scope:** Universal over arbitrary schedules/losses and every t after choosing feasible a.
3. **Hypotheses:** a in V; no positive step-size or loss regularity premises.
4. **Operation:** The specified recursion with projection and the total selector including its fallback.
5. **Conclusion:** x_t in V.
6. **Constants/indices:** x_0=a, and the conclusion covers t=0 and all successors.
7. **Degeneracies/limits:** Zero/negative rates and losses lacking supports are permitted for this membership assertion. It does not certify support legality, finite loss, or any performance inequality.

## P05

1. **Objects/binders:** All common binders; same V,a; two schedules eta,eta'; two loss sequences f,f'; natural t.
2. **Scope:** The compiled universal order is V,eta,eta',f,f',a,t, followed by the two strict-prefix premises. Initial a is shared and need not be feasible.
3. **Hypotheses:** For every s<t, eta_s=eta'_s; for every s<t, f_s=f'_s as whole functions on E. No condition at t or later.
4. **Operation:** Compare the two time-t iterates using the same defined selector, domain, and initial value.
5. **Conclusion:** x_t(V,eta,f,a)=x_t(V,eta',f',a).
6. **Constants/indices:** Strict prefix includes 0,...,t-1, not t. At t=0 both premises are vacuous and both sides equal a.
7. **Degeneracies/limits:** Equal scalar observations or equal values only at played points are not the stated hypothesis. This is deterministic prefix invariance conditional on external inputs, not a ban on future-dependent a or schedule selection, not a measurable/adapted policy result, and not equality between independently chosen support policies.

## P06

1. **Objects/binders:** All common binders; V, schedule, losses, feasible a, natural t.
2. **Scope:** After those choices, assume only S_V(f_t) for the current round.
3. **Hypotheses:** a in V and S_V(f_t). No support or positivity hypotheses for earlier rounds.
4. **Operation:** At the recursively produced x_t, compute g_t=c(f_t,x_t).
5. **Conclusion:** g_t belongs to partial f_t(x_t).
6. **Constants/indices:** Loss index and query index are both t; no horizon or norm constant.
7. **Degeneracies/limits:** Current legality does not assert past legality or a norm bound. The selector uses f_t after x_t has been determined by its recursive prefix.

## P07

1. **Objects/binders:** All common binders; V, schedule, losses, feasible a, natural t, comparator u.
2. **Scope:** After S_V(f_t), every u in V, for the current time of this run.
3. **Hypotheses:** a in V, S_V(f_t), u in V; no positivity or other-round regularity assumption.
4. **Operation:** Evaluate f_t at x_t and u, convert each toReal, and embed back.
5. **Conclusion:** The conjunction
   \[
   f_t(x_t)=\operatorname{embed}(f_t(x_t)^{\rm r}),\qquad f_t(u)=\operatorname{embed}(f_t(u)^{\rm r}).
   \]
6. **Constants/indices:** Two exact equalities for the same current loss, not losses at different times.
7. **Degeneracies/limits:** Supplies actual finite-value meaning at these two points; does not make toReal arithmetic faithful at infinity or prove finiteness of every ambient value.

## P08

1. **Objects/binders:** All common binders; V, schedule, losses, feasible a, natural t and comparator u.
2. **Scope:** Fix the run and t, assume current positivity and regularity, then quantify over feasible u.
3. **Hypotheses:** a in V, eta_t>0, S_V(f_t), u in V. Other rates and losses are unrestricted.
4. **Operation:** g_t=c(f_t,x_t) and actual successor x_{t+1}=Pi_V(x_t-eta_t g_t).
5. **Conclusion:** Both links hold:
   \[
   \eta_t(f_t(x_t)^{\rm r}-f_t(u)^{\rm r})\le\eta_t\langle g_t,x_t-u\rangle
   \le\frac{\|x_t-u\|^2}{2}-\frac{\|x_{t+1}-u\|^2}{2}+\frac{\eta_t^2}{2}\|g_t\|^2.
   \]
6. **Constants/indices:** t versus t+1; half potentials; squared current rate/2 norm term.
7. **Degeneracies/limits:** Excludes zero current rate. No diameter or uniform norm premise. The performance chain is the conclusion, not an assumption about an arbitrary update sequence.

## P09

1. **Objects/binders:** All common binders; V, schedule, losses, feasible a, t,u.
2. **Scope:** Current time t of the specified run, for every feasible u after current positivity and regularity.
3. **Hypotheses:** a,u in V, eta_t>0, S_V(f_t), with no other-round assumptions.
4. **Operation:** Actual x_t,g_t,x_{t+1} from the defined update.
5. **Conclusion:**
   \[
   f_t(x_t)^{\rm r}-f_t(u)^{\rm r}\le\frac{\|x_t-u\|^2-\|x_{t+1}-u\|^2}{2\eta_t}+\frac{\eta_t}{2}\|g_t\|^2.
   \]
6. **Constants/indices:** The entire squared-distance difference is divided by 2 eta_t; norm term is eta_t/2, without a squared rate.
7. **Degeneracies/limits:** Zero step is excluded; finiteness comes from the assumptions, not unconditional toReal arithmetic. No cumulative bound or all-policy claim is inserted.

## P10

1. **Objects/binders:** All common binders; V, positive scalar eta, losses, feasible a, natural horizon T, comparator u.
2. **Scope:** In order: V,eta, positivity, losses,a, feasibility,T, regularity of every t<T, then feasible u. T may be zero.
3. **Hypotheses:** eta>0, a,u in V, S_V(f_t) for all t<T. No bounded domain or uniform support bound.
4. **Operation:** Constant schedule eta at every index; regret and all g_t are from that same constant-step run.
5. **Conclusion:**
   \[
   R_T(u)\le\frac{\|a-u\|^2}{2\eta}+\frac{\eta}{2}\sum_{t=0}^{T-1}\|g_t\|^2-\frac{\|x_T-u\|^2}{2\eta}.
   \]
6. **Constants/indices:** Negative terminal residual retained; T played losses end at T-1 and the terminal iterate is x_T.
7. **Degeneracies/limits:** At T=0, regret and sum are zero and the initial/terminal terms cancel. Eta=0 remains excluded. No supplied per-step performance premise replaces the concrete run.

## P11

1. **Objects/binders:** All common binders; V, positive fixed eta, losses, feasible a, natural T,u.
2. **Scope:** Same compiled ordering and finite-prefix scope as P10, including T=0.
3. **Hypotheses:** eta>0, a,u in V and S_V(f_t) for every t<T; no norm or diameter bound.
4. **Operation:** One constant-step choice/recursion, with same-run selected supports.
5. **Conclusion:**
   \[
   R_T(u)\le\frac{\|a-u\|^2}{2\eta}+\frac{\eta}{2}\sum_{t=0}^{T-1}\|g_t\|^2.
   \]
6. **Constants/indices:** Initial coefficient 1/(2 eta), support coefficient eta/2; terminal residual omitted in this statement.
7. **Degeneracies/limits:** At zero horizon this states 0<=||a-u||^2/(2 eta). It is not already a uniform square-root rate without additional bounds and tuning.

## P12

1. **Objects/binders:** All common binders; V, variable eta, losses, feasible a, positive natural T, real D and comparator u.
2. **Scope:** First run inputs and positive horizon, then played-prefix positivity/monotonicity/regularity, then D with an all-pairs diameter premise, then feasible u.
3. **Hypotheses:** a,u in V; T>0; eta_t>0 for every t<T; eta_{t+1}<=eta_t whenever t+1<T; S_V(f_t) for t<T; ||x-y||<=D for every x,y in V. No explicit D>0 premise; nonemptiness implies D>=0 from the diameter premise.
4. **Operation:** The variable-step recursion, with the actual same-run g_t in each summand.
5. **Conclusion:**
   \[
   R_T(u)\le\frac{D^2}{2\eta_{T-1}}+\sum_{t=0}^{T-1}\frac{\eta_t}{2}\|g_t\|^2-\frac{\|x_T-u\|^2}{2\eta_{T-1}}.
   \]
6. **Constants/indices:** Both outside denominators use the last played eta_{T-1}, not eta_T; each summand uses its own eta_t. The terminal term is negative. Natural T-1 is used only with T>0.
7. **Degeneracies/limits:** T=0 excluded; at T=1 monotonicity has no instances. D=0 is allowed when the diameter premise holds. Rates from index T onward are unrestricted; no norm bound is assumed.

## P13

1. **Objects/binders:** All common binders; bounded domain V, variable schedule, losses, feasible a, positive T,u.
2. **Scope:** V and its bornological boundedness come before run inputs; prefix conditions precede the final feasible comparator.
3. **Hypotheses:** IsBounded(V), a,u in V, T>0, eta_t>0 for t<T, eta_{t+1}<=eta_t if t+1<T, and S_V(f_t) for t<T.
4. **Operation:** Actual variable-step recursion and its selected supports; use d=Metric.diam(V).
5. **Conclusion:**
   \[
   R_T(u)\le\frac{d^2}{2\eta_{T-1}}+\sum_{t=0}^{T-1}\frac{\eta_t}{2}\|g_t\|^2-\frac{\|x_T-u\|^2}{2\eta_{T-1}}.
   \]
6. **Constants/indices:** Exact metric diameter squared and last-played denominator; negative terminal residual is retained.
7. **Degeneracies/limits:** Diameter need not be positive; singleton diameter zero is permitted. Boundedness is an explicit hypothesis and must not be dropped because Metric.diam is real-valued. T=0 is excluded; T=1 has vacuous monotonicity.

## P14

1. **Objects/binders:** All common binders; V,losses,feasible a,positive T,positive real D,G, comparator u.
2. **Scope:** After T,D,G positivity and prefix regularity, choose feasible u with ||a-u||<=D, then assume the same-run support bound. This is an initial-distance condition for that comparator, not a domain diameter condition.
3. **Hypotheses:** a,u in V; T>0,D>0,G>0; S_V(f_t) for all t<T; ||a-u||<=D; ||c(f_t,x_t)||<=G for every t<T on the run with constant eta_star=D/(G sqrt(T)).
4. **Operation:** Construct and evaluate that exact tuned run. The norm hypothesis is not imported from an untuned or differently tuned trajectory, nor is it about every support at every point.
5. **Conclusion:**
   \[
   R_T(u;\eta_\star)\le DG\sqrt T,\qquad\eta_\star=\frac{D}{G\sqrt T}.
   \]
6. **Constants/indices:** Leading constant exactly 1; T is coerced to a real before square root; support bound covers all played indices t<T; no terminal residual appears.
7. **Degeneracies/limits:** T=0,D=0,G=0 are excluded, even if totalized division exists. Actual distance or support norms may be zero while positive D,G upper bounds are supplied. No global Lipschitz premise, global diameter bound, universal legal-policy claim, or anytime guarantee is asserted; tuning explicitly depends on T.

## P15

1. **Objects/binders:** All common binders; V,losses,feasible a,positive T,positive D,G.
2. **Scope:** After fixing those objects, impose the all-pairs diameter bound, played-prefix regularity, and same-run norm bound; only then quantify over every comparator u in V. One run and common constants serve all comparators.
3. **Hypotheses:** a in V; T>0,D>0,G>0; ||x-y||<=D for all x,y in V; S_V(f_t) for every t<T; ||c(f_t,x_t)||<=G at all t<T on the constant eta_star=D/(G sqrt(T)) run.
4. **Operation:** The tuned recursion independent of comparator u; all quantities refer to that run.
5. **Conclusion:**
   \[
   \forall u\in V,\qquad R_T(u;\eta_\star)\le DG\sqrt T.
   \]
6. **Constants/indices:** Same exact constant 1 and played indices as P14. D is a common diameter upper bound, not necessarily Metric.diam(V).
7. **Degeneracies/limits:** Strict positivity remains even when actual diameter or norms vanish. The comparator-uniform claim does not assert existence of a best comparator, attainment of an infimum, computation of an oracle, every legal support policy, or an anytime/stochastic guarantee.

## Certification boundary

The standalone elaboration demonstrates the displayed proposition descriptions and their retained binders. It does not exhibit proofs of P01-P15. This reconstruction neither validates target proof bodies nor accepts external-source fidelity, integrated library gates, chapter completion, or Goal completion.
