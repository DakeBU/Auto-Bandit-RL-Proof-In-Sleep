# Source-blind reconstruction: policy v1

Only this run's blind-packet-v1.md was read. The 21 headers are treated as proposed propositions/contracts, not compiled or proved theorems. This is a distinct automated decoding, not source review, independent human review, or package acceptance.

## Visible definitions, notation, and interpretation gaps

The ambient E is an arbitrary finite-dimensional real inner-product space with normed additive group structure. Write C=V.carrier, f_t=loss(t), P_V=the imported project, S_V(f)=the imported SubdifferentiableOn V f, and partial f(x)=the imported SourceSubdifferential f x. These imported definitions are NOT expanded in this packet. Their exact mathematical properties cannot be recovered by inspecting the import name. In particular, the packet does not supply Domain fields, project specification, SourceProper or SourceSubdifferential definitions, SubdifferentiableOn expansion, or definitions of imported currentSubgradient and iterate. It also does not expand Metric.diam, Bornology.IsBounded, or EReal.toReal endpoint behavior. I preserve those symbols explicitly rather than substitute unverified definitions. The words support, projection, properness, and boundedness below describe their roles, not a verification of their imported implementation. If partial denotes global supporting inequalities as intended by the request, membership means a true ambient global support; that definition is absent from the packet itself.

The visible policy type is exactly
\[
p:\prod_{t\in\mathbb N}
 (\operatorname{Fin}(t)\to(E\to\mathrm{EReal}))
 \to(\operatorname{Fin}(t+1)\to E)
 \to(E\to\mathrm{EReal})\to E.
\]
At time t its inputs are t, the t past entire loss functions, a finite vector of t+1 outputs through the current output, and the current entire loss. There is no explicit future-loss, comparator, horizon, or schedule argument. A fixed policy can nevertheless be chosen externally using other data; the contracts do not constrain such external selection. Policies are mathematical functions, not an asserted executable restricted-value oracle.

For fixed V, schedule a, loss f, initial x1, and p, write H_t=history(...,t), X_t=output(...,t), g_t=selected(...,t). The visible recursion is
\[
H_0=(x_1),\quad X_t=H_t(t),\quad
 g_t=p(t,(f_0,\ldots,f_{t-1}),H_t,f_t),\quad
H_{t+1}=\operatorname{snoc}(H_t,P_V(X_t-a_tg_t)).
\]
Here Fin.snoc preserves the earlier entries and appends one entry; Fin.last t is the last index t. Thus x1 is the index-0 initial point, H_t has t+1 entries, and the actual next output is P_V(X_t-a_tg_t). Only past losses determine H_t; the current f_t is an input when choosing g_t for the next update.

OracleLaw(V,p) universally quantifies over every t, arbitrary past loss vector, arbitrary output vector h, and current f. It requires p(t,past,h,f) in partial f(h_t) whenever S_V(f) and h_t in C. It does not require past/h to be realized by the recursion, or all earlier h entries to be feasible. LegalFeedback(V,a,f,x1,p,T), in contrast, requires only g_t in partial f_t(X_t) at the actual played points for every t<T. It is specific to this schedule and run. It imposes no universal off-path condition and does not itself assert S_V(f_t).

Write q^R(x)=toReal(q(x)) and
\[
R_T(u)=\sum_{t=0}^{T-1}[f_t^R(X_t)-f_t^R(u)].
\]
All numerical formulas below use this exact run unless explicitly comparing two runs. The regret definition itself has no finite-value premises. The finite-value equalities in result_10 are explicit conclusions; interpreting them as actual real witnesses uses the usual finite real embedding. Other headers contain assumptions intended to enable such consequences, not explicit finite-value witnesses. Their derivability cannot be verified without the omitted imported definitions and proofs.

## result_1
1. **Objects:** V,a,f,x1,p and H_0.
2. **Quantifiers:** Every such data, with no restriction on the policy.
3. **Hypotheses:** None beyond shared type structure.
4. **Conclusion:** H_0 is the function on Fin(1) constantly equal to x1.
5. **Order:** Initialization uses no observations or selected vector.
6. **Boundary:** Initial feasibility is not assumed.
7. **Scope:** Exact history initialization contract, not a performance bound.

## result_2
1. **Objects:** V,a,f,x1,p and any natural t.
2. **Quantifiers:** Every run and every t.
3. **Hypotheses:** No feasibility, support, or step-sign conditions.
4. **Conclusion:** H_{t+1}=snoc(H_t,P_V(X_t-a_t g_t)).
5. **Order:** Preserve the t+1 current entries and append the next output after the current selection.
6. **Boundary:** Real steps may be zero or negative; p may supply unsupported vectors.
7. **Scope:** Exact finite-history recursion, leaving imported projection semantics unverified.

## result_3
1. **Objects:** Any run and X_0.
2. **Quantifiers:** All V,a,f,x1,p.
3. **Hypotheses:** None.
4. **Conclusion:** X_0=x1.
5. **Order:** The parameter spelling x1 does not shift indexing to one.
6. **Boundary:** No initial feasibility required for this identity.
7. **Scope:** Initial output equality only.

## result_4
1. **Objects:** Any run, g_t, X_t, X_{t+1}.
2. **Quantifiers:** Every natural t for every run.
3. **Hypotheses:** None beyond shared structure.
4. **Conclusion:** X_{t+1}=P_V(X_t-a_tg_t).
5. **Order:** Current feedback is used to form the next output, not retroactively the current output.
6. **Boundary:** No positivity or actual support membership assumed.
7. **Scope:** The actual algorithmic step equality, not a chosen surrogate next point.

## result_5
1. **Objects:** H_t and arbitrary i in Fin(t+1).
2. **Quantifiers:** Every run, every t, every valid history index i.
3. **Hypotheses:** x1 in C only.
4. **Conclusion:** H_t(i) in C.
5. **Order:** Feasibility covers the entire stored output vector through time t.
6. **Boundary:** No OracleLaw, LegalFeedback, positive steps, or loss regularity is assumed.
7. **Scope:** Feasibility contract for arbitrary policies; its justification would depend on the unseen projection properties.

## result_6
1. **Objects:** Any run and output X_t.
2. **Quantifiers:** Every natural t.
3. **Hypotheses:** x1 in C.
4. **Conclusion:** X_t in C.
5. **Order:** Includes the initial output at t=0.
6. **Boundary:** Arbitrary policy and real schedule are allowed without legal feedback.
7. **Scope:** Output feasibility alone does not assert support validity or finite losses.

## result_7
1. **Objects:** Two schedules a,a', two loss sequences f,f', common V,x1,p, time t.
2. **Quantifiers:** Every such pair of runs and t with the SAME policy.
3. **Hypotheses:** a_s=a'_s and f_s=f'_s for every s<t. Loss equality is whole-function equality.
4. **Conclusion:** H_t=H'_t as complete finite-history functions.
5. **Order:** Entire histories depend only on strict input prefixes; current inputs at t need not agree.
6. **Boundary:** At t=0 prefix conditions are vacuous. No feasibility or legality assumptions occur.
7. **Scope:** Does not compare different policies or initial points, or prohibit future information encoded in external policy selection.

## result_8
1. **Objects:** The same two-run data as result_7.
2. **Quantifiers:** Every common-policy pair of runs and t.
3. **Hypotheses:** Matching schedules and loss functions only for s<t.
4. **Conclusion:** X_t=X'_t.
5. **Order:** Current loss can differ while the current output agrees; selected g_t need not agree in that case.
6. **Boundary:** t=0 is unconditional equality to the common x1.
7. **Scope:** Output prefix-invariance contract, not equality under arbitrary different policies or merely equal observed scalar values.

## result_9
1. **Objects:** Any run, policy p, and natural T.
2. **Quantifiers:** Every such data satisfying the following premises.
3. **Hypotheses:** x1 in C, OracleLaw(V,p), and S_V(f_t) for every t<T.
4. **Conclusion:** LegalFeedback for this actual schedule/run/horizon: all actual g_t belong to partial f_t(X_t) for t<T.
5. **Order:** Universal off-path oracle validity is a sufficient route to actual played legality.
6. **Boundary:** T=0 gives vacuous legality. Step positivity is absent.
7. **Scope:** No reverse implication is stated. Later performance contracts directly assume played legality and do not require this stronger OracleLaw.

## result_10
1. **Objects:** Any run, time t, and comparator u.
2. **Quantifiers:** Every run, t and feasible u under the next premises.
3. **Hypotheses:** x1 in C, S_V(f_t), u in C. No support validity of p is assumed.
4. **Conclusion:** f_t(X_t)=coe(f_t^R(X_t)) AND f_t(u)=coe(f_t^R(u)).
5. **Order:** Both values refer to the same current loss, before the current update.
6. **Boundary:** Arbitrary earlier losses and arbitrary real steps remain allowed; t=0 is included.
7. **Scope:** Explicit finite-value representation contract. It is independent of OracleLaw/LegalFeedback in its visible premises, but depends on unseen S_V semantics for justification.

## result_11
1. **Objects:** Any run at t, actual selected g_t, and feasible u.
2. **Quantifiers:** Every V,a,f,x1,p,t,u satisfying the premises.
3. **Hypotheses:** a_t>0, S_V(f_t), g_t in partial f_t(X_t), u in C. Crucially no x1 in C premise is present.
4. **Conclusion:**
   \[
   a_t(f_t^R(X_t)-f_t^R(u))\le a_t\langle g_t,X_t-u\rangle
   \le\|X_t-u\|^2/2-\|X_{t+1}-u\|^2/2+a_t^2\|g_t\|^2/2.
   \]
   The Lean conclusion is the conjunction of these two inequalities.
5. **Order:** Uses actual selected feedback and actual next output from the recursion.
6. **Boundary:** At t=0 an infeasible initial query is allowed if its supplied support membership holds. Finite-query reasoning from properness plus actual support would require the unseen imported definitions. Eta zero/negative is excluded at this round.
7. **Scope:** Single-step chain under played support membership, not universal policy legality or a cumulative estimate.

## result_12
1. **Objects:** The same actual run and comparator data as result_11.
2. **Quantifiers:** All such data under the identical visible hypotheses.
3. **Hypotheses:** a_t>0, S_V(f_t), g_t in partial f_t(X_t), u in C; no initial-feasibility requirement.
4. **Conclusion:**
   \[
   f_t^R(X_t)-f_t^R(u)\le
   (\|X_t-u\|^2-\|X_{t+1}-u\|^2)/(2a_t)+a_t\|g_t\|^2/2.
   \]
5. **Order:** Actual next output follows the selected current support.
6. **Boundary:** Denominator is strictly positive. Current legality is needed explicitly even for a policy not satisfying OracleLaw.
7. **Scope:** One-step scalar bound, not finite-horizon performance by itself.

## result_13
1. **Objects:** Constant schedule a_t=eta, policy p, its run, natural T and feasible u.
2. **Quantifiers:** Every such constant-step run and comparator.
3. **Hypotheses:** eta>0, x1 in C, S_V(f_t) for t<T, LegalFeedback on EXACTLY this constant schedule through T, u in C.
4. **Conclusion:** R_T(u)<=norm(x1-u)^2/(2 eta)+(eta/2) sum_{t<T} norm(g_t)^2-norm(X_T-u)^2/(2 eta).
5. **Order:** The negative residual is retained at terminal T; gradients are selected at t<T on the same run.
6. **Boundary:** T=0 is allowed and initial/terminal terms cancel. No norm or diameter bound is required.
7. **Scope:** Fixed-step cumulative contract under actual legality; no universal OracleLaw premise.

## result_14
1. **Objects:** Constant-step run, policy, natural T and comparator.
2. **Quantifiers:** Every such run and feasible comparator under its premises.
3. **Hypotheses:** Exactly eta>0, feasible initial/comparator, prefix S_V, and LegalFeedback for that constant-step run.
4. **Conclusion:** R_T(u)<=norm(x1-u)^2/(2 eta)+(eta/2) sum_{t<T} norm(g_t)^2.
5. **Order:** Same actual support sum; no terminal residual in this contract.
6. **Boundary:** T=0 gives zero bounded by the nonnegative initial-distance expression under ordinary norm semantics.
7. **Scope:** Coarse cumulative bound, not an optimized rate.

## result_15
1. **Objects:** Variable schedule a, actual policy run, T, real D and comparator u.
2. **Quantifiers:** Every such run, D and u meeting all conditions.
3. **Hypotheses:** x1,u in C; T>0; a_t>0 for t<T; a_{t+1}<=a_t if t+1<T; prefix S_V; played LegalFeedback for this variable run; norm(x-y)<=D for all x,y in C.
4. **Conclusion:**
   \[
   R_T(u)\le D^2/(2a_{T-1})+\sum_{t<T}(a_t/2)\|g_t\|^2
      -\|X_T-u\|^2/(2a_{T-1}).
   \]
5. **Order:** Last used step is a_{T-1}; terminal state is X_T. Each support norm has its own a_t weight.
6. **Boundary:** T=0 excluded; T=1 monotonicity vacuous. D is not explicitly positive; feasible x1 ensures D>=0 from the pairwise premise. No future schedule restriction.
7. **Scope:** Nonincreasing-positive-prefix performance with a pairwise distance upper bound, not necessarily exact diameter.

## result_16
1. **Objects:** Variable actual policy run, T, feasible u, Metric.diam(C).
2. **Quantifiers:** All such data satisfying the premises.
3. **Hypotheses:** Feasible x1,u; T>0; positive nonincreasing used-step prefix; prefix S_V; actual LegalFeedback; Bornology.IsBounded(C).
4. **Conclusion:** R_T(u)<=Metric.diam(C)^2/(2a_{T-1})+sum_{t<T}(a_t/2)norm(g_t)^2-norm(X_T-u)^2/(2a_{T-1}).
5. **Order:** Both endpoint terms use a_{T-1}, not a_T; terminal output is X_T.
6. **Boundary:** Boundedness is explicitly required and must not be removed. Exact diameter/infinite-value conventions are not supplied in this packet.
7. **Scope:** Diameter-form contract with imported metric semantics still opaque; no imported definition is inferred from other runs.

## result_17
1. **Objects:** Policy p, horizon T, real D,G, comparator u, and constant schedule a_t=D/(G sqrt(T)).
2. **Quantifiers:** Every such data and particular feasible comparator satisfying the distance premise.
3. **Hypotheses:** Feasible x1,u; T,D,G>0; prefix S_V; LegalFeedback on THIS tuned run; norm(x1-u)<=D; norm(g_t)<=G for all t<T on THIS tuned run.
4. **Conclusion:** R_T(u)<=D G sqrt(T).
5. **Order:** All feedback legality and norm premises use the same policy/schedule/trajectory as the regret. Horizon-dependent constant tuning may change the whole run when T changes.
6. **Boundary:** Zero T,D,G excluded; denominator G sqrt(T) is positive. No pairwise diameter premise is required.
7. **Scope:** Comparator-distance tuning. D may be comparator-related; changing D is not the same run. No actual-feedback bound is proved merely by assuming it.

## result_18
1. **Objects:** One policy, one tuned schedule D/(G sqrt(T)), its run and positive T,D,G.
2. **Quantifiers:** Fix run data and premises first; then for EVERY u in C the bound holds.
3. **Hypotheses:** x1 in C; T,D,G>0; prefix S_V; played legality on the tuned run; all pairwise feasible distances<=D; actual selected norms<=G for all t<T.
4. **Conclusion:** For all u in C, R_T(u)<=D G sqrt(T).
5. **Order:** The same policy, tuned trajectory, and gradient bounds serve every comparator; no retuning per u is stated.
6. **Boundary:** Positive D is required even for a singleton domain. Future losses and later feedback are unconstrained.
7. **Scope:** Uniform-comparator tuned contract, not an anytime trajectory, a lower bound, or a global all-support norm theorem.

## result_19
1. **Objects:** V and the visible canonicalPolicy(t,past,h,f)=imported currentSubgradient(f,h_t).
2. **Quantifiers:** Every V; expanded OracleLaw quantifies every t,past,h,f.
3. **Hypotheses:** Inside OracleLaw, S_V(f) and h_t in C; no realized-history requirement.
4. **Conclusion:** Imported currentSubgradient(f,h_t) belongs to partial f(h_t) in every such case.
5. **Order:** canonicalPolicy ignores past losses except for taking the current point from h; its explicit function input is current f.
6. **Boundary:** Only the last history point must be feasible in this law. Definition/selection behavior of imported currentSubgradient is absent.
7. **Scope:** Universal oracle-validity contract for the canonical policy, not its proof or a specified numerical tie-break.

## result_20
1. **Objects:** V,a,f,x1,t and the canonical policy trajectory versus imported iterate.
2. **Quantifiers:** Every such data, every t.
3. **Hypotheses:** No feasibility, positive-step, loss-admissibility, or legality premises.
4. **Conclusion:** output(V,a,f,x1,canonicalPolicy,t)=imported iterate(V,a,f,x1,t).
5. **Order:** Exact same schedule, losses, initial point and index on both sides.
6. **Boundary:** t=0 included. Imported iterate recursion is not supplied, so the equality is decoded as a bridge contract without claiming independent verification of the right side.
7. **Scope:** Output compatibility, not equality of arbitrary policies or a performance claim.

## result_21
1. **Objects:** The same canonical run and imported currentSubgradient and iterate.
2. **Quantifiers:** Every V,a,f,x1,t.
3. **Hypotheses:** None beyond shared type structure.
4. **Conclusion:** selected(V,a,f,x1,canonicalPolicy,t)=imported currentSubgradient(f_t,imported iterate(V,a,f,x1,t)).
5. **Order:** Feedback uses the current loss f_t at the same-index imported iterate, not the next iterate.
6. **Boundary:** No support-validity premise: equality of expressions does not alone establish that either is a true support.
7. **Scope:** Selected-feedback bridge contract. The imported selection definition remains an explicit interpretation gap.

## Contract boundaries and missing interfaces

The visible finite-history recursion and optional-vs-played legality distinction are fully specified. Universal OracleLaw is used in result_9 and asserted for canonicalPolicy in result_19; it is not silently added to the numerical performance contracts. Results 11-12 intentionally have no initial-feasibility premise, while 10 and 13-18 do. Prefix equality is only for a common policy and common initial point. Tuning is tied to each specified horizon and actual run.

Exact interpretation of the imported mathematical predicates/operators still needs the missing definitions/specifications listed at the start: Domain, project, SourceSubdifferential, SubdifferentiableOn (including SourceProper), currentSubgradient, iterate, Metric.diam, Bornology.IsBounded, and finite/infinite toReal semantics. For example, if the conventional properness and global-support meanings are intended, properness plus actual supported query excludes infinite query values, and feasible comparator support similarly supplies finite comparator values; this is a conditional explanation, not an expansion justified by this packet. No packet content was supplemented by reading other runs or by assuming imported definitions from names.

All statements remain proposed contracts here. Only this report and its matching receipt were written. Requested model and effort describe the assignment; runtime identity was not independently attested.
