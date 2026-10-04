# Policy v2: semantic reconstruction of 21 contracts

Only blind-packet-v2.md was opened. IMPORTANT evidence limitation: despite its proof-omission labels, the supplement contains repeated full proof bodies for an imported numbered lemma. Those bytes were exposed by reading the authorized packet. No proof of the 21 targets was supplied, no other file was opened, and no proof was verified. This report must not be represented as a strictly proof-unexposed decoding. The numbered imported identifier was visible; no literature identity was sought or inferred. This is automated semantic reconstruction, not human review, source acceptance, or compilation.

## Shared exact semantics

Every claim is universally quantified over a finite-dimensional real inner-product space E, all its displayed data, and the specified hypotheses. C=V.carrier is nonempty, closed and real-convex. P_C is the actual chosen nearest-point projection: P_C(z) belongs to C and norm(z-P_C(z))=inf_{w in C} norm(z-w).

Proper(f) means f never equals negative infinity and there exist y0 in E and r in R with f(y0)=coe(r). Define the ambient global support set
\[
\partial f(x)=\{g\in E:\forall y\in E,
 f(x)+\operatorname{coe}(\langle g,y-x\rangle)\le f(y)\}.
\]
S_C(f) means Proper(f) and nonemptiness of this set at every x in C. The inequalities test every ambient y, not only feasible points. No separate global loss-convexity or differentiability assumption is supplied. Positive infinity outside supported points remains possible.

A policy has type
\[
p:\prod_t(\operatorname{Fin}(t)\to(E\to\mathrm{EReal}))
 \to(\operatorname{Fin}(t+1)\to E)\to(E\to\mathrm{EReal})\to E.
\]
For fixed V, schedule a, losses f_t, initial x1 and policy p, define H_t, X_t and g_t by
\[
H_0=(x_1),\quad X_t=H_t(t),\quad
 g_t=p(t,(f_s)_{s<t},H_t,f_t),\quad
 H_{t+1}=\operatorname{snoc}(H_t,P_C(X_t-a_tg_t)).
\]
Fin.snoc appends one entry and keeps the prior entries; H_t contains t+1 outputs. Thus X_0=x1 despite the spelling of the parameter. The current function f_t is observed for selection after X_t has been formed from past inputs. Policies receive entire functions, not only numerical oracle values. No comparator, horizon, schedule, or future loss is an explicit policy argument, but external selection of a policy or initialization is not constrained. Claims comparing input sequences keep the same policy.

OracleLaw(C,p) means: for every t, every arbitrary past function vector, every arbitrary output vector h and every f, if S_C(f) and h_t in C then p(t,past,h,f) belongs to partial f(h_t). Past/h need not be realized histories, and earlier entries of h need not be feasible. LegalFeedback through T means only that g_t belongs to partial f_t(X_t) for every t<T on the specified actual run. It imposes no off-path condition. The universal law is optional and is not a hidden hypothesis of the cumulative performance bounds.

The canonical chooser c(f,x) is a classical choice from partial f(x) when nonempty and zero otherwise. The canonical policy ignores past losses and all history entries except the current point, returning c(f,h_t). The imported canonical iteration I_t is I_0=x1 and I_{t+1}=P_C(I_t-a_t c(f_t,I_t)). Its selection is noncomputable and no numerical tie-breaking rule is given.

Set q^R(v)=toReal(q(v)) and R_T(u)=sum_{t<T}(f_t^R(X_t)-f_t^R(u)). Both infinite EReal endpoints map to zero, while finite coe(r) maps to r. Bare regret therefore does not ensure genuine finite losses. Properness plus a support at v supplies finiteness: compare its inequality with the proper finite witness y0 to exclude positive infinity, while properness excludes negative infinity. Feasible v obtains support from S_C(f). At an arbitrary supported query, its supplied support suffices even without feasibility. These are semantic explanations, not claimed formal proof validation.

The packet defines ediam(C) as the ENNReal supremum of all pairwise extended distances and diam(C)=ENNReal.toReal(ediam(C)); it supplies boundedness iff ediam(C) is not top. Hence boundedness ensures the extended diameter is finite before real conversion. ENNReal.toReal's full definition is not copied in this packet; its standard infinite-to-zero convention must not be confused with a supplied definition of EReal.toReal. The displayed equivalence suffices to state the boundedness premise exactly, and the diameter expression is preserved literally below.

## result_1
1. Objects: any V,a,f,x1,p and H_0.
2. Quantifiers: every such run.
3. Hypotheses: none beyond shared structure.
4. Conclusion: H_0 is the constant function x1 on Fin(1).
5. Order: initialization precedes all loss/feedback inputs.
6. Boundary: x1 need not be feasible.
7. Scope: initialization identity only.

## result_2
1. Objects: any run and natural t.
2. Quantifiers: every run and t.
3. Hypotheses: no feasibility, legality, or step-sign condition.
4. Conclusion: H_{t+1}=snoc(H_t,P_C(X_t-a_tg_t)).
5. Order: the true projected next point is appended after current selection.
6. Boundary: zero/negative real steps and unsupported policies are allowed.
7. Scope: exact finite-history recursion, not performance.

## result_3
1. Objects: any run and X_0.
2. Quantifiers: every V,a,f,x1,p.
3. Hypotheses: none.
4. Conclusion: X_0=x1.
5. Order: initial index is zero.
6. Boundary: feasibility not required for the identity.
7. Scope: initial output equality only.

## result_4
1. Objects: any run, t, X_t,g_t,X_{t+1}.
2. Quantifiers: all such data.
3. Hypotheses: none beyond shared structure.
4. Conclusion: X_{t+1}=P_C(X_t-a_tg_t).
5. Order: current support selection affects the next output.
6. Boundary: no positivity or legality assumption.
7. Scope: actual projected update identity.

## result_5
1. Objects: H_t and i in Fin(t+1).
2. Quantifiers: every run, t and valid i.
3. Hypotheses: x1 in C.
4. Conclusion: H_t(i) in C.
5. Order: all stored outputs through t are feasible.
6. Boundary: no assumptions on loss regularity, policy legality or step signs.
7. Scope: projection-based feasibility contract, not support or finite-value validity.

## result_6
1. Objects: any run and X_t.
2. Quantifiers: every t.
3. Hypotheses: x1 in C.
4. Conclusion: X_t in C.
5. Order: includes initial and successor outputs.
6. Boundary: arbitrary policy and real schedule allowed.
7. Scope: output feasibility only.

## result_7
1. Objects: runs with common V,x1,p but schedules a,a' and losses f,f', time t.
2. Quantifiers: every such common-policy pair and t.
3. Hypotheses: a_s=a'_s and f_s=f'_s for all s<t; function equality is global equality of entire loss functions.
4. Conclusion: H_t=H'_t as functions on Fin(t+1).
5. Order: strict-prefix agreement suffices; current/future inputs may differ.
6. Boundary: t=0 hypotheses are vacuous; no feasibility or legality required.
7. Scope: common-policy causality, not equality for different policies or merely matching observed loss values.

## result_8
1. Objects: the same paired run data.
2. Quantifiers: every common-policy pair and t.
3. Hypotheses: schedules and loss functions agree for s<t.
4. Conclusion: X_t=X'_t.
5. Order: f_t may differ, so selected feedback need not agree.
6. Boundary: t=0 gives the common initial point without other premises.
7. Scope: output prefix invariance; external generation of p,x1,a is not constrained.

## result_9
1. Objects: any run, p and natural T.
2. Quantifiers: every such run meeting the premises.
3. Hypotheses: x1 in C; OracleLaw(C,p); S_C(f_t) for all t<T.
4. Conclusion: LegalFeedback on this run through T, namely all actual g_t are global supports at X_t.
5. Order: a universal law yields legality at realized histories.
6. Boundary: T=0 is vacuous; step signs unrestricted.
7. Scope: sufficient route to legality, with no converse asserted.

## result_10
1. Objects: any run, selected time t and comparator u.
2. Quantifiers: every such data under the premises.
3. Hypotheses: x1 in C, S_C(f_t), u in C; no policy-law or legality premise.
4. Conclusion: f_t(X_t)=coe(f_t^R(X_t)) AND f_t(u)=coe(f_t^R(u)).
5. Order: both finite values concern the current loss, before its update.
6. Boundary: arbitrary earlier losses and step signs allowed. Feasibility plus S_C supplies supports even if p selects an illegal vector.
7. Scope: actual finite-value representation, not a bound or mere toReal operation.

## result_11
1. Objects: any actual run, time t, selected g_t and comparator u.
2. Quantifiers: every such data meeting the premises, with no initial-feasibility requirement.
3. Hypotheses: a_t>0; S_C(f_t); g_t in partial f_t(X_t); u in C.
4. Conclusion, as two conjuncts:
\[
a_t(f_t^R(X_t)-f_t^R(u))\le a_t\langle g_t,X_t-u\rangle,
\]
\[
a_t\langle g_t,X_t-u\rangle\le\|X_t-u\|^2/2-\|X_{t+1}-u\|^2/2+a_t^2\|g_t\|^2/2.
\]
5. Order: actual selected vector and next projected output, not hypothetical replacements.
6. Boundary: an infeasible X_0 is allowed if its supplied support is genuine; properness plus that support makes the queried value finite. Feasible u is finite from S_C. Zero/negative current step excluded.
7. Scope: single-step two-stage bound under current played membership, without a universal policy law.

## result_12
1. Objects: the same run, t and u.
2. Quantifiers: all such data with the same premises.
3. Hypotheses: a_t>0; S_C(f_t); actual g_t in partial f_t(X_t); u in C; no x1 in C premise.
4. Conclusion:
\[
f_t^R(X_t)-f_t^R(u)\le(\|X_t-u\|^2-\|X_{t+1}-u\|^2)/(2a_t)+(a_t/2)\|g_t\|^2.
\]
5. Order: current finite loss difference bounded via actual next output.
6. Boundary: denominator strictly positive; supported query may be infeasible.
7. Scope: scalar one-step upper bound only.

## result_13
1. Objects: constant schedule a_t=eta, policy run, natural T and comparator u.
2. Quantifiers: every such run and feasible comparator.
3. Hypotheses: eta>0; x1,u in C; S_C(f_t) for t<T; LegalFeedback on this exact constant-step run through T.
4. Conclusion:
\[
R_T(u)\le\|x_1-u\|^2/(2\eta)+(\eta/2)\sum_{t<T}\|g_t\|^2-\|X_T-u\|^2/(2\eta).
\]
5. Order: sum uses t<T; retained negative residual uses terminal X_T.
6. Boundary: T=0 allowed and initial/terminal terms cancel; no domain or support bound required.
7. Scope: constant-step cumulative contract, needing only actual legality rather than OracleLaw.

## result_14
1. Objects: constant-step policy run, T and u.
2. Quantifiers: every such run and feasible u.
3. Hypotheses: eta>0, feasible initial/comparator, prefix S_C and played LegalFeedback for that same schedule.
4. Conclusion: R_T(u)<=norm(x1-u)^2/(2 eta)+(eta/2) sum_{t<T} norm(g_t)^2.
5. Order: same actual norm sum; terminal residual absent.
6. Boundary: T=0 yields zero bounded by the initial-distance term.
7. Scope: coarse cumulative estimate, not a numerical rate without norm control.

## result_15
1. Objects: variable schedule a, actual p-run, T, real D and comparator u.
2. Quantifiers: every such data satisfying all conditions.
3. Hypotheses: x1,u in C; T>0; a_t>0 for t<T; a_{t+1}<=a_t when t+1<T; S_C(f_t) for t<T; LegalFeedback for this run; norm(x-y)<=D for all x,y in C.
4. Conclusion:
\[
R_T(u)\le D^2/(2a_{T-1})+\sum_{t<T}(a_t/2)\|g_t\|^2-\|X_T-u\|^2/(2a_{T-1}).
\]
5. Order: denominator is last used a_{T-1}; terminal output is X_T; norm weights use their own steps.
6. Boundary: T=0 excluded, T=1 monotonicity vacuous. D need not be strictly positive; nonempty C implies D>=0. D=0 can force singleton C without forcing ambient supports to vanish.
7. Scope: positive nonincreasing used-prefix estimate with an explicit pairwise upper bound, not an exact diameter requirement.

## result_16
1. Objects: variable p-run, T, feasible u and delta=Metric.diam(C).
2. Quantifiers: every such data meeting the hypotheses.
3. Hypotheses: x1,u in C; T>0; positive nonincreasing used-step prefix; prefix S_C; actual LegalFeedback; bounded C, equivalently ediam(C) not top.
4. Conclusion: R_T(u)<=delta^2/(2a_{T-1})+sum_{t<T}(a_t/2)norm(g_t)^2-norm(X_T-u)^2/(2a_{T-1}).
5. Order: both endpoint denominators use a_{T-1}, never a_T; terminal state X_T.
6. Boundary: boundedness ensures finite extended diameter before real conversion; a real codomain alone does not certify a usable diameter bound. Singleton delta is zero. T=0 excluded.
7. Scope: bounded-domain metric-diameter version; no boundedness premise may be silently dropped.

## result_17
1. Objects: policy p, T,D,G,u, and constant schedule a_t=D/(G sqrt(T)).
2. Quantifiers: every such data and particular comparator satisfying the conditions.
3. Hypotheses: x1,u in C; T,D,G>0; prefix S_C; LegalFeedback on exactly this tuned run; norm(x1-u)<=D; norm(g_t)<=G for every t<T on exactly this run.
4. Conclusion: R_T(u)<=D G sqrt(T).
5. Order: schedule, legality, actual support norms and regret share the same trajectory. Changing T or D can change the entire run.
6. Boundary: zero T,D,G excluded; denominator and step positive. No global diameter assumption required.
7. Scope: comparator-distance tuning, not global support bounds or uniformity over differently tuned runs.

## result_18
1. Objects: fixed p and one tuned run with a_t=D/(G sqrt(T)).
2. Quantifiers: fix V,f,x1,p,T,D,G and premises; then the conclusion holds for every u in C.
3. Hypotheses: x1 in C; T,D,G>0; prefix S_C; played legality on the tuned run; all feasible pairwise distances<=D; actual selected norms<=G for t<T.
4. Conclusion: for all u in C, R_T(u)<=D G sqrt(T).
5. Order: one policy/run/schedule serves all comparators. No u enters the legality or norm premise.
6. Boundary: D must be positive even for singleton C; future losses and future legality are unrestricted.
7. Scope: uniform comparator bound for a horizon-tuned family, not an anytime schedule or lower bound.

## result_19
1. Objects: V and canonicalPolicy(t,past,h,f)=c(f,h_t).
2. Quantifiers: every V and, through OracleLaw, every t,past,h,f.
3. Hypotheses: inside that law, S_C(f) and h_t in C only.
4. Conclusion: c(f,h_t) is a global support of f at h_t.
5. Order: canonical policy ignores past losses and earlier history entries; uses the current f and point.
6. Boundary: histories can be unrealized; only the last entry needs feasibility. Nonempty support makes the classical-choice branch applicable. No tie-break is specified.
7. Scope: universal canonical-policy oracle contract, not universal legality for arbitrary policies.

## result_20
1. Objects: canonical-policy output X_t and supplied imported canonical recursion I_t.
2. Quantifiers: every V,a,f,x1,t.
3. Hypotheses: no feasibility, positivity, S_C or legality requirements.
4. Conclusion: X_t=I_t, where I_0=x1 and I_{s+1}=P_C(I_s-a_s c(f_s,I_s)).
5. Order: same schedule, losses, initial point and time on both sides.
6. Boundary: t=0 included; fallback behavior is allowed when supports are empty.
7. Scope: exact output compatibility contract, not a performance claim.

## result_21
1. Objects: canonical-policy selected g_t, current f_t and canonical I_t.
2. Quantifiers: every V,a,f,x1,t.
3. Hypotheses: none beyond shared structure.
4. Conclusion: g_t=c(f_t,I_t).
5. Order: current loss at same-index state, not the next state.
6. Boundary: equality alone does not establish membership when the support set is empty; c then uses zero fallback.
7. Scope: exact feedback compatibility, complementary to output compatibility.

## Scope, ambiguities, and receipt status

All target signatures can now be interpreted using supplied definitions. The full ENNReal.toReal definition is not displayed, but the metric target is stated exactly as the supplied diam composition with finite ediam guaranteed by boundedness; no unbounded-diameter behavior is needed for its stated premise. No mathematical strengthening is inserted. Zero-dimensional spaces are allowed; nonempty C then contains only the zero vector. Singleton and lower-dimensional feasible sets are allowed. Loss convexity, differentiability, global finiteness and support-norm bounds are not silently added. Supports are ambient global supports, even on a lower-dimensional carrier.

The material evidence defect is the included imported proof body and numbered imported identifier. This prevents an honest proof-unexposed receipt even though only the authorized packet was read and no target proof was present. The report makes no claim that those imported proofs were checked, that any target is proved/compiled, or that a literature source has been accepted. All 21 are decoded as contracts.

Only fresh v2 report/receipt files were written. No earlier files or outside source were read or modified. Requested model and effort identify the assignment, not independently verified runtime identity.
