# Genalti Theorem6: split-sample concentration with original constant8

Date: 2026-09-20. Mathematical reconstruction with separate source and repair reviews; see the bound receipt.
Source: Genalti et al. COLT2024, genalti24a.pdf SHA256 65eceb2cd402baa8c7f5b60d273a103fbd181cf6803a4b7f0d2f4092742fe5b6, Theorem6 Eq18 p10 and proof pp27–28. Prerequisite: the event-semantic Theorem5 reconstruction in genalti-root-concentration.md, requiring independent acceptance. No concentration statement is imported from the old source merely because it is printed.

## Contract

Let p in (1,2], u>=0 finite, delta in (0,1/4), L=log(1/delta), n>=2, s=2n. Let X_1,...,X_n and X'_1,...,X'_n be two INDEPENDENT samples, all iid from a real law nu with integral |x|^p<=u. Duplicates remain indexed observations. Define mu=E X; integrability follows from |x|<=1+|x|^p. Let c=(1+sqrt2)^2 and E be the unique-root event for the threshold sample X', using exactly n terms and a=cL. Let Mhat solve the threshold equation on E and extend it by0 outside E. On E define
muhat=(1/n)sum_j X_j 1_{|X_j|<=Mhat}.
An arbitrary measurable extension outside E has no role in the theorem.

The target is the explicit intersection-event statement
P(E intersect {|muhat-mu|>8 u^(1/p)(L/s)^((p-1)/p)})<=4delta.
Thus, with probability at least1-4delta, the bound holds whenever the unique root exists. This is not a conditional-on-E claim. No truncated non-positivity assumption is needed. u=0 implies P(E)=0 and is vacuous; take u>0 below.

## Direct uncentered MGF avoids an unjustified centered-range substitution

Fix deterministic M>0 and Y=X1_{|X|<=M}. Put v_M=EY^2<=u M^(2-p). For any real y with |y|<=M and lambda>0, termwise expansion gives
exp(lambda y)<=1+lambda y+(y^2/M^2)(exp(lambda M)-1-lambda M).
Indeed |y|^k<=y^2 M^(k-2) for k>=2; negative odd terms are bounded above by their absolute values. Taking expectations, using log(1+x)<=x (the upper-bound expression is positive as it bounds an exponential expectation), and centering ONLY after this estimate gives
log E exp(lambda(Y-EY))<= (v_M/M^2)(exp(lambda M)-1-lambda M).
The same applies to -Y. Thus for either sign and 0<lambda<3/M, independence yields the sum bound
log E exp(lambda sum_j (Y_j-EY))<= n v_M lambda^2/(2(1-M lambda/3)).
The power-series denominator uses k!>=2*3^(k-2). We have not asserted |Y-EY|<=M; that claim can be false. The parameter M here comes from the UNcentered power-series bound and raw second moment.

Put v=n v_M and b=M/3. If v>0, define r=sqrt(2L/v), lambda=r/(1+b r). For t=sqrt(2vL)+bL, direct substitution gives
-lambda*t+v lambda^2/(2(1-b lambda))=-L.
Markov gives each signed tail probability at most delta. If v=0, Y=0 almost surely, hence the centered sum is zero and the conclusion is immediate. Consequently with probability at least1-2delta at fixed M,
|mean(Y)-EY|<=sqrt(2 v_M L/n)+M L/(3n).
Replacing v_M by its raw-moment upper bound is valid.

## Conditioning on the independent threshold sample

The threshold is a measurable function of X' alone. The map (x,M)->x1_{|x|<=M} is jointly Borel, and its absolute value is bounded by |x|, integrable under nu. Its expectation is therefore measurable in M; conditional integration is legitimate. Independence means that, for every fixed realization of X' on E, the mean sample remains nu^n. Applying both signed fixed-M bounds and integrating over X' gives an intersection-event failure probability at most2delta. This is conditional on the threshold SAMPLE, not an assertion that trimmed observations are independent without conditioning. Outside E no threshold guarantee is claimed.

Separately, the reconstructed Theorem5 gives probability at most2delta for root event E with either
Mhat>B=(un/L)^(1/p) or tail(Mhat)>beta=(1+2sqrt2)^2 L/n.
The simplification uses sqrt(c)-sqrt2=1. Keep this SAME root-good event for both mean tails. A union of the root-bad event (2delta) and the two mean-tail events (delta each) costs4delta, not6delta.

## Bias, normalization and source constant8

Holder gives for every M>0
|EY-mu|<=E[|X|1_{|X|>M}]<=u^(1/p) tail(M)^q,
where q=(p-1)/p in (0,1/2]. On the intersection of root-good and mean-good events within E, put A=u^(1/p)(L/n)^q. Then
sqrt(2u Mhat^(2-p)L/n)<=sqrt2 A,
Mhat L/(3n)<=A/3,
u^(1/p)tail(Mhat)^q<=(1+2sqrt2)^(2q) A<=(1+2sqrt2) A.
The first comparison uses 2-p>=0; it includes p=2 without introducing a negative exponent. Summing yields
|muhat-mu|<=(4/3+3sqrt2) A.
Since n=s/2, A=2^q u^(1/p)(L/s)^q, and 2^q<=sqrt2. Finally
(4/3+3sqrt2)*sqrt2=6+(4sqrt2)/3<8,
because sqrt2<3/2. The desired constant8 thus holds with failure4delta and the source total-sample normalization. No 5.6 rounding or unsupported centered bound is needed.

## Scope and remaining work

This proves the source-sized split-sample concentration endpoint as a qualified intersection-event theorem at fixed n, with the same constant8 and total-sample denominator s. It uses original signed truncated observations, independent sample splitting, raw moments and a threshold computed from exactly the other n observations. It does not supply the missing root outside E or accept the literal source algorithm's guard. The root repair, event semantics and proof route are explicit deltas.

The earlier audit's centered-Bernstein concern is resolved by the direct UNcentered MGF argument above, not by pretending a centered variable has absolute bound M. This does not certify every printed proof step. Conditional-on-root-existence probabilities, adaptive sample counts, empirical-variance indices, forced exploration, Eq57 count constants, full regret and Lean formalization remain separate obligations. No author-issued correction is asserted.

## Publication and formalization boundary

Evidence: `runs/extended-topics-20260919/genalti-concentration-audit.json` binds the unchanged private derivations and separate reviews. This page changes only source/provenance documentation. No new Lean declaration, public-root import, canary, graph node, site build, main merge or deployment is claimed. All-ten topic completion remains0/10. Functor classification: none-found-with-reason; this mathematical mechanism is not a certified cross-topic bridge.

Formalization retrieval: searched the shared HeavyTail algorithm modules and Mathlib Probability/Moments for Bernstein, sub-gamma and Chernoff interfaces, and checked the local probability theorem cards. The sub-Gaussian card (`MLIB-PROBABILITY-SUBGAUSSIAN`) provides a different quadratic MGF contract and is not evidence for the rational-denominator bound used here. No exact compiled implementation of this new root/uncentered-MGF chain was identified in that bounded search. Candidate foundations are finite independent products, exponential integrals, and measurable parameter integration in the existing project; compatibility is not yet established. Status: mathematical proof complete in the reviewed scope, Lean interface/proof work outstanding. No imported concentration theorem is hidden as an assumed consumer premise.

The subsequent `GENALTI24-ADAPTIVE-PREFIX-CONCENTRATION.md` supplies the fixed-prefix union and pathwise adaptive-count transfer for these events under explicit causal iid paired streams. That limited transfer does not establish the empirical-variance index or full regret.
