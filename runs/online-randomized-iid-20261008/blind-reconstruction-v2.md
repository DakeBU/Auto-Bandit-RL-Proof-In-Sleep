# Neutral reconstruction v2

Actor `/root/osd_blind`; requested GPT-6 Astra / medium, with neither runtime model nor effort independently attested. This reused automated actor has earlier staged neutral-decoder history and inherited background from other packets. This is not absolute blindness, human review or external independence. Only this packet, its listed neutral context and manifest were read for this reconstruction. No source identity, proof body or prior verdict was inspected. The Q declarations define closed propositions; defining a proposition is not proving it. This document reconstructs semantics without a source, proof or acceptance verdict.

## Notation and full assumption expansions

Let \(I=[0,1]\), \(I_t=\{i\in\mathbb N:i<t\}\), and
\[
H_t(\omega)=(Y_i(\omega))_{i\in I_t},\qquad
V(\omega)=(Y_i(\omega))_{i\in\mathbb N},\qquad
Z_t(\omega)=(S(\omega),H_t(\omega)).
\]
Finite and infinite function spaces carry their product measurable spaces, and seed-history pairs carry the product measurable space. \(\mathbb E_\mu\) denotes integration over the given measure, not a separate seed average. \(U\perp_\mu W\) denotes `IndepFun U W μ`, independence of the two complete random elements.

For concise formulas below, \(A(\Omega,\mathrm{Seed},\mu,Y,S)\) expands to: arbitrary types \(\Omega:\mathrm{Type}\ u\), \(\mathrm{Seed}:\mathrm{Type}\ v\), their measurable spaces, a measure \(\mu\) with probability-measure instance, a sequence \(Y:\mathbb N\to\Omega\to\mathbb R\) with every \(Y_t\) measurable and `iIndepFun Y μ`, and a measurable \(S:\Omega\to\mathrm{Seed}\) with \(S\perp_\mu V\). The latter is independence of the seed from the entire infinite outcome vector, not merely from each coordinate separately. No product representation of \(\Omega\), particular seed distribution, or standard-Borel assumption is present.

Write \(B(Y)\) for the additional all-time assumptions: each \(Y_t\) has the same distribution as \(Y_0\) under \(\mu\), and \(Y_t\in I\) almost surely. Bounds hold a.s. for each time, not pointwise on all samples. Let \(m=\int Y_0\,d\mu\). All universal formulas using A and B mean their full expansions; binder order is detailed in each item. No limit statement occurs in this packet.

## C0 — fixed expected-loss benchmark

In words, C0 is the real infimum of the expected finite cumulative squared loss as a single constant comparator ranges through the interval I:
\[
\forall\Omega\ [\text{measurable space}],\ \mu:\mathrm{Measure}(\Omega),\ Y:\mathbb N\to\Omega\to\mathbb R,\ T\in\mathbb N,
\quad C0(\mu,Y,T)=\inf\left\{\int\sum_{t<T}(u-Y_t(\omega))^2\,d\mu(\omega):u\in I\right\}.
\]

1. **Objects:** arbitrary measurable space, measure, real outcome functions, natural horizon and feasible real constant.
2. **Quantifiers:** definition arguments are space/structure, measure, Y, T; u is the variable in the image of I within the infimum.
3. **Assumptions:** no probability, outcome measurability, integrability, independence or support assumption in the definition.
4. **Operation:** `sInf` of the actual image of I under expected cumulative loss, an infimum outside the integral.
5. **Constants/normalization:** feasible interval [0,1], squared loss, sum at indices 0 through T-1, no division by T.
6. **Information/probability:** the comparator is fixed across times, seeds and outcomes. This is not the integral of the samplewise hindsight minimum. No interchange of infimum and expectation is licensed.
7. **Boundary:** T0 gives empty sums and value zero. The comparator set is not finite; a minimum or unique minimizer is not part of the definition. The real integral and infimum are totalized expressions; merely defining them does not certify integrability or attainment.

## C1 — excess of a supplied prediction sequence

In words, C1 subtracts C0 from the supplied sequence's expected cumulative squared loss:
\[
\forall\Omega\ [\text{measurable space}],\mu,Y,P,T,\quad
C1(\mu,Y,P,T)=\int\sum_{t<T}(P_t(\omega)-Y_t(\omega))^2\,d\mu(\omega)-C0(\mu,Y,T),
\quad Y,P:\mathbb N\to\Omega\to\mathbb R,\ T\in\mathbb N.
\]

1. **Objects:** measure, outcome sequence, supplied real prediction sequence and horizon.
2. **Quantifiers:** arguments in order are space/structure, μ, Y, prediction P, T.
3. **Assumptions:** no causal, measurable, feasible, independent or integrable condition is built in.
4. **Operation:** signed real subtraction of the fixed-comparator benchmark from expected prediction loss.
5. **Constants/normalization:** squared loss and range t<T; neither positive part nor absolute value nor average is used.
6. **Information/probability:** P is supplied; this definition generates no policy or recursion and does not restrict access to current or future outcomes.
7. **Boundary:** T0 is zero. Nonnegativity is a later claim under extra premises, not a defining property. The definition does not substitute samplewise hindsight regret.

## C2 — seed and strict-past information

In words, C2 is the sigma algebra on Ω pulled back from the measurable seed-history pair:
\[
\forall\Omega:\mathrm{Type}\ u,\ \mathrm{Seed}:\mathrm{Type}\ v\ [\text{measurable space}],\ S:\Omega\to\mathrm{Seed},\ Y:\mathbb N\to\Omega\to\mathbb R,\ t\in\mathbb N,
\quad C2(S,Y,t)=Z_t^{-1}\bigl(\mathcal M_{\mathrm{Seed}\times\mathbb R^{I_t}}\bigr).
\]
Here the inverse-image notation means the `MeasurableSpace.comap` sigma algebra, not an inverse function.

1. **Objects:** arbitrary Ω and measurable seed type, maps S and Y, finite-history index t, resulting measurable space on Ω.
2. **Quantifiers:** Ω, Seed, seed measurable structure, S, Y, t; Ω need not already have an ambient measurable-space instance.
3. **Assumptions:** no measure, measurable S/Y, independence, feasibility or law is required to define this comap.
4. **Operation:** pull back the product measurable structure through exactly \(\omega\mapsto(S\omega,(Y_i\omega)_{i<t})\).
5. **Constants/indices:** the finite subtype range t includes 0 and excludes t; no numerical normalization.
6. **Information/probability:** one whole seed/tape and strictly earlier targets are available. The current outcome is absent. The seed may encode all private random bits, with no requirement that its internal coordinates be independent.
7. **Boundary:** at t0 the history type is empty and only seed information remains; it is not necessarily the trivial sigma algebra. C2 is an exact comap, not an explicitly completed or augmented filtration.

## Q001 — regrouping joint independent inputs

For arbitrary measurable codomains, if S is independent of the complete pair (X,Y), and X is independent of Y, the pair (S,X) is independent of Y:
\[
\forall\Omega,\mathrm{Seed},\mathcal X,\mathcal Z\ [\text{measurable spaces}],\ \forall\mu\ [\text{probability}],
\forall S:\Omega\to\mathrm{Seed},X:\Omega\to\mathcal X,Y:\Omega\to\mathcal Z,
\quad [S,X,Y\text{ measurable}]\Longrightarrow
S\perp_\mu(X,Y)\Longrightarrow X\perp_\mu Y\Longrightarrow (S,X)\perp_\mu Y.
\]

1. **Objects:** four arbitrary-universe types, measurable structures, probability measure and three random elements.
2. **Quantifiers:** Ω, Seed, Χ, Ζ and their structures, μ/probability, S/X/Y, their three measurability proofs, joint seed independence, then X-Y independence.
3. **Assumptions:** exactly those shown. Independence of S from X and from Y separately is not a replacement for independence from the pair.
4. **Conclusion:** `IndepFun (fun ω => (S ω, X ω)) Y μ` for the actual paired map.
5. **Constants/indices:** none; no horizon, scalar loss, common-law or support premise.
6. **Information/probability:** all random elements live on the same probability space. The result concerns joint blocks, not three pairwise statements or a stochastic-kernel representation.
7. **Boundary:** no cardinality, standard-Borel, atomlessness or nondegeneracy restriction; no assertion about arbitrary additional side information.

## Q002 — current target independent of seed and strict history

For a measurable independent outcome family and a measurable seed jointly independent of the whole outcome vector, every current target is independent of the seed-history pair:
\[
\forall\Omega,\mathrm{Seed},\mu,Y,S,\quad A(\Omega,\mathrm{Seed},\mu,Y,S)
\Longrightarrow\forall t\in\mathbb N,\quad Z_t\perp_\mu Y_t.
\]

1. **Objects:** probability space, arbitrary measurable seed type, real outcome family and actual pair Zt.
2. **Quantifiers:** space and seed structures, μ/probability, Y, all-time measurability and family independence, S, seed measurability and whole-vector independence, then t.
3. **Assumptions:** A only; outcome laws need not coincide and no support bound is imposed. Family independence is `iIndepFun`, not merely pairwise independence.
4. **Conclusion:** independence of the actual entire seed plus finite strict-history random element from Yt.
5. **Constants/indices:** all natural t, history indices i<t.
6. **Information/probability:** the seed is independent of the full vector, including future outcomes, even though only strict history enters Zt. No extra hidden side information is permitted by this conclusion.
7. **Boundary:** at zero, seed plus empty tuple is independent of Y0; no fixed initial prediction is imposed.

## Q003 — monotonicity of the information spaces

For arbitrary S and Y, increasing the history index can only enlarge C2:
\[
\forall\Omega,\mathrm{Seed}\ [\text{Seed measurable}],\ S,Y,\quad
\forall s,t\in\mathbb N,\quad s\le t\Longrightarrow C2(S,Y,s)\le C2(S,Y,t).
\]
The order on measurable spaces means inclusion of measurable sets.

1. **Objects:** arbitrary maps to seed and real sequences and their induced measurable structures.
2. **Quantifiers:** Ω, Seed, seed measurable instance, S, Y, then the s,t and order premise expanded from `Monotone`.
3. **Assumptions:** only the typed data; no ambient measurable Ω, measure, independence, measurability of the maps relative to an ambient space, or boundedness.
4. **Conclusion:** monotonicity of the function t↦C2 S Y t.
5. **Constants/indices:** weak order s≤t, including equality and zero.
6. **Information/probability:** the seed is retained while more past target coordinates are included. This is a structural information claim without probability.
7. **Boundary:** does not say that C2 equals an arbitrary external filtration or its completion; no right-continuity or limiting sigma-algebra claim.

## Q004 — consumer for a supplied information-measurable prediction

Under A, any real prediction measurable with respect to a sigma algebra F contained in the available seed-history information is independent of the current target:
\[
\forall\Omega,\mathrm{Seed},\mu,Y,S,\quad A\Longrightarrow
\forall t\in\mathbb N\ \forall\mathcal F\le C2(S,Y,t)\ \forall P:\Omega\to\mathbb R,
\quad P\text{ is }\mathcal F\text{-measurable}\Longrightarrow P\perp_\mu Y_t.
\]

1. **Objects:** A's probability data, one time, a supplied measurable space F on Ω, and supplied real prediction P.
2. **Quantifiers:** A binders, t, F, the inclusion proof, P, then `Measurable[F] P`.
3. **Assumptions:** A and the exact inclusion F≤C2 plus measurability with F as domain structure. Ambient measurability alone is not the premise.
4. **Conclusion:** independence of P and Yt; no integrability or loss conclusion.
5. **Constants/indices:** single arbitrary natural t; no numerical bounds or normalization.
6. **Information/probability:** this consumes an already supplied restricted-information prediction. It covers sub-sigma-algebras of seed and strict history, not arbitrary correlated side information or arbitrary completion/augmentation of them.
7. **Boundary:** P may be unbounded; no common distribution of Y is required. At t0, allowable information is contained in the seed comap. No factorization into a measurable policy is asserted.

## Q005 — explicit seed-history policy produces independent predictions

Under A, every measurable deterministic policy of the seed and finite strict history yields a current prediction independent of the current target:
\[
\forall\Omega,\mathrm{Seed},\mu,Y,S,\quad A\Longrightarrow
\forall\pi:\prod_{t\in\mathbb N}(\mathrm{Seed}\times\mathbb R^{I_t}\to\mathbb R),
\quad [\forall t,\pi_t\text{ measurable}]\Longrightarrow\forall t\in\mathbb N,
\quad (\omega\mapsto\pi_t(S\omega,H_t\omega))\perp_\mu Y_t.
\]

1. **Objects:** measurable policy family and its explicit actual path, together with A data.
2. **Quantifiers:** A binders, policy, all-time measurability premise, then the tested t.
3. **Assumptions:** A and policy measurability on the complete seed-times-real-product domain. There is no policy feasibility, integrability or output bound.
4. **Conclusion:** independence of the actual composed prediction from Yt, not independence assumed for an arbitrary trace.
5. **Constants/indices:** policy receives i<t; no averaging, horizon or initial numerical constant.
6. **Information/probability:** policy input is exactly the seed first and history second. Randomization is via S on Ω; no independent fresh seed at every time is required. No current/future target or additional random argument appears.
7. **Boundary:** t0 permits arbitrary measurable seed-dependent output. No general theorem representing every randomized kernel or every information-measurable P in this form is asserted.

## Q006 — bounded information-measurable trace excess

For independent, identically distributed, a.s. feasible outcomes and an independent private seed, every supplied a.s. feasible prediction sequence measurable in supplied sub-information spaces has excess equal to a sum of squared distances from the common mean, and that excess is nonnegative:
\[
\forall\Omega,\mathrm{Seed},\mu,Y,S,\quad A\land B(Y)\Longrightarrow
\forall\mathcal F:\mathbb N\to\mathrm{MeasurableSpace}(\Omega),
\ [\forall t,\mathcal F_t\le C2(S,Y,t)]\Longrightarrow
\forall P:\mathbb N\to\Omega\to\mathbb R,
\ [\forall t,P_t\text{ is }\mathcal F_t\text{-measurable}]\Longrightarrow
\ [\forall t,P_t\in I\ \mu\text{-a.s.}]\Longrightarrow\forall T\in\mathbb N,
\quad C1(\mu,Y,P,T)=\sum_{t<T}\int(P_t-m)^2\,d\mu\ \land\ 0\le C1(\mu,Y,P,T).
\]

1. **Objects:** arbitrary-universe probability and seed data, outcome family, supplied information-space sequence and supplied prediction trace.
2. **Quantifiers:** Ω/Seed structures, μ/probability, Y, outcome measurability, same-law and a.s. bounds, family independence, S/measurability/whole-vector independence, F/inclusions, P/information-measurability/a.s. bounds, then T. A and B in the formula abbreviate this stated order.
3. **Assumptions:** all-time common law and a.s. support, joint family independence, seed independence from the whole vector, F inclusion and P measurability, plus a.s. feasible P. F itself is not explicitly required to be monotone.
4. **Conclusion:** exact equality and nonnegativity, both for the same supplied P and same C1 benchmark.
5. **Constants/normalization:** mean m is the integral of Y0, squared deviations, sum t<T, no division by T and no finite-time numerical upper bound.
6. **Information/probability:** a consumer of a supplied trace satisfying information restrictions; the trace is not recursively constructed here. Integrals average all randomness already in μ, including the seed. No exchange with a hindsight minimum or separate conditional seed integral is present.
7. **Boundary:** T0 yields zero and an empty sum. Initial prediction may depend on the seed. Pointwise feasibility at every sample is not required; no almost-sure convergence, expectation convergence, asymptotic rate or minimizer uniqueness is claimed.

## Q007 — bounded actual randomized policy excess

For the same probability, common-law and seed assumptions, a measurable policy that outputs a feasible real for every seed and every feasible finite history has the squared-deviation excess identity and nonnegative excess on its actual path:
\[
\forall\Omega,\mathrm{Seed},\mu,Y,S,\quad A\land B(Y)\Longrightarrow
\forall\pi:\prod_t(\mathrm{Seed}\times\mathbb R^{I_t}\to\mathbb R),
\ [\forall t,\pi_t\text{ measurable}]\Longrightarrow
\ [\forall t\ \forall s\in\mathrm{Seed}\ \forall z\in\mathbb R^{I_t},
\ (\forall i\in I_t,z_i\in I)\Rightarrow\pi_t(s,z)\in I]\Longrightarrow
\forall T\in\mathbb N,
\quad C1(\mu,Y,P^\pi,T)=\sum_{t<T}\int(P^\pi_t-m)^2\,d\mu\ \land\ 0\le C1(\mu,Y,P^\pi,T),
\quad P^\pi_t(\omega)=\pi_t(S\omega,H_t\omega).
\]

1. **Objects:** A/B probability data and a time-dependent measurable seed-history policy, with its defined actual prediction path.
2. **Quantifiers:** Ω/Seed structures, μ/probability, Y, measurability/same-law/a.s. support/independence, S and its two premises, policy, all-time measurability, all-time/all-seed/all-history conditional bound, then T.
3. **Assumptions:** A and B, full-domain policy measurability, and pointwise feasibility for every seed s when every coordinate of history z lies in I. This is not only a.s. seed feasibility. No bound is imposed for histories with infeasible coordinates.
4. **Conclusion:** exact squared-deviation equality and nonnegative C1 for the same explicitly composed Pπ. Neither a supplied independence premise for Pπ nor a replacement prediction sequence appears.
5. **Constants/normalization:** I endpoints 0 and 1, mean of Y0, finite sum t<T, no division or rate constant.
6. **Information/probability:** the current prediction receives the whole private seed and exactly finite strict-past outcomes. The all-seed legal-history premise is stronger than actual-path a.s. bounds; outcomes themselves are only a.s. feasible. C0 still optimizes one fixed comparator outside the integral over all seed/outcome randomness.
7. **Boundary:** at t0, empty-history feasibility is vacuous, so π0 must output in I for every seed but can depend on that seed. T0 gives zero. No kernel representation, unrestricted adaptive adversary, extra correlated side information, universal minimax claim or asymptotic no-regret statement is included.

## Scope and ambiguity record

No blocking ambiguity is present in the specified neutral types. Whole-vector seed independence and joint family independence must not be weakened to pairwise conditions. Q004/Q006 restrict the exact domain sigma algebra rather than only ambient measurability; they do not provide a policy-factorization theorem. Q005/Q007 explicitly compose a seed-history policy. Q006 allows merely a.s. prediction feasibility; Q007 requires feasibility for every seed and every legal history. The seed could encode arbitrary private side information independent of the entire outcome vector; outcome-correlated extra information is not covered. None of these statements establishes a representation for arbitrary randomized kernels, an asymptotic limit, proof correctness or source fidelity.
