# Fifty-target neutral reconstruction

Actor /root/osd_blind; requested GPT-6 Astra / medium, runtime model and effort unverified. This reused automated decoder retains prior staged history. No absolute blindness, human review or external independence is claimed. Only the designated packet, index and two indexed mathematical files were read. Visible names were not investigated. This report reconstructs types without proving, compiling or accepting sources/chapters.

## Context and conventions

All sums over t<T mean indices 0,...,T-1; natural scalars are coerced to reals. Real division is totalized. Types X, Ω and Seed are arbitrary in their indicated universes. Measurable structures/probability instances are included only where specified. The 23 supplied context definitions are:

1. \(R_T(\ell,q,u)=\sum_{t<T}\ell_t(q_t)-\sum_{t<T}\ell_t(u)\), signed comparator regret for arbitrary actions/losses.
2. \(U(V,\ell,q)\equiv\forall u\in V\,\forall\epsilon>0\,\exists N\,\forall T\ge N,\ R_T/T\le\epsilon\). N may depend on u,ε; one-sided eventual upper condition.
3. \(L(V,\ell,q)\equiv\forall u\in V\,\exists a\in\mathbb R,\ a\le0\land R_T/T\to a\). Ordinary finite real limits, potentially different for each comparator.
4. \(e_T(y)=\sum_{t<T}y_t/T\), empirical mean with e0=0.
5. \(p_0(y)=1/2,\ p_t(y)=e_t(y)\) for positive t, actual strict-past mean prediction.
6. \(p^a_0(y)=a,\ p^a_t(y)=e_t(y)\) for positive t.
7. State update \(D((n,x),z)=(n+1,x+(z-x)/(n+1))\).
8. Actual state \(S^a_0(y)=(0,a),\ S^a_{t+1}(y)=D(S^a_t(y),y_t)\).
9. \(G_T(y,q)=\sum_{t<T}(q_t-y_t)^2-\inf_{u\in I}\sum_{t<T}(u-y_t)^2\), I=[0,1]. Realized-prefix best regret, no expectation.
10. \(B_T(\mu,Y)=\inf_{u\in I}\mathbb E_\mu\sum_{t<T}(u-Y_t)^2\), fixed comparator optimized outside integration, not expected hindsight minimum.
11. \(E_T(\mu,Y,Q)=A_T(Q)-B_T\), \(A_T(Q)=\mathbb E_\mu\sum_{t<T}(Q_t-Y_t)^2\).
12. \(\mathcal G_t=\operatorname{comap}_{\omega\mapsto(S\omega,(Y_i\omega)_{i<t})}\mathcal M_{\mathrm{Seed}\times\mathbb R^{J_t}}\), Jt={i:i<t}, exact seed/strict-past information.
13. \(H_t=I^{\operatorname{Fin}t}\times\mathbb R^{\operatorname{Fin}t}\), kernel history.
14. \(\mathcal K=\prod_t(H_t\to I\to I)\), sampler families.
15. \(a_0=()\), \(a_{t+1}(f,u,y)=\operatorname{snoc}(a_t(f,u_{<t},y_{<t}),f_t(a_t(f,u_{<t},y_{<t}),y_{<t})(u_t))\), actual generated actions.
16. \(b_t(f,u,z)=f_t(a_t(f,u_{<t},z),z)(u_t)\), before-reveal kernel policy.
17. \(c_t(f,(u,y))=(a_t(f,u_{<t},y_{<t}),y_{<t})\), actual generated history.
18. \(q_t(f,(u,y))=b_t(f,u,y_{<t})\), one infinite prediction process.
19. \(d_0=0,\ d_{n+1}=1-d_{\lfloor n/2\rfloor}\), dyadic observation, natural predecessor division.
20. Binary stream of list h: entry t of reverse(h), default false beyond length.
21. Binary real values: 1 for true, 0 for false.
22. Boolean causal predictor: \(q_t=A(\operatorname{reverse}[y_0,\ldots,y_{t-1}])\), strict-past newest-first list.
23. Path regret of h: this causal predictor's squared regret over length(h) against the empirical mean of the complete binary prefix. h is newest-first; reversing h gives chronological observations.

All regret definitions above vanish at T0 (infimum image {0}); normalized T0 values are zero. Bare integrals and real infima are totalized, not evidence of integrability/attainment. Positive empirical means differ from initial prediction. Write \(C_T(y,u)=\sum_{t<T}(u-y_t)^2\), and \(R_T^y(q,u)\) for squared comparator regret, omitting q when q=p(y).

The following exact recurring premises abbreviate full universal scopes:
- \(\mathsf B(\mu,Y)\): measurable Ω, probability μ, real process Y; every Yt measurable, identically distributed with Y0 under μ, and Yt∈I μ-a.e. All-time AE support, not pointwise.
- \(\mathsf D(Y)\): joint family independence iIndepFun Y μ, separate from common law.
- \(\mathsf S(S,Y)\): measurable Seed and measurable S, independent of the entire infinite vector \(\omega\mapsto(Y_t\omega)_t\), not merely each coordinate.
- \(\mathsf H(\pi)\): all-time measurability on the whole finite real-history domain and \(\forall t,z,(\forall i<t,z_i\in I)\Rightarrow\pi_t(z)\in I\).
- \(\mathsf H_S(\pi)\): all-time measurable seed-history policy and \(\forall t,s,z,(\forall i<t,z_i\in I)\Rightarrow\pi_t(s,z)\in I\). Every seed, only legal histories; empty-history antecedent vacuous.
Let \(m=\mathbb E Y_0,\ v=\operatorname{Var}_\mu Y_0,\ D_T(Q)=\sum_{t<T}\mathbb E(Q_t-m)^2\).
\(\mathrm{AESM}_{F,\mu}(P)\) denotes AEStronglyMeasurable[F] P μ: an F-strongly-measurable representative equals P ambient-μ-a.e. \(\mathcal E_\mu(F)\) denotes eventuallyMeasurableSpace F (ae μ), the eventual measurable structure, not a changed measure or merely ambient measurability. F need not be monotone. Limits use natural atTop and real nhds; little-o is a magnitude condition, not merely an upper bound.

## Missing context / transcription limits

The actual definition of kernelGameLaw is absent. In A003 retain it as opaque \(\Lambda_\nu\); its tape law, independence/freshness and normalization cannot be reconstructed from this packet, and earlier memory is not used to fill it.

A046 has no visible separator between the let value and the concluding conjunction: the exact line reads “let prediction := fun t ω => policy t (S ω, fun i => Y i ω) (∀ T, ...)”. The intended mathematics is readable, but exact binding is ambiguous/possibly malformed. Its entry is conditional on inserting the intended let-body separator; corrected exact text is requested.

A050 does not supply harmonic's definition. Conventional harmonic-number indexing is noted only conditionally; exact indexing/coercion remains a context request, not a fact imported from earlier memory.

## Individual targets

Each entry has prose, LaTeX and seven numbered slots. Abbreviations expand as above.

### A001

Every measurable randomized bounded Boolean-history rule has a fixed binary length-T witness with logarithmic expected path regret.

\[
\forall(\Omega,\mu\text{ probability}),A,\ [\forall h,A(\cdot,h)\text{ measurable}]\Rightarrow[\forall\omega,h,A(\omega,h)\in I]\Rightarrow\forall T>0,\ \exists v\in\mathrm{Vector}(\mathrm{Bool},T),\ \log(T+2)/6\le\mathbb E_\mu\mathrm{pathRegret}(A_\omega,v).
\]

1. **Objects:** Probability space, seed-indexed history rule, fixed-length binary vector and path regret.
2. **Quantifiers/order:** Ω/structure, μ/probability, A, measurability, global bound, T, positivity, then ∃v before integration.
3. **Assumptions:** Every seed and every Boolean list output lies in I, not AE/only reached histories.
4. **Conclusion/metric:** Logarithmic lower bound for one witness independent of sampled ω.
5. **Constants/indices/boundary:** T>0; log(T+2)/6; list length exactly T, no empty case.
6. **Information/probability:** A sees newest-first strict past; comparator is full-prefix mean of the chosen path. Seed randomness is averaged after selecting v.
7. **Excluded scope:** No simultaneous witness for all T or samplewise lower bound; no observation-law independence premise needed.

### A002

An AE information-measurable bounded supplied trace has exact nonnegative expected fixed-comparator excess.

\[
\forall\mathsf B,\mathsf D,\mathsf S,\ F\le\mathcal G,\ Q,\ [\forall t,\mathrm{AESM}_{F_t,\mu}(Q_t)]\Rightarrow[\forall t,Q_t\in I\ {\rm ae}]\Rightarrow\forall T,\ E_T(Q)=D_T(Q)\land E_T(Q)\ge0.
\]

1. **Objects:** Arbitrary measurable Ω/Seed, probability process, seed, information sequence and supplied trace.
2. **Quantifiers/order:** Ω,Seed,μ,Y; measurable/common-law/AE-support/independent Y; S and its premises; F/inclusions; Q/AE-measurability/bounds; T.
3. **Assumptions:** Full bundles B,D,S; every-time inclusion F_t≤G_t; ambient-μ AE strong measurability and AE feasibility.
4. **Conclusion/metric:** Equality and nonnegativity for original Q, not only a representative.
5. **Constants/indices/boundary:** Squares about m; unnormalized t<T sum; T0 both sides zero.
6. **Information/probability:** Restricted-information version supplied; whole-stream seed independence; fixed comparator outside expectation.
7. **Excluded scope:** No constructed policy, F monotonicity, pointwise equality/bounds or rate.

### A003

One sampler realizes all supplied Markov kernels with actual recursive consistency, all-law joint/conditional identities and a conditional iid excess identity.

\[
\forall\kappa\ {\rm Markov},\ \exists f,\ J(f)\land K(f,\kappa)\land B_m(f)\land A_c(f)\land P_c(f)\land\forall\nu,\ [\forall t,\ (c_t,q_t)_*\Lambda_\nu=(c_t)_*\Lambda_\nu\otimes_m\kappa_t]\land[\forall t,\operatorname{condDistrib}_{\Lambda_\nu}(q_t\mid c_t)=\kappa_t\ ((c_t)_*\Lambda_\nu)\text{-ae}]\land[\mathrm{iid}_\nu(y)\land(\forall t,y_t\in I\ {\rm ae})\Rightarrow\forall T,E_T(\Lambda_\nu,y,q)=D_T(q)\land E_T\ge0].
\]

1. **Objects:** History H_t, sampler f, kernels, recursive a/b/c/q, ν probability stream laws; Λν=undefined kernelGameLaw.
2. **Quantifiers/order:** κ/all Markov instances precede ∃f; f precedes every ν and T.
3. **Assumptions:** Markov kernels; loss identity additionally joint coordinate independence, identical coordinate law to time zero, AE support under ν.
4. **Conclusion/metric:** J=joint sampler measurability; K=∀t,h uniform-volume pushforward κ_t(h); B_m=∀t measurable b_t; A_c=∀t,u,y,i<t a_t(... )_i=q_i; P_c=∀t,ω,ω′ tape equality through t and observations before t implies q_t equality; plus displayed laws.
5. **Constants/indices/boundary:** All t/T, empty a0, q0 sampled from f0 with current tape coordinate; no numeric initial action; T0 excess zero.
6. **Information/probability:** Same f/actual prior actions everywhere; joint measure-kernel law differs from independence, conditional equality is history-law AE. Λν's probabilistic construction missing.
7. **Excluded scope:** Partial reconstruction: kernelGameLaw and its tape-law abbreviation are absent. Do not infer product/freshness from earlier history; no universal null set across ν.

### A004

Sublinear centered totals are equivalent to convergence of normalized centered totals.

\[
\forall a:\mathbb N\to\mathbb R,\ c\in\mathbb R,\ (a_T-Tc)=o(T)\ \Longleftrightarrow\ a_T/T-c\to0.
\]

1. **Objects:** Arbitrary real total sequence and fixed scalar c.
2. **Quantifiers/order:** total then c; varying natural T in both asymptotics.
3. **Assumptions:** No sign, regularity or probabilistic assumptions.
4. **Conclusion/metric:** Equivalence, not production of either limit.
5. **Constants/indices/boundary:** Real T; at T0 residual a0 and normalized centered value -c need not agree.
6. **Information/probability:** Deterministic magnitude little-o and ordinary real limit.
7. **Excluded scope:** Not a one-sided upper condition; c is fixed, not tuned with T.

### A005

Regret equals the sum of pointwise loss differences.

\[
\forall X,\ell,q,u,T,\ R_T(\ell,q,u)=\sum_{t<T}(\ell_t(q_t)-\ell_t(u)).
\]

1. **Objects:** Arbitrary action type, real losses, trace, comparator, horizon.
2. **Quantifiers/order:** X then loss,prediction,u,T.
3. **Assumptions:** Types only.
4. **Conclusion/metric:** Finite algebraic equality.
5. **Constants/indices/boundary:** T0 empty sums zero.
6. **Information/probability:** No stochastic or causal restriction on supplied trace.
7. **Excluded scope:** No feasibility or nonnegativity assertion.

### A006

Regret to any feasible constant is bounded above by feasible-best regret.

\[
\forall y,q,T,\ [\forall t<T,y_t\in I]\Rightarrow\forall u\in I,\ R_T^y(q,u)\le G_T(y,q).
\]

1. **Objects:** Real observations/predictions, feasible comparator and realized prefix.
2. **Quantifiers/order:** y,q,T,prefix bound,u,membership.
3. **Assumptions:** Only observations in scored prefix and comparator feasible; q unrestricted.
4. **Conclusion/metric:** One-sided comparison of signed metrics.
5. **Constants/indices/boundary:** T0 both zero; no positive-T premise.
6. **Information/probability:** Deterministic fixed comparator versus prefix infimum.
7. **Excluded scope:** No causality or feasibility requirement on predictions.

### A007

Completed-information measurable AE-bounded trace has the expected-excess identity.

\[
\forall\mathsf B,\mathsf D,\mathsf S,F,Q,\ [\forall t,F_t\le\mathcal G_t]\Rightarrow[\forall t,Q_t\text{ measurable on }\mathcal E_\mu(F_t)]\Rightarrow[\forall t,Q_t\in I\ {\rm ae}]\Rightarrow\forall T,\ E_T(Q)=D_T(Q)\land E_T(Q)\ge0.
\]

1. **Objects:** Probability process/seed, information structures and supplied real trace.
2. **Quantifiers/order:** Same order as A002, replacing its AESM premise by exact eventual-space measurability.
3. **Assumptions:** B,D,S, all-time F inclusions, completed-information measurability and AE bounds.
4. **Conclusion/metric:** Equality plus nonnegativity for original predictions.
5. **Constants/indices/boundary:** All T, zero included; mean m, exponent 2.
6. **Information/probability:** Ambient μ remains fixed, not a measure silently restricted to F; fixed expectation benchmark.
7. **Excluded scope:** No pointwise raw-F predictability or constructed-policy claim.

### A008

Completed-information prediction is independent of the current outcome.

\[
\forall\mu\ {\rm probability},Y,\ [\forall i,Y_i\text{ measurable}]\Rightarrow\mathsf D(Y)\Rightarrow\forall S,\mathsf S(S,Y)\Rightarrow\forall t,F\le\mathcal G_t,P,\ P\text{ measurable on }\mathcal E_\mu(F)\Rightarrow P\perp_\mu Y_t.
\]

1. **Objects:** Measurable Ω/Seed, process, seed, one t, F and real P.
2. **Quantifiers/order:** Spaces,μ,Y,measurability,independence,S/premises,t,F/inclusion,P/premise.
3. **Assumptions:** No common law, support or L2 assumption; completed-information measurability.
4. **Conclusion/metric:** Independence produced for original supplied P.
5. **Constants/indices/boundary:** t0 permits seed-only information.
6. **Information/probability:** Whole-vector seed independence plus joint target independence, not pairwise substitutes.
7. **Excluded scope:** No loss guarantee, bound, policy factorization or arbitrary side information.

### A009

The distribution mean is feasible and the constant oracle achieves zero expected fixed excess.

\[
\forall\mathsf B(\mu,Y)\ \forall T,\ m\in I\land E_T(\mu,Y,Q_t\equiv m)=0.
\]

1. **Objects:** Common-law outcome process and its constant mean predictor.
2. **Quantifiers/order:** Space,μ,Y,all-time measurability/common-law/AE-support,T.
3. **Assumptions:** B only; target independence absent.
4. **Conclusion/metric:** Feasible mean and zero excess.
5. **Constants/indices/boundary:** T0 included, no uniqueness.
6. **Information/probability:** Population mean may depend on unknown law; fixed across samples/time.
7. **Excluded scope:** Not an implementable unknown-law estimator claim.

### A010

The dyadic actual run has upper no-regret and vanishing best average but no fixed-zero ordinary regret limit.

\[
U(I,\ell_d,p(d))\land G_T(d,p)/T\to0\land\neg\exists a\in\mathbb R,\ R_T^d(0)/T\to a\land\neg L(I,\ell_d,p(d)).
\]

1. **Objects:** Fixed recursively defined d, actual p and two signed regret metrics.
2. **Quantifiers/order:** Closed conjunction; U expands comparator/ε/eventual T; third negates every real a for u0.
3. **Assumptions:** No external premises.
4. **Conclusion/metric:** Upper success and best-average convergence coexist with ordinary-limit obstruction.
5. **Constants/indices/boundary:** T0 normalized values zero; d_{n+1}=1-d_floor(n/2); comparator0 feasible.
6. **Information/probability:** Deterministic actual strict-past run.
7. **Excluded scope:** Not positive limiting regret, not failure of U, not nonconvergence for every comparator.

### A011

Finite squared loss decomposes around the empirical mean.

\[
\forall y,n>0,u\in\mathbb R,\ C_n(y,u)=C_n(y,e_n)+n(u-e_n)^2.
\]

1. **Objects:** Real y, positive prefix, real comparator.
2. **Quantifiers/order:** y,n,positivity,u.
3. **Assumptions:** n>0 only; y,u unrestricted.
4. **Conclusion/metric:** Exact additive variance-style decomposition.
5. **Constants/indices/boundary:** n coerced real; excludes zero although operations total.
6. **Information/probability:** Deterministic full-prefix mean.
7. **Excluded scope:** No feasible bound, stochastic variance or causality assertion.

### A012

A positive feasible prefix has a feasible empirical mean.

\[
\forall y,n>0,\ [\forall t<n,y_t\in I]\Rightarrow e_n(y)\in I.
\]

1. **Objects:** Real prefix and its mean.
2. **Quantifiers/order:** y,n,positivity,prefix support.
3. **Assumptions:** Only scored prefix bounded.
4. **Conclusion/metric:** Mean feasibility.
5. **Constants/indices/boundary:** Denominator n>0; explicit zero excluded.
6. **Information/probability:** Deterministic.
7. **Excluded scope:** No all-time bound or prediction statement.

### A013

The empirical mean minimizes squared loss over all real constants for positive prefixes.

\[
\forall y,n>0,u\in\mathbb R,\ C_n(y,e_n)\le C_n(y,u).
\]

1. **Objects:** Arbitrary real prefix and comparator.
2. **Quantifiers/order:** y,n,positivity,u.
3. **Assumptions:** No boundedness.
4. **Conclusion/metric:** Global real comparator minimality.
5. **Constants/indices/boundary:** Positive n, no zero case in type.
6. **Information/probability:** Hindsight prefix mean.
7. **Excluded scope:** Explicit candidate producer property, not supplied minimizing premise; no feasibility asserted.

### A014

Any comparator no worse than the empirical mean must equal it at a positive horizon.

\[
\forall y,n>0,u,\ C_n(y,u)\le C_n(y,e_n)\Rightarrow u=e_n.
\]

1. **Objects:** Real sequence, prefix and proposed comparator.
2. **Quantifiers/order:** y,n,positivity,u,loss comparison.
3. **Assumptions:** Supplied no-worse loss inequality and n>0.
4. **Conclusion/metric:** Equality/uniqueness characterization.
5. **Constants/indices/boundary:** At zero uniqueness would fail; excluded.
6. **Information/probability:** Deterministic comparator.
7. **Excluded scope:** Does not assume compact feasible set or prove general minimizer existence.

### A015

Positive-prefix empirical means have the stated incremental update.

\[
\forall y,t>0,\ e_{t+1}=e_t+(y_t-e_t)/(t+1).
\]

1. **Objects:** Sequence and adjacent means.
2. **Quantifiers/order:** y,t,positivity.
3. **Assumptions:** t>0, no bounds.
4. **Conclusion/metric:** Exact update equation.
5. **Constants/indices/boundary:** Denominator t+1; current y_t enters next mean.
6. **Information/probability:** Update after current target.
7. **Excluded scope:** t0 excluded by actual signature, even if a separate formula could extend.

### A016

The expected fixed benchmark equals horizon times common variance.

\[
\forall\mathsf B(\mu,Y)\ \forall T,\ B_T=Tv.
\]

1. **Objects:** Probability common-law process and outside-expectation infimum.
2. **Quantifiers/order:** Space,μ,Y,measurable/common-law/AE-support,T.
3. **Assumptions:** B; no independence.
4. **Conclusion/metric:** Exact benchmark value.
5. **Constants/indices/boundary:** T0 gives0, all natural T.
6. **Information/probability:** Optimization over fixed constants after integration.
7. **Excluded scope:** Not expectation of hindsight minimum, not uniqueness.

### A017

Expected loss of every real constant has the variance-plus-bias decomposition.

\[
\forall\mathsf B(\mu,Y)\ \forall T\ \forall u\in\mathbb R,\ \mathbb E\sum_{t<T}(u-Y_t)^2=Tv+T(u-m)^2.
\]

1. **Objects:** Common-law process and fixed comparator.
2. **Quantifiers/order:** B binders then T,u.
3. **Assumptions:** No independence or u∈I restriction.
4. **Conclusion/metric:** Exact expected-loss decomposition.
5. **Constants/indices/boundary:** Real factor T; T0 zero.
6. **Information/probability:** Same u across all samples/time.
7. **Excluded scope:** No policy or rate.

### A018

The mean is feasible and common-variance loss is an attained least expected value.

\[
\forall\mathsf B\ \forall T,\ m\in I\land\operatorname{IsLeast}(\{\mathbb E\sum_{t<T}(u-Y_t)^2:u\in I\},Tv).
\]

1. **Objects:** Expected-loss image set, mean, common variance.
2. **Quantifiers/order:** B binders then T; comparator quantifiers inside IsLeast.
3. **Assumptions:** No independence.
4. **Conclusion/metric:** IsLeast includes membership/existence of a feasible attaining comparator and lower bound against all feasible comparators.
5. **Constants/indices/boundary:** T0 all comparators tie at0.
6. **Information/probability:** Fixed comparator outside expectation.
7. **Excluded scope:** No unique minimizer; value-set membership is stronger than only an infimum equality.

### A019

The half-initialized general predictor is the mean predictor.

\[
\forall y,t,\ p^{1/2}_t(y)=p_t(y).
\]

1. **Objects:** Two explicit rule definitions.
2. **Quantifiers/order:** y,t.
3. **Assumptions:** None.
4. **Conclusion/metric:** Pointwise equality.
5. **Constants/indices/boundary:** t0 both half; later both empirical mean.
6. **Information/probability:** Same strict-past input.
7. **Excluded scope:** Not arbitrary initialization equality.

### A020

A feasible initial value and feasible strict past give a feasible general prediction.

\[
\forall a,y,t,\ a\in I\Rightarrow[\forall i<t,y_i\in I]\Rightarrow p^a_t(y)\in I.
\]

1. **Objects:** General initialization and real sequence.
2. **Quantifiers/order:** a,y,t,initial membership,prefix support.
3. **Assumptions:** Exactly initial and strict-past bounds.
4. **Conclusion/metric:** Prediction feasibility.
5. **Constants/indices/boundary:** t0 uses a; no current target bound.
6. **Information/probability:** Before-reveal prediction.
7. **Excluded scope:** Not all-time stream support or bound for arbitrary a.

### A021

General prediction depends only on strict past and the shared initialization.

\[
\forall a,y,z,t,\ [\forall i<t,y_i=z_i]\Rightarrow p^a_t(y)=p^a_t(z).
\]

1. **Objects:** Two streams, common real initialization.
2. **Quantifiers/order:** a,y,z,t,prefix equality.
3. **Assumptions:** No bounds; same a.
4. **Conclusion/metric:** Pointwise causal equality.
5. **Constants/indices/boundary:** t0 premise vacuous, both output a.
6. **Information/probability:** Current/future observations invisible.
7. **Excluded scope:** No claim for different initializations.

### A022

The actual recursive state equals time paired with the general predictor.

\[
\forall a,y,t,\ S^a_t(y)=(t,p^a_t(y)).
\]

1. **Objects:** Actual state recursion, count and prediction.
2. **Quantifiers/order:** a,y,t.
3. **Assumptions:** No bounds.
4. **Conclusion/metric:** Whole-pair invariant.
5. **Constants/indices/boundary:** t0 state(0,a); positive-time mean.
6. **Information/probability:** Current y_t not yet in state at t.
7. **Excluded scope:** Actual recurrence identity, not merely supplied trace correspondence.

### A023

After one update the initial value is replaced by the first observation.

\[
\forall a,y,\ S^a_1(y)=(1,y_0).
\]

1. **Objects:** Initial state and first update.
2. **Quantifiers/order:** a,y.
3. **Assumptions:** No feasibility.
4. **Conclusion/metric:** Exact first state.
5. **Constants/indices/boundary:** Count1; update denominator1.
6. **Information/probability:** After observing y0.
7. **Excluded scope:** Initial value arbitrary but this is only time1 assertion.

### A024

The half-initialized state exactly tracks the mean predictor.

\[
\forall y,t,\ S^{1/2}_t(y)=(t,p_t(y)).
\]

1. **Objects:** State and actual fixed-initial rule.
2. **Quantifiers/order:** y,t.
3. **Assumptions:** None.
4. **Conclusion/metric:** Whole state identity.
5. **Constants/indices/boundary:** t0(0,1/2), not (0,e0).
6. **Information/probability:** One actual recurrence.
7. **Excluded scope:** No alternative algorithm or initialization.

### A025

The mean component of a feasibly initialized state remains feasible over a feasible prefix.

\[
\forall a,y,t,\ a\in I\Rightarrow[\forall i<t,y_i\in I]\Rightarrow (S^a_t(y))_2\in I.
\]

1. **Objects:** State's real second component.
2. **Quantifiers/order:** a,y,t,initial support,prefix support.
3. **Assumptions:** Exactly supplied bounds.
4. **Conclusion/metric:** Second-component interval membership.
5. **Constants/indices/boundary:** t0 component a.
6. **Information/probability:** Actual prefix updates.
7. **Excluded scope:** Does not replace whole state by an arbitrary bounded trace.

### A026

The whole state is determined by strict past and shared initialization.

\[
\forall a,y,z,t,\ [\forall i<t,y_i=z_i]\Rightarrow S^a_t(y)=S^a_t(z).
\]

1. **Objects:** Two real streams and entire states.
2. **Quantifiers/order:** a,y,z,t,equal past.
3. **Assumptions:** No feasibility.
4. **Conclusion/metric:** Whole-pair equality.
5. **Constants/indices/boundary:** t0 same(0,a).
6. **Information/probability:** No current/future dependence.
7. **Excluded scope:** Stronger than only equal prediction components; no different-a claim.

### A027

Every feasible finite prefix, including empty, has a feasible empirical-mean minimizer on I.

\[
\forall y,T,\ [\forall t<T,y_t\in I]\Rightarrow e_T\in I\land\forall u\in I,\ C_T(y,e_T)\le C_T(y,u).
\]

1. **Objects:** Prefix, empirical mean, feasible competitors.
2. **Quantifiers/order:** y,T,prefix support; then conclusion all u∈I.
3. **Assumptions:** No positivity.
4. **Conclusion/metric:** Explicit candidate feasibility and minimizing property.
5. **Constants/indices/boundary:** T0 e0=0, all losses0, no uniqueness.
6. **Information/probability:** Hindsight prefix comparison.
7. **Excluded scope:** Not a supplied-minimizer premise, no stochastic expectation.

### A028

For an iid feasible process and legal-history policy, positive-horizon average loss minus variance equals average fixed excess.

\[
\forall\mathsf B,\mathsf D,\pi,\mathsf H(\pi),\ \forall T>0,\ A_T(Q)/T-v=E_T(Q)/T,\quad Q_t=\pi_t((Y_i)_{i<t}).
\]

1. **Objects:** Probability process, actual finite-history policy, expected metrics.
2. **Quantifiers/order:** B binders then independence,policy,measurability,conditional bound,T,positivity.
3. **Assumptions:** All-time B,D,H. Bound only if every history coordinate feasible.
4. **Conclusion/metric:** Exact normalization identity.
5. **Constants/indices/boundary:** Real T>0; at T0 left -v versus right0 in general.
6. **Information/probability:** Actual strict-past composition, no seed input.
7. **Excluded scope:** Not a rate or convergence claim; no global bound on infeasible tuples.

### A029

Supplied feasible prefix leaders satisfy the next-leader finite inequality.

\[
\forall X,V,\ell,L,T,\ [\forall 0<n\le T,L_n\in V]\Rightarrow[\forall 0<n\le T,\forall u\in V,\sum_{t<n}\ell_t(L_n)\le\sum_{t<n}\ell_t(u)]\Rightarrow\sum_{t<T}\ell_t(L_{t+1})\le\sum_{t<T}\ell_t(L_T).
\]

1. **Objects:** Arbitrary action type/set, losses, supplied leader sequence.
2. **Quantifiers/order:** X,V,loss,leader,T,membership,minimizing premises.
3. **Assumptions:** Positive-prefix minimizers supplied up to T; no convexity/compactness.
4. **Conclusion/metric:** Finite sum inequality.
5. **Constants/indices/boundary:** t+1 leader includes current loss t; T0 vacuous premises and0≤0.
6. **Information/probability:** Deterministic; not a before-reveal implementation.
7. **Excluded scope:** No existence construction for leaders, no uniqueness.

### A030

If each comparator regret ratio has a real limit, limit-no-regret and upper-no-regret are equivalent.

\[
\forall X,V,\ell,q,\ [\forall u\in V,\exists a\in\mathbb R,\ R_T(u)/T\to a]\Rightarrow[L(V,\ell,q)\leftrightarrow U(V,\ell,q)].
\]

1. **Objects:** Arbitrary action/loss/trace, feasible set and normalized regrets.
2. **Quantifiers/order:** X,V,loss,prediction,all-comparator convergence premise.
3. **Assumptions:** Ordinary limit existence for each feasible u, without a sign restriction in premise.
4. **Conclusion/metric:** Equivalence of the two predicates under this extra convergence hypothesis.
5. **Constants/indices/boundary:** T0 total quotient irrelevant; empty V both vacuous.
6. **Information/probability:** No stochastic or causal assumptions.
7. **Excluded scope:** Not unconditional equivalence; no common limit across u.

### A031

Ordinary-limit no-regret implies the eventual upper condition.

\[
\forall X,V,\ell,q,\ L(V,\ell,q)\Rightarrow U(V,\ell,q).
\]

1. **Objects:** Arbitrary action type, losses, trace and feasible set.
2. **Quantifiers/order:** X,V,loss,prediction,LimitNoRegret proof.
3. **Assumptions:** Comparatorwise finite nonpositive limits supplied.
4. **Conclusion/metric:** Upper condition produced.
5. **Constants/indices/boundary:** All natural T eventually; empty feasible set vacuous.
6. **Information/probability:** No probability or causality premise.
7. **Excluded scope:** No converse without added convergence, no uniform comparator threshold.

### A032

Every bounded stream has vanishing average best regret for the actual mean predictor.

\[
\forall y,\ [\forall t,y_t\in I]\Rightarrow G_T(y,p(y))/T\to0.
\]

1. **Objects:** Real stream, actual p, realized-prefix best metric.
2. **Quantifiers/order:** y,all-time bound,then limit over T.
3. **Assumptions:** Pointwise all-time support only.
4. **Conclusion/metric:** Ordinary convergence produced.
5. **Constants/indices/boundary:** T0 G0/0=0; no rate constant.
6. **Information/probability:** Deterministic, no mean-convergence assumption.
7. **Excluded scope:** Does not yield ordinary limits for each fixed comparator.

### A033

Mean prediction has the logarithmic finite best-regret upper bound.

\[
\forall y,T>0,\ [\forall t<T,y_t\in I]\Rightarrow G_T(y,p)\le4+4\log T.
\]

1. **Objects:** Bounded scored prefix, actual p, best regret.
2. **Quantifiers/order:** y,T,positivity,prefix bound.
3. **Assumptions:** No future bound.
4. **Conclusion/metric:** One-sided finite upper bound.
5. **Constants/indices/boundary:** Natural log of real T, not T+1; T1 bound4; T0 excluded.
6. **Information/probability:** Deterministic actual prediction.
7. **Excluded scope:** No absolute-value bound or expectation metric.

### A034

A sharper finite best-regret bound retains its harmonic sum.

\[
\forall y,T>0,\ [\forall t<T,y_t\in I]\Rightarrow G_T(y,p)\le\tfrac14+\sum_{t<T-1}\frac4{t+2}.
\]

1. **Objects:** Same actual predictor and finite metric.
2. **Quantifiers/order:** y,T,positivity,prefix support.
3. **Assumptions:** Only scored prefix bounded.
4. **Conclusion/metric:** Finite upper bound.
5. **Constants/indices/boundary:** T-1 is natural subtraction; denominators real t+2, from2 through T; T1 empty sum gives1/4.
6. **Information/probability:** Deterministic.
7. **Excluded scope:** Not sum starting denominator1 or extending through T+1; T0 excluded.

### A035

The actual mean predictor has zero normalized expected excess and little-o excess under iid bounded outcomes.

\[
\forall\mathsf B(\mu,Y),\ \mathsf D(Y)\Rightarrow [E_T(\mu,Y,Q)/T\to0]\land[E_T(\mu,Y,Q)=o(T)],\quad Q_t(\omega)=p_t(i\mapsto Y_i\omega).
\]

1. **Objects:** Probability common-law independent outcomes, actual mean prediction and expected-fixed excess.
2. **Quantifiers/order:** Space,μ,Y,measurable/common-law/AE-support,independence; T varies inside both conclusions.
3. **Assumptions:** B plus D; no seed/policy premise.
4. **Conclusion/metric:** Actual limit and little-o conjunction, not an equivalence-only criterion.
5. **Constants/indices/boundary:** Initial half, T0 ratio0; magnitude little-o versus real T.
6. **Information/probability:** Same concrete algorithm for all horizons; expectation not samplewise limit.
7. **Excluded scope:** No arbitrary-policy convergence guarantee or high-probability conclusion.

### A036

The first-round loss gap against the first-prefix mean is at most one quarter.

\[
\forall y,\ y_0\in I\Rightarrow(p_0-y_0)^2-(e_1-y_0)^2\le\tfrac14.
\]

1. **Objects:** First observation, initialized predictor and first mean.
2. **Quantifiers/order:** y,only y0 bound.
3. **Assumptions:** No other-time support.
4. **Conclusion/metric:** Signed one-step upper gap.
5. **Constants/indices/boundary:** p0=1/2, e1=y0; constant1/4.
6. **Information/probability:** Current observation used by comparison mean, not predictor.
7. **Excluded scope:** Not a sum or arbitrary-initialization result.

### A037

For feasible streams, ordinary-limit no-regret exactly characterizes empirical-mean convergence.

\[
\forall y,\ [\forall t,y_t\in I]\Rightarrow[L(I,\ell_y,p(y))\leftrightarrow\exists m\in I,\ e_T(y)\to m].
\]

1. **Objects:** Real stream, actual p, comparatorwise limits and mean.
2. **Quantifiers/order:** y,all-time support,then biconditional.
3. **Assumptions:** No mean convergence assumed separately.
4. **Conclusion/metric:** Equivalence; not universal existence of means.
5. **Constants/indices/boundary:** Finite ordinary limits, potentially negative comparator limits; T0 irrelevant.
6. **Information/probability:** Deterministic actual rule.
7. **Excluded scope:** Not equivalence with merely U or best-average convergence.

### A038

The fixed-initial mean prediction is feasible under a feasible strict past.

\[
\forall y,t,\ [\forall i<t,y_i\in I]\Rightarrow p_t(y)\in I.
\]

1. **Objects:** Real stream and actual p.
2. **Quantifiers/order:** y,t,prefix bound.
3. **Assumptions:** No current/future support.
4. **Conclusion/metric:** Feasibility of played value.
5. **Constants/indices/boundary:** t0 premise vacuous, output1/2.
6. **Information/probability:** Strict-past visibility.
7. **Excluded scope:** No assumption e0=1/2; actual empty mean remains0.

### A039

Every pointwise feasible stream satisfies upper no-regret for mean prediction.

\[
\forall y,\ [\forall t,y_t\in I]\Rightarrow U(I,\ell_y,p(y)).
\]

1. **Objects:** Actual deterministic squared-loss run and feasible comparators.
2. **Quantifiers/order:** y,all-time support; conclusion ∀u∈I,∀ε>0,eventually T.
3. **Assumptions:** No empirical-mean convergence or stochastic assumptions.
4. **Conclusion/metric:** One-sided eventual upper condition.
5. **Constants/indices/boundary:** Threshold may depend on u and ε; totalized T0 harmless.
6. **Information/probability:** Actual p before reveal.
7. **Excluded scope:** Not ordinary fixed-comparator convergence nor absolute sublinearity.

### A040

Mean prediction is determined by the strict observation prefix.

\[
\forall y,z,t,\ [\forall i<t,y_i=z_i]\Rightarrow p_t(y)=p_t(z).
\]

1. **Objects:** Two real streams and shared time.
2. **Quantifiers/order:** y,z,t,prefix equality.
3. **Assumptions:** No bounds.
4. **Conclusion/metric:** Pointwise causal equality.
5. **Constants/indices/boundary:** t0 vacuous, both half.
6. **Information/probability:** No current/future observations.
7. **Excluded scope:** Not equality of full streams or general initializations.

### A041

Actual mean prediction's gap against its final empirical mean has the harmonic upper bound.

\[
\forall y,T>0,\ [\forall t<T,y_t\in I]\Rightarrow\sum_{t<T}(p_t-y_t)^2-C_T(y,e_T)\le\tfrac14+\sum_{t<T-1}\frac4{t+2}.
\]

1. **Objects:** Actual cumulative loss and explicitly chosen horizon mean comparator.
2. **Quantifiers/order:** y,T,positivity,prefix support.
3. **Assumptions:** No future bound.
4. **Conclusion/metric:** Signed upper bound with actual comparator, no infimum in displayed conclusion.
5. **Constants/indices/boundary:** T1 bound1/4; denominator sequence2,...,T; T0 excluded.
6. **Information/probability:** Predictions strict-past, comparator hindsight prefix mean.
7. **Excluded scope:** Same number may equal best regret under premises, but metric not silently replaced.

### A042

A one-round gap to the current-inclusive mean is bounded by 4/(t+1).

\[
\forall y,t,\ [\forall i\le t,y_i\in I]\Rightarrow(p_t-y_t)^2-(e_{t+1}-y_t)^2\le4/(t+1).
\]

1. **Objects:** Current squared losses of predictor and updated mean.
2. **Quantifiers/order:** y,t,support through current index.
3. **Assumptions:** Includes current outcome bound, unlike strict-past-only feasibility.
4. **Conclusion/metric:** One-round signed upper gap.
5. **Constants/indices/boundary:** Denominator real t+1 never zero; t0 allowed with bound4.
6. **Information/probability:** Updated comparison mean includes y_t, prediction does not.
7. **Excluded scope:** No telescoping sum or sharp initial1/4 asserted here.

### A043

Scalar positive-horizon normalization distributes over the variance term.

\[
\forall a,v\in\mathbb R,\ \forall T>0,\ a/T-v=(a-Tv)/T.
\]

1. **Objects:** Two arbitrary real scalars and natural T.
2. **Quantifiers/order:** total,variance,T,positivity.
3. **Assumptions:** Only T>0; named variance not required nonnegative or statistical.
4. **Conclusion/metric:** Algebraic equality.
5. **Constants/indices/boundary:** T0 excluded: left -v versus right0.
6. **Information/probability:** No probability.
7. **Excluded scope:** No loss or convergence theorem by itself.

### A044

A measurable bounded-on-legal-history seeded policy has exact nonnegative expected fixed excess.

\[
\forall\mathsf B,\mathsf D,\mathsf S,\pi,\ \mathsf H_S(\pi)\Rightarrow\forall T,\ E_T(Q)=D_T(Q)\land E_T(Q)\ge0,\quad Q_t=\pi_t(S,(Y_i)_{i<t}).
\]

1. **Objects:** Probability process, whole-stream-independent seed, actual seeded policy.
2. **Quantifiers/order:** Spaces,μ,Y,measurable/common-law/AE-support/independence,S/premises,policy,measurability,conditional feasibility,T.
3. **Assumptions:** B,D,S and H_S; output bound every seed but only coordinatewise feasible histories.
4. **Conclusion/metric:** Identity and lower bound for actual composed Q.
5. **Constants/indices/boundary:** All T incl0; t0 policy may depend on seed, no forced half.
6. **Information/probability:** Actual finite strict history; original μ averages seed and outcomes; fixed benchmark outside expectation.
7. **Excluded scope:** No global output bound on infeasible tuples, arbitrary-policy rate or oracle mean access.

### A045

The actual measurable seeded strict-history prediction is independent of the current target.

\[
\forall\mu\ {\rm probability},Y,\ [\forall i,Y_i\text{ measurable}]\Rightarrow\mathsf D(Y)\Rightarrow\forall S,\mathsf S(S,Y)\Rightarrow\forall\pi,\ [\forall t,\pi_t\text{ measurable}]\Rightarrow\forall t,\ \pi_t(S,(Y_i)_{i<t})\perp_\mu Y_t.
\]

1. **Objects:** Arbitrary measurable Ω/Seed, independent process, seed, policy family.
2. **Quantifiers/order:** Spaces,μ,Y,measurability,independence,S/premises,policy,measurability,t.
3. **Assumptions:** No target common law/support, no policy bounds or L2.
4. **Conclusion/metric:** Derived independence of actual composition.
5. **Constants/indices/boundary:** All t, t0 seed-only output.
6. **Information/probability:** Joint target independence and seed independent of entire vector, not pairwise only.
7. **Excluded scope:** No generic supplied-independence consumer or numerical loss conclusion.

### A046

Conditional reading: one seeded policy has nonnegative expected excess and two success-condition equivalences.

\[
\forall\mathsf B,\mathsf D,\mathsf S,\pi,\mathsf H_S(\pi),\quad Q_t=\pi_t(S,(Y_i)_{i<t}):\quad [\forall T,E_T(Q)\ge0]\land[E_T(Q)=o(T)\leftrightarrow A_T(Q)/T-v\to0]\land[A_T(Q)/T-v\to0\leftrightarrow D_T(Q)/T\to0].
\]

1. **Objects:** Same probability/seed/policy objects as A044, let-bound actual Q and three asymptotic quantities.
2. **Quantifiers/order:** B,D,S,policy/measurability/conditional feasibility, then intended let-Q body. Exact supplied delimiter is missing.
3. **Assumptions:** Under intended parse: B,D,S,H_S; no convergence premise.
4. **Conclusion/metric:** One nonnegativity statement and two biconditionals, not universal production of convergence.
5. **Constants/indices/boundary:** At T0 E/T=D/T=0 while A/T-v=-v; limits ignore this discrepancy.
6. **Information/probability:** Same actual policy run across all T, expected fixed benchmark.
7. **Excluded scope:** Blocking transcription ambiguity for literal Lean scope: require explicit separator between Q value and conjunction. No automatic correction is treated as verified text.

### A047

On a feasible prefix, best regret equals regret to the empirical mean for any supplied trace.

\[
\forall y,q,T,\ [\forall t<T,y_t\in I]\Rightarrow G_T(y,q)=R_T^y(q,e_T).
\]

1. **Objects:** Arbitrary real prediction trace, feasible observation prefix and mean comparator.
2. **Quantifiers/order:** y,prediction,T,prefix support.
3. **Assumptions:** No q bound or causality, no T positivity.
4. **Conclusion/metric:** Exact metric adapter identity.
5. **Constants/indices/boundary:** T0 both0 with e0=0.
6. **Information/probability:** Realized prefix, no expectation.
7. **Excluded scope:** Does not identify arbitrary supplied trace with actual mean predictor.

### A048

The feasible squared-loss infimum is attained at the empirical mean, including the empty prefix.

\[
\forall y,T,\ [\forall t<T,y_t\in I]\Rightarrow\inf_{u\in I}C_T(y,u)=C_T(y,e_T).
\]

1. **Objects:** Finite loss image over I and explicit empirical mean.
2. **Quantifiers/order:** y,T,prefix support.
3. **Assumptions:** Only prefix bound, no positivity.
4. **Conclusion/metric:** Exact infimum value equality with specified candidate.
5. **Constants/indices/boundary:** T0 image{0}, mean0, all comparators tie.
6. **Information/probability:** Deterministic prefix optimization.
7. **Excluded scope:** No uniqueness at zero; no expectation/min interchange.

### A049

The actual prediction gap to the horizon mean obeys the logarithmic finite upper bound.

\[
\forall y,T>0,\ [\forall t<T,y_t\in I]\Rightarrow\sum_{t<T}(p_t-y_t)^2-C_T(y,e_T)\le4+4\log T.
\]

1. **Objects:** Actual p and empirical-mean comparator.
2. **Quantifiers/order:** y,T,positivity,prefix support.
3. **Assumptions:** Only scored prefix bounded.
4. **Conclusion/metric:** Signed upper gap, with no infimum in displayed expression.
5. **Constants/indices/boundary:** Natural log real T, T1 bound4, T0 excluded.
6. **Information/probability:** Same strict-past predictions; full-prefix comparison mean.
7. **Excluded scope:** No stochastic or absolute-regret statement.

### A050

A harmonic quantity is bounded by one plus the real logarithm of its natural index.

\[
\forall n\in\mathbb N,\quad \operatorname{harmonic}(n)\le1+\log n.
\]

1. **Objects:** Natural n and library harmonic symbol whose exact definition is absent.
2. **Quantifiers/order:** Universal n only.
3. **Assumptions:** No positivity hypothesis.
4. **Conclusion/metric:** Scalar upper bound; precise harmonic sum cannot be certified from supplied context.
5. **Constants/indices/boundary:** n0 is included; Real.log is totalized at0. If conventional H_n=∑_{j=1}^n1/j is intended, its zero value is0, but that indexing is conditional here.
6. **Information/probability:** No probability or algorithm.
7. **Excluded scope:** Missing exact harmonic definition/coercions: do not silently assert an n+1-indexed or rational/real implementation.

## Completion and required context

All 50 entries have individual prose, mathematical formulas and seven slots. A003 is necessarily partial concerning its measure family; A046 is an explicitly conditional parse rather than a silently repaired exact type; A050 retains an opaque harmonic symbol until its exact definition is supplied. Required additions: the actual kernelGameLaw definition and any kernelUniformTapeLaw abbreviation it uses; an unambiguous A046 let-body delimiter; the exact harmonic definition or scoped expansion if its indexing is to be audited. The missing game-law reference occurs in A003 in these actual inputs, not A004.

No source identities, mappings, fingerprints, reviewer verdicts or proof bodies were consulted. Hashes bind the supplied raw bytes, not normalized text. This report neither treats the 23 context definitions as new theorems nor interprets its 50 reconstructions as integration, proof, source or chapter acceptance.

