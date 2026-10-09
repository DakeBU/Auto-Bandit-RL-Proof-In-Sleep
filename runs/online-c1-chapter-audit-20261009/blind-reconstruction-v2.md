# Versioned neutral reconstruction v2

Actor `/root/osd_blind`; requested GPT-6 Astra / medium, without independent runtime model or effort attestation. This reused automated actor retains earlier staged decoder/project history. No absolute blindness, human review or external independence is claimed. Only the designated v2 packet/index, its three indexed inputs and this actor's v1 report/receipt were read. No source maps, fingerprints, intent, reviewer verdicts or proof bodies were consulted. This is a statement reconstruction, not proof, compilation or source/chapter acceptance.

This report incorporates the full prose, LaTeX and seven-slot entries of [v1](E:/ABRL/worktrees/research-online-book/runs/online-c1-chapter-audit-20261009/blind-reconstruction-v1.md), raw SHA256 `8d9e28ac228448bb8dd9e695dfe1c2eed4ca6421f22632b8c5188acf593bb186`, for the 47 entries explicitly listed below. The three complete replacement entries here supersede v1's A003, A046 and A050 and its unresolved-gap discussion. The v1 files remain intact as historical reports of the then-supplied inputs. v2's packet states that normalized signatures are unchanged; no separate old-target/source comparison or compilation was performed. Every current v2 target was read and compared semantically with its v1 reconstruction.

## Context completion

Retain all 23 exact v1 context definitions and mathematical abbreviations. The added definitions specify:
\[
\lambda=\operatorname{volume}_I,\qquad
\rho=\operatorname{kernelUniformTapeLaw}=\bigotimes_{j\in\mathbb N}\lambda,
\qquad
\Lambda_\nu=\operatorname{kernelGameLaw}(\nu)=\rho\otimes\nu.
\]
Here I is the unit-interval subtype, λ its uniform volume probability measure, and ν is a probability measure on real infinite streams. Thus the tape coordinates are independent uniforms; the entire tape is independent of the entire observation stream under the product. ν may have arbitrary temporal dependence for realization claims. This exogenous product model is not an action-responsive environment model.

The other added definition is exactly rational:
\[
H_n^{\mathbb Q}=\operatorname{harmonic}(n)=\sum_{i=0}^{n-1}\bigl((i+1):\mathbb Q\bigr)^{-1}.
\]
It has n summands, denominators 1 through n, and H0=0. In A050 the rational value is coerced into ℝ to compare to the real logarithm expression. None of these definitions is treated as an additional theorem target.

## Replacement A003 — one sampler, exact product law and the same actual recursion

Every natural-time family of Markov kernels from past action/observation histories to I has one jointly measurable uniform sampler family, chosen before all observation laws and horizons. Its actual recursive process has consistent finite prefixes and pointwise before-reveal dependence. For every observation-stream probability law, the joint history/action law and the corresponding almost-everywhere conditional law realize the kernels. If that observation law additionally has independent, identically distributed, a.s. feasible coordinates, the same process has exact nonnegative expected fixed-comparator excess.

Define \(H_t=I^{\operatorname{Fin}t}\times\mathbb R^{\operatorname{Fin}t}\) and \(\mathcal K=\prod_t(H_t\to I\to I)\). For f, let generated actions a, before-reveal policy b, generated history c and generated prediction q be exactly the recursions in the supplied context. In particular,
\[
a_0=(),\quad
a_{t+1}(f,u,y)=\operatorname{snoc}\bigl(a_t(f,u_{<t},y_{<t}),
f_t(a_t(f,u_{<t},y_{<t}),y_{<t})(u_t)\bigr),
\]
\[
b_t(f,u,z)=f_t(a_t(f,u_{<t},z),z)(u_t),\quad
c_t(f,(u,y))=(a_t(f,u_{<t},y_{<t}),y_{<t}),\quad q_t(f,(u,y))=b_t(f,u,y_{<t}).
\]
The complete conclusion is
\[
\begin{gathered}
\forall\kappa\in\prod_t\operatorname{Kernel}(H_t,I),\quad
[\forall t,\kappa_t\text{ Markov}]\Longrightarrow\exists f\in\mathcal K,\\
(\forall t,\operatorname{uncurry}(f_t)\text{ measurable})\ \land\
(\forall t\ \forall h\in H_t,(f_t(h))_*\lambda=\kappa_t(h))\ \land\
(\forall t,b_t(f,\cdot)\text{ measurable})\ \land\\
(\forall t,u\in I^{\mathbb N},y\in\mathbb R^{\mathbb N},i\in\operatorname{Fin}t,
a_t(f,u_{<t},y_{<t})_i=q_i(f,(u,y)))\ \land\\
(\forall t,\omega=(u,y),\omega'=(u',y'),
[\forall i\le t,u_i=u'_i]\Rightarrow[\forall i<t,y_i=y'_i]\Rightarrow q_t(f,\omega)=q_t(f,\omega'))\ \land\\
\forall\nu\in\operatorname{ProbabilityMeasure}(\mathbb R^{\mathbb N}),\\
[\forall t,(c_t,q_t)_*\Lambda_\nu=((c_t)_*\Lambda_\nu)\otimes_m\kappa_t]\ \land\\
[\forall t,\operatorname{condDistrib}_{\Lambda_\nu}(q_t\mid c_t)
=\kappa_t\quad((c_t)_*\Lambda_\nu)\text{-a.e.}]\ \land\\
\left[\operatorname{iIndepFun}_\nu(y\mapsto y_t)_{t\in\mathbb N}\Longrightarrow
(\forall t,\operatorname{IdentDistrib}_\nu(y_t,y_0))\Longrightarrow
(\forall t,y_t\in I\quad\nu\text{-a.e.})\Longrightarrow\forall T\in\mathbb N,\\
E_T(\Lambda_\nu,Y,Q)=\sum_{t<T}\int(Q_t-m_\nu)^2\,d\Lambda_\nu
\ \land\ 0\le E_T(\Lambda_\nu,Y,Q)\right],
\end{gathered}
\]
where \(Y_t(u,y)=y_t\), \(Q_t(u,y)=\operatorname{real}(q_t(f,(u,y)))\), \(m_\nu=\int Y_0\,d\Lambda_\nu\), and
\[
E_T(\mu,Y,Q)=\int\sum_{t<T}(Q_t-Y_t)^2\,d\mu-
\inf_{a\in[0,1]}\int\sum_{t<T}(a-Y_t)^2\,d\mu.
\]

1. **Objects/spaces:** finite unit-interval action histories and real observation histories, kernel family, one sampler family, one actual infinite prediction process, infinite iid uniform tape, arbitrary stream probability ν and product Λν.
2. **Quantifiers/order:** κ and all-time Markov instances precede ∃f. That same f precedes every ν, t and T. Deterministic measurability/consistency clauses are outside ∀ν. Inside ∀ν, both all-time law claims precede the conditional iid/support implication for all horizons. No law- or horizon-specific replacement sampler is allowed.
3. **Assumptions:** Markov kernels suffice for representation and all-law identities. Only the final loss clause additionally requires joint coordinate independence under ν, identical distributions to coordinate zero and per-time a.s. support in I. No iid assumption on arbitrary ν in the first law clauses, and no pointwise feasible-observation premise. Tape freshness and its independence from the whole stream come from the now-supplied product definitions, not an added hypothesis.
4. **Conclusion/metric:** sampler's uniform pushforward equals κ at every history; b is measurable; generated prefixes exactly match q; pointwise causality holds; joint measure factors via a measure-kernel composition; conditional kernels agree history-law-a.e.; under the extra ν premises, expected fixed excess equals a nonnegative squared-deviation sum. History/action dependence is retained by the kernel composition, not replaced by independent marginals.
5. **Constants/indices/degeneracies:** t uses tape coordinates through t and observation coordinates strictly before t. Initial history is empty; initial action is f0 at that history and u0, without a specified numeric value. Actions are feasible by type at all inputs. T0 has zero excess and an empty sum. No division by T or rate constant occurs. The fixed real comparator is shared by every time and sample.
6. **Information/probability:** actual prior generated actions feed the recursion. Same f and same path are used for finite prefixes, conditional laws and losses. The tape is independent of the entire exogenous stream, and its fresh uniform u_t drives the new action. Conditional-law equality is AE under the ν,t-dependent history pushforward; every-history sampler representation is a different, stronger pointwise scope. The infimum is outside expectation over both tape and stream, not an expected hindsight minimum.
7. **Excluded regimes:** no adaptive tape/action-dependent observation law, no single universal null-history set across all ν, no assertion of unique/computable sampler, no regret convergence or zero excess for arbitrary policies, and no proof/compilation evidence. The v1 measure-context ambiguity is resolved solely by the supplied addendum.

## Replacement A046 — result-level let and success-condition equivalences

The restored multiline declaration places the local `prediction` definition at result level. Its value is the function \(Q_t(\omega)=\pi_t(S\omega,(Y_i\omega)_{i<t})\); the following three-part proposition is the let body, not an extra argument to the real policy output. Newline/layout restores this scope. No semicolon or hypothesis is added by this reconstruction.

Universally quantify arbitrary Ω and Seed with measurable structures, a probability μ, real outcome family Y, its all-time measurability, same-law-to-Y0 and a.s. interval support, then joint family independence; next a measurable seed S independent of the entire infinite Y vector; then the time-indexed policy
\(\pi_t:\mathrm{Seed}\times\mathbb R^{J_t}\to\mathbb R\), its all-time measurability and its all-seed legal-history feasibility:
\[
\forall t,s,z,\quad(\forall i\in J_t,z_i\in I)\Rightarrow\pi_t(s,z)\in I.
\]
For the single let-defined Q, write \(m=\int Y_0\,d\mu\), \(v=\operatorname{Var}_\mu(Y_0)\),
\(A_T=\int\sum_{t<T}(Q_t-Y_t)^2\,d\mu\),
\(D_T=\sum_{t<T}\int(Q_t-m)^2\,d\mu\), and E_T as above. The complete result is
\[
(\forall T\in\mathbb N,\ 0\le E_T)
\ \land\ \left[(T\mapsto E_T)=o_{T\to\infty}(T)\ \Longleftrightarrow\ \lim_{T\to\infty}(A_T/T-v)=0\right]
\ \land\ \left[\lim_{T\to\infty}(A_T/T-v)=0\ \Longleftrightarrow\ \lim_{T\to\infty}D_T/T=0\right].
\]

1. **Objects/spaces:** arbitrary measurable probability space and measurable seed type, real iid a.s.-bounded process, whole-stream-independent seed, actual measurable seeded finite-history policy, one let-bound trace and three real asymptotic quantities.
2. **Quantifiers/order:** Ω/Seed structures, μ/probability, Y, measurable/common-law/support proofs, joint independence, S/measurability/whole-vector independence, policy/measurability/conditional feasibility; then the result-level let and conjunction. Natural T is bound in the first conjunct and separately inside each asymptotic function, not supplied before selecting a new prediction trace.
3. **Assumptions:** exact stated probability and independence premises. The policy bound covers every seed and every history whose coordinates all lie in I, not all arbitrary real tuples. Target support is only a.s. for each time. No convergence or sublinearity premise is supplied, and the local Q is defined rather than assumed as an independent variable.
4. **Conclusion/metric:** nonnegative finite excess and two biconditionals. The target does not assert that every such policy has sublinear excess or that either success limit holds. Little-o is a two-sided magnitude condition and both limits are ordinary real limits along natural horizons.
5. **Constants/indices/degeneracies:** mean and variance are those of Y0; all scored indices t<T; division uses real T. At T0, E0=D0=A0=0, so E0/0=D0/0=0 whereas A0/0-v=-v. This finite discrepancy does not affect the limit equivalences. At prediction time0 the seed can influence the feasible output; no half initialization is required.
6. **Information/probability:** all terms use exactly the same actual seeded strict-past Q and μ. Neither current/future outcomes nor a separate comparator are inputs to the policy. The benchmark minimizes one expected constant-comparator loss outside integration. Whole-vector seed independence is distinct from pairwise independence with each outcome.
7. **Excluded regimes:** no universal convergence claim, no expectation-of-hindsight benchmark, no all-real-history output bound, no random-kernel representation theorem here, and no proof/source acceptance. The v1 layout ambiguity is resolved by the exact multiline input; its conditional parse caveat is superseded.

## Replacement A050 — rational harmonic sum coerced to reals

For every natural n, the rational sum of reciprocals of 1 through n, embedded into ℝ, is bounded above by one plus the real logarithm of n:
\[
\forall n\in\mathbb N,\qquad
\left(\sum_{i=0}^{n-1}\bigl((i+1):\mathbb Q\bigr)^{-1}:\mathbb Q\right)_{\mathbb R}
\le 1+\log(n:\mathbb R).
\]
Equivalently, after the rational-to-real coercion, the left is \(\sum_{j=1}^{n}1/j\).

1. **Objects/spaces:** natural n, exact rational finite harmonic sum, its real coercion and the real logarithm. No observation sequence, learner or measure.
2. **Quantifiers/order:** one universal n only, without a positivity premise or existential constant.
3. **Assumptions:** none beyond n being natural. The exact rational definition is supplied by the addendum, so no conventional-indexing assumption is needed.
4. **Conclusion/metric:** a scalar real upper inequality with coefficient one and additive constant one; it is not an asymptotic equivalence or a regret statement by itself.
5. **Constants/indices/degeneracies:** exactly n summands, index i in range n and denominator i+1 in ℚ. n0 has empty rational sum0; Lean's totalized Real.log0=0 gives the stated bound0≤1. At n1 it reads1≤1. This is not a sum to n+1 or one with denominator zero.
6. **Information/probability:** purely deterministic arithmetic; ℚ-to-ℝ coercion occurs for the inequality, while the definition itself sums rational inverses.
7. **Excluded regimes:** no hidden n>0 restriction, no probability or algorithm claim, no compilation/proof verdict. The v1 harmonic-context gap is resolved.

## All-fifty reconciliation

The following entries inherit their complete prose/LaTeX/seven slots from v1 after checking the current multiline signature. Each row records its scope check. The new tape-law definitions and harmonic definition do not change their assumptions, metrics or conclusions; A046's restored result-level layout affects no other binder.

| Target | v2 disposition and semantic check |
|---|---|
| A001 | Retained: fixed binary witness chosen before seed integration, global all-history bound, T>0. |
| A002 | Retained: supplied AE-strongly-information-measurable trace, same ambient μ, exact expected excess. |
| A003 | Replaced above: tape/product law now fully interpreted. |
| A004 | Retained: arbitrary centered total little-o iff ordinary normalized limit; no kernel-law reference. |
| A005 | Retained: finite regret as sum of differences, arbitrary supplied trace. |
| A006 | Retained: feasible fixed comparator bounded by realized best regret; prediction unrestricted. |
| A007 | Retained: eventual-information measurability and a.s. trace bounds. |
| A008 | Retained: completed-information prediction independence; no support/common-law assumption. |
| A009 | Retained: distribution-mean oracle has zero fixed expected excess; no independence requirement. |
| A010 | Retained: four-part dyadic obstruction distinguishes upper and ordinary-limit conditions. |
| A011 | Retained: positive-prefix squared-loss decomposition, unrestricted real comparator. |
| A012 | Retained: positive feasible prefix gives feasible mean. |
| A013 | Retained: positive-prefix empirical mean minimizes over all reals. |
| A014 | Retained: supplied no-worse comparator is uniquely the mean, n>0. |
| A015 | Retained: update uses y_t and denominator t+1, with explicit t>0. |
| A016 | Retained: outside-expectation fixed minimum Tv; independence absent. |
| A017 | Retained: all-real fixed-comparator expected bias/variance identity. |
| A018 | Retained: IsLeast includes attainment in the image and the lower-bound property; T0 ties. |
| A019 | Retained: half initialization gives identical predictor. |
| A020 | Retained: general feasible initialization and strict-past feasibility. |
| A021 | Retained: same initialization plus equal strict past yields equal predictions. |
| A022 | Retained: whole actual state equals time paired with general predictor. |
| A023 | Retained: first update produces (1,y0), regardless of initialization. |
| A024 | Retained: half-initialized state equals time paired with meanPredict. |
| A025 | Retained: second state component feasible under initial/prefix bounds. |
| A026 | Retained: whole-state strict-past causal equality. |
| A027 | Retained: empty-inclusive feasible empirical-mean minimizing candidate. |
| A028 | Retained: positive-horizon normalization for actual legal-history policy, conditional output bound. |
| A029 | Retained: supplied prefix leaders, not existence construction; next-prefix leader includes current loss. |
| A030 | Retained: equivalence of upper/ordinary notions needs supplied comparatorwise real convergence. |
| A031 | Retained: ordinary nonpositive-limit no-regret implies upper condition. |
| A032 | Retained: actual mean predictor has vanishing realized-best average for every bounded stream. |
| A033 | Retained: positive-horizon best-regret upper bound 4+4 log T. |
| A034 | Retained: 1/4 plus explicit sum of 4/(t+2) for t<T-1; no opaque harmonic term. |
| A035 | Retained: actual iid mean predictor's expected excess converges normalized to zero and is little-o. |
| A036 | Retained: first-round gap ≤1/4 using only y0 feasibility. |
| A037 | Retained: ordinary-limit no-regret iff feasible empirical-mean convergence. |
| A038 | Retained: actual prediction feasible from strict-past support, t0 output half. |
| A039 | Retained: bounded stream yields only the stated eventual upper condition. |
| A040 | Retained: strict-past equality gives same meanPredict output. |
| A041 | Retained: explicit gap to final mean with the same finite reciprocal sum. |
| A042 | Retained: current-inclusive support gives one-step gap ≤4/(t+1), t0 allowed. |
| A043 | Retained: scalar normalization requires T>0, arbitrary real variance-named parameter. |
| A044 | Retained: actual seeded legal-history policy, exact expected excess/nonnegativity. |
| A045 | Retained: actual seeded policy independence produced without common-law/boundedness premises. |
| A046 | Replaced above: exact result-level let scopes the conjunction. |
| A047 | Retained: realized best regret equals empirical-mean comparator regret for any supplied trace. |
| A048 | Retained: feasible-prefix infimum equals empirical-mean loss, including T0. |
| A049 | Retained: explicit final-mean gap ≤4+4 log T, T>0. |
| A050 | Replaced above: exact rational n-term harmonic sum, real coercion and n0 boundary. |

All fifty targets therefore have complete statement reconstructions: 47 incorporated unchanged seven-slot entries and three complete seven-slot replacements. The original 23 definitions plus the three exact additions supply the context used here. No remaining blocking semantic ambiguity or missing context was identified for these fifty supplied statements. This conclusion concerns reconstruction completeness only. It does not certify proof terms, compilation, unchanged public-source fingerprints, literature fidelity or chapter acceptance.
