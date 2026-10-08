# Statement-only neutral reconstruction

Actor `/root/osd_blind`; requested GPT-6 Astra / medium, without independently attested runtime model or effort. This reused automated role retains earlier staged neutral-decoder/project history. No absolute historical blindness, human review or external independence is claimed. Only the designated input manifest and its two exact listed inputs were read. Declaration/import names present in those inputs were visible but not investigated. This report reconstructs four complete target types; no proof, native check, source identification or acceptance assessment was performed.

## Exact context and notation

For the ambient measurable space \((\Omega,\mathcal M)\) and measure μ, define
\[
\mathcal E_\mu(\mathcal F)=\{A\subseteq\Omega:\exists B\in\mathcal F,\ \mathbf1_A=\mathbf1_B\ \mu\text{-a.e.}\}.
\]
This is the supplied `eventuallyMeasurableSpace F (ae μ)`: sets equal modulo the ambient μ-a.e. filter to F-measurable sets. The measure remains on its given ambient sigma field; no measure restricted to F or on this enlarged structure is substituted. In particular, \(P\) measurable for \(\mathcal E_\mu(\mathcal F)\) is not a premise of pointwise F-measurability or necessarily ambient measurability. No assumption \(\mathcal F\le\mathcal M\), probability normalization, or ambient completeness is hidden in the definition of this notation.

Let \(I=[0,1]\), \(J_t=\{i\in\mathbb N:i<t\}\), \(H_t(\omega)=(Y_i(\omega))_{i\in J_t}\), and \(V(\omega)=(Y_i(\omega))_{i\in\mathbb N}\). Write
\[
\mathcal G_t=\operatorname{comap}_{\omega\mapsto(S(\omega),H_t(\omega))}
\mathcal M_{\mathrm{Seed}\times\mathbb R^{J_t}}.
\]
The product and finite function-space measurable structures are those of the supplied context. This exact seed-and-strict-past comap is distinct from \(\mathcal E_\mu(\mathcal F_t)\). At t0 the history is empty, so \(\mathcal G_0\) carries only seed information, which need not be trivial. Ω and Seed range over their arbitrary universes and measurable structures; no standard-Borel or countability restriction on those types is imposed.

For fixed-comparator loss, set
\[
M_T=\inf\left\{\int\sum_{t<T}(a-Y_t(\omega))^2\,d\mu(\omega):a\in I\right\},\qquad
R_T(P)=\int\sum_{t<T}(P_t(\omega)-Y_t(\omega))^2\,d\mu(\omega)-M_T.
\]
These are precisely the supplied `expectedFixedMinimum` and `expectedFixedRegret`. The real `sInf` operates on the image of I after integration: a single fixed comparator a is shared by every sample and time. This is not the expectation of a samplewise hindsight minimum. The definition alone supplies no attaining minimizer or uniqueness and no justification for interchanging infimum and integral. Real integrals are totalized. At T0 the sums vanish, the comparator image is {0}, and M0=R0=0.

Below C1–C4 label the four target headers in their supplied order; they are report labels, not additional declarations.

## C1 — existence of an F-measurable real version

For any ambient measure, every real function measurable in the specified eventually-measurable enlargement of F has a genuinely F-measurable version equal to it almost everywhere:
\[
\forall\Omega:\mathrm{Type}\ u\ [\mathcal M],\quad
\forall\mu:\operatorname{Measure}(\Omega),\ \mathcal F:\operatorname{MeasurableSpace}(\Omega),\ P:\Omega\to\mathbb R,
\quad P\text{ measurable on }\mathcal E_\mu(\mathcal F)\Longrightarrow
\exists Q:\Omega\to\mathbb R,\quad
Q\text{ measurable on }\mathcal F\ \land\ P=Q\ \mu\text{-a.e.}
\]

1. **Objects/spaces:** arbitrary ambient measurable Ω, measure μ, another measurable structure F on the same Ω, supplied real P and existential real version Q.
2. **Quantifiers/order:** Ω and ambient structure, μ, F, P, the completed-information measurability premise, then existence of one version with two conjuncts. The version may depend on all preceding data.
3. **Assumptions:** only the displayed types and measurability of P from \(\mathcal E_\mu(F)\) into the usual real measurable space. μ need not be finite, sigma-finite or a probability measure. No inclusion of F in the ambient structure, bound on P, integrability or seed data is assumed.
4. **Conclusion/metric:** an F-measurable function Q and equality P=Q in the ambient `ae μ` filter. This is an existence assertion, not a supplied-version assumption.
5. **Constants/indices/zero:** no numerical constants, time or horizon; the codomain is specifically the reals. Zero measure is not excluded; equality remains an a.e. rather than pointwise condition.
6. **Probability/information:** the conclusion moves measurability to the exact smaller F while permitting null-set changes to P. μ and its ambient sigma field remain unchanged throughout.
7. **Boundaries:** neither uniqueness nor pointwise equality is asserted. No general arbitrary-codomain version theorem, constructive program, independence or loss claim is part of this header. The report does not turn the header into a proof.

## C2 — globally bounded seed-history policy representation

If predictions are measurable in the eventual enlargements of information spaces contained in seed and strict past, and each prediction is almost surely feasible, one globally bounded measurable policy family represents all predictions simultaneously outside one null set:
\[
\begin{gathered}
\forall\Omega:\mathrm{Type}\ u,\mathrm{Seed}:\mathrm{Type}\ v\ [\mathcal M,\mathcal M_{\mathrm{Seed}}],\quad
\forall\mu:\operatorname{Measure}(\Omega),Y:\mathbb N\to\Omega\to\mathbb R,S:\Omega\to\mathrm{Seed},\\
\forall\mathcal F:\mathbb N\to\operatorname{MeasurableSpace}(\Omega),\quad
[\forall t,\mathcal F_t\le\mathcal G_t]\Longrightarrow
\forall P:\mathbb N\to\Omega\to\mathbb R,\\
[\forall t,P_t\text{ measurable on }\mathcal E_\mu(\mathcal F_t)]\Longrightarrow
[\forall t,P_t\in I\ \mu\text{-a.e.}]\Longrightarrow\\
\exists\pi:\prod_{t\in\mathbb N}(\mathrm{Seed}\times\mathbb R^{J_t}\to\mathbb R),\quad
(\forall t,\pi_t\text{ measurable})\ \land\
(\forall t\ \forall q\in\mathrm{Seed}\times\mathbb R^{J_t},\pi_t(q)\in I)\ \land\\
[\mu\text{-a.e. }\omega,\ \forall t\in\mathbb N,\ P_t(\omega)=\pi_t(S(\omega),H_t(\omega))].
\end{gathered}
\]

1. **Objects/spaces:** arbitrary ambient measure, seed type, outcome and seed maps, sequence of information structures F, supplied prediction trace and existential policy family on finite seed-history products.
2. **Quantifiers/order:** Ω/Seed structures, μ, Y, S, F, all-time inclusion, P, all-time enlarged-space measurability, all-time a.e. feasibility, then a single existential family π. The concluding order is a.e. ω followed by every natural t, not policies chosen separately for individual samples.
3. **Assumptions:** exactly those in the formula. There is no probability-measure requirement, measurability requirement on S or Y, outcome support restriction, independence or identical-law assumption. F need not be monotone. P is required measurable in the explicit \(\mathcal E_\mu(F_t)\), not pointwise measurable in F_t.
4. **Conclusion/metric:** three simultaneous properties: measurable policy at each time, globally I-valued output at every time/input, and equality to the original predictions at all times on a single common full-measure set. The policy is produced existentially; it is not supplied as a premise.
5. **Constants/indices/empty prefix:** bounds 0 and 1, strict history i<t. At time zero π0 can depend on the seed only; no 1/2 initial output is required. Natural times are countable, and simultaneous all-time equality is explicitly in the conclusion. There is no finite horizon parameter.
6. **Probability/information:** the all-input bound covers all seeds and every real history, including infeasible or never-realized histories. It is stronger than the prediction premise, which is only a.e. for each t. Null exceptions may separate P from its causal policy representation. No current/future target coordinate is an input to πt.
7. **Boundaries:** no pointwise-for-every-sample agreement, unique policy, kernel representation, integrability, independent prediction or regret claim. Neither existence of a restricted measure on F_t nor identity with a conventional completed filtration is added. The entire μ and eventual-space convention is the one supplied.

## C3 — independence of a completed-information prediction

For a measurable jointly independent outcome sequence and a measurable seed independent of its entire infinite stream, any real P measurable in the eventual enlargement of a subspace of seed-and-strict-past information is independent of the current target:
\[
\begin{gathered}
\forall\Omega,\mathrm{Seed}\ [\mathcal M,\mathcal M_{\mathrm{Seed}}],\quad
\forall\mu\ [\operatorname{IsProbabilityMeasure}(\mu)],\quad
\forall Y:\mathbb N\to\Omega\to\mathbb R,\\
[\forall i,Y_i\text{ measurable}]\Longrightarrow\operatorname{iIndepFun}_\mu(Y)\Longrightarrow
\forall S:\Omega\to\mathrm{Seed},\quad S\text{ measurable}\Longrightarrow S\perp_\mu V\Longrightarrow\\
\forall t\in\mathbb N\ \forall\mathcal F:\operatorname{MeasurableSpace}(\Omega),\quad
\mathcal F\le\mathcal G_t\Longrightarrow\forall P:\Omega\to\mathbb R,\quad
P\text{ measurable on }\mathcal E_\mu(\mathcal F)\Longrightarrow P\perp_\mu Y_t.
\end{gathered}
\]

1. **Objects/spaces:** arbitrary-universe measurable probability space and seed type; real outcome process; measurable seed; fixed time, information structure and supplied real prediction.
2. **Quantifiers/order:** Ω/Seed structures, μ/probability, Y, coordinate measurability, family independence, S, seed measurability and whole-stream independence, t, F/inclusion, P/enlarged-space measurability, then independence conclusion.
3. **Assumptions:** probability normalization and all preceding independence/measurability premises. No boundedness or L2 requirement on P, no common distribution or boundedness of outcomes. Family independence is joint `iIndepFun`; the seed is independent of V as one whole random element, not merely pairwise independent of each target.
4. **Conclusion/metric:** independence of the original supplied P from Yt. This produces independence from an information restriction; it does not assume it for P or limit its conclusion to a version Q.
5. **Constants/indices/empty prefix:** every natural t, strict-past range t; t0 allows a completed-seed-information prediction. No fixed initial value, finite horizon or numerical bound.
6. **Probability/information:** measurable P is interpreted for \(\mathcal E_\mu(F)\), using ambient μ. The current target is excluded from the raw seed-history map. Seed independence covers the whole infinite stream including its future, while P may differ on null sets from a raw-information representative.
7. **Boundaries:** this does not assert feasibility, square-loss bounds, representation of arbitrary randomized kernels, independence of arbitrary extra side information, or equivalence between pairwise and whole-vector seed independence. No completed-filtration identity beyond the specified eventual-space construction is asserted.

## C4 — expected fixed-comparator excess under completed predictability

Under independent identically distributed measurable outcomes with a.s. I support, an independent private seed, and an a.s. feasible trace measurable in the specified eventual information enlargements, finite expected fixed-comparator excess equals cumulative mean-square deviation from the population mean and is nonnegative.

Writing \(m=\int Y_0\,d\mu\), the full scope is
\[
\begin{gathered}
\forall\Omega,\mathrm{Seed}\ [\mathcal M,\mathcal M_{\mathrm{Seed}}],\quad
\forall\mu\ [\operatorname{IsProbabilityMeasure}(\mu)],\quad
\forall Y:\mathbb N\to\Omega\to\mathbb R,\\
[\forall i,Y_i\text{ measurable}]\Longrightarrow
[\forall i,\operatorname{IdentDistrib}(Y_i,Y_0;\mu,\mu)]\Longrightarrow
[\forall i,Y_i\in I\ \mu\text{-a.e.}]\Longrightarrow\operatorname{iIndepFun}_\mu(Y)\Longrightarrow\\
\forall S:\Omega\to\mathrm{Seed},\quad S\text{ measurable}\Longrightarrow S\perp_\mu V\Longrightarrow
\forall\mathcal F:\mathbb N\to\operatorname{MeasurableSpace}(\Omega),\quad
[\forall t,\mathcal F_t\le\mathcal G_t]\Longrightarrow\\
\forall P:\mathbb N\to\Omega\to\mathbb R,\quad
[\forall t,P_t\text{ measurable on }\mathcal E_\mu(\mathcal F_t)]\Longrightarrow
[\forall t,P_t\in I\ \mu\text{-a.e.}]\Longrightarrow\forall T\in\mathbb N,\\
R_T(P)=\sum_{t<T}\int(P_t(\omega)-m)^2\,d\mu(\omega)
\quad\land\quad 0\le R_T(P).
\end{gathered}
\]

1. **Objects/spaces:** arbitrary-universe ambient probability and seed spaces, common-law independent targets, independent seed, sub-information sequence, completed-information measurable supplied prediction sequence, finite horizon and fixed benchmark/excess.
2. **Quantifiers/order:** Ω/Seed structures, μ/probability, Y, all-time measurability, identical laws, a.s. support, family independence, S/measurability/whole-vector independence, F/inclusions, P/enlarged-space measurability/a.s. bounds, then T. One trace is fixed before T; no per-horizon replacement trace appears.
3. **Assumptions:** all listed stochastic premises separately. Both outcome and prediction feasibility are only a.e. for each time. Identical law does not imply independence; both are required. F is not required monotone, and no all-input policy bound is a premise because P is directly supplied.
4. **Conclusion/metric:** exact equality and nonnegativity for the original P and outside-integral fixed-comparator benchmark. This is expected signed excess, not pathwise hindsight regret or an absolute-value error. No minimizer is constructed by this statement.
5. **Constants/indices/empty prefix:** squared deviations, population mean of Y0, bounds [0,1], finite t<T sum. Every T including zero is permitted; at zero excess and deviation sum are both zero. There is no division by T, positive-horizon restriction or rate constant.
6. **Probability/information:** all expectations use ambient μ and include its seed randomness. P is measurable in \(\mathcal E_\mu(F_t)\), so a.e. representation by raw information is distinct from pointwise raw causality of P. The seed is independent of the entire stream and available at the start; no extra correlated information is included.
7. **Boundaries:** no convergence, little-o, high-probability claim, samplewise nonnegativity, unknown-law oracle implementation, unique optimizer or universal kernel representation. Unlike C1/C2 this target needs a probability measure and independence; unlike C3 it also imposes common law and a.s. boundedness.

## Ambiguity and assessment boundary

No blocking ambiguity was found in the provided context and four types. The exact eventual measurable structure is defined relative to the ambient ae filter, and no restricted/completed measure is silently substituted. The version and policy conclusions are existential, while the independence and excess conclusions concern the original supplied predictions. Global policy bounds in C2 and a.e. trace bounds in its premise and in C4 are distinct. This is a four-target mathematical reconstruction only; source fidelity, proofs, compilation, acceptance and program completion remain unassessed.
