# Neutral draft reconstruction

Actor `/root/osd_blind`. Requested GPT-6 Astra / medium; runtime model and effort are not independently attested. This reused automated actor has earlier staged decoder/project history. No absolute blindness, external independence or human review is claimed. Only the two designated neutral files were read; no other package files, source or old verdict were inspected. The supplied text contains definitions and proposed theorem headers without proofs. This report interprets their types and does not establish elaboration, existence, proof correctness or source acceptance.

## Complete operational and probabilistic context

Here I is the unit-interval subtype, so actions and tape entries lie in [0,1] by type. Let
\[
H_t=I^{\operatorname{Fin}t}\times\mathbb R^{\operatorname{Fin}t},\qquad
F=\prod_{t\in\mathbb N}(H_t\to I\to I).
\]
A history includes both previously generated actions and strictly earlier real observations. An f in F alone is not assumed measurable. Its joint-measurability condition is measurability of \((h,z)\mapsto f_t(h)(z)\), not merely separate measurability in h and z.

For finite tape prefix u and observation prefix y of length t, A is exactly this recursion:
\[
A_0(f,u,y)=(),\qquad
A_{t+1}(f,u,y)=\operatorname{snoc}\left(a,
f_t\bigl(a,y_{<t}\bigr)(u_t)\right),\quad
a=A_t(f,u_{<t},y_{<t}).
\]
The recursive call restricts both finite vectors by `castSucc`; the newly sampled action uses the last tape coordinate `Fin.last t`. The current observation y_t is not used to sample that action. This appends an action to the actual generated prefix, rather than substituting an arbitrary action-history input.

For an infinite tape u and exactly t past observations y,
\[
B_t(f,u,y)=f_t(A_t(f,u_{<t},y),y)(u_t).
\]
On the common infinite sample space \(\mathcal W=I^{\mathbb N}\times\mathbb R^{\mathbb N}\), write ω=(u,y). Then
\[
C_t(f,\omega)=(A_t(f,u_{<t},y_{<t}),y_{<t}),\qquad
P_t(f,\omega)=B_t(f,u,y_{<t}).
\]
Thus P is one infinite prediction process, not one fresh algorithm for each horizon. At t0, A is the empty vector, C is the unique empty history, and \(P_0=f_0((),())(u_0)\); there is no fixed initial action such as one half.

Let λ be volume on I, the uniform probability measure on the unit interval, and
\[
R=\bigotimes_{i\in\mathbb N}\lambda,\qquad M_\nu=R\otimes\nu,
\quad\nu\in\operatorname{ProbabilityMeasure}(\mathbb R^{\mathbb N}).
\]
The tape has independent uniform coordinates and is independent of the whole observation stream. ν may have arbitrary dependence across its own time coordinates unless further premises are explicitly given. In particular, this product model does not let observations respond to the generated tape/actions; arbitrary temporal dependence in an exogenous stream is different from an adaptive action-dependent observation mechanism.

For any ambient measure μ and real outcome/prediction sequences Y,Q, the literal benchmark definitions are
\[
b(\mu,Y,T)=\inf\left\{\int\sum_{t<T}(a-Y_t(\omega))^2\,d\mu(\omega):a\in[0,1]\right\},
\]
\[
r(\mu,Y,Q,T)=\int\sum_{t<T}(Q_t(\omega)-Y_t(\omega))^2\,d\mu(\omega)-b(\mu,Y,T).
\]
The infimum is the real `sInf` of the expected-loss image of the feasible interval: expectation is evaluated for one fixed real comparator before minimization. It is not expectation of a samplewise hindsight minimum. The set is not a finite candidate list; the definition itself asserts neither attainment nor uniqueness. The bare integrals and real infimum are totalized expressions. At T0, the empty sums and image {0} give b=r=0. No normalization by T appears in these definitions.

## q1 — universal sampler family for the given kernels

For any time-indexed family of Markov kernels from histories H_t to actions I, there exists a single jointly measurable sampler family whose pushforward of a uniform draw equals the given kernel at every history:
\[
\forall\kappa\in\prod_t\operatorname{Kernel}(H_t,I),\quad
[\forall t,\kappa_t\text{ is Markov}]\Longrightarrow
\exists f\in F,\quad
[\forall t,(h,z)\mapsto f_t(h)(z)\text{ measurable}]\ \land\
[\forall t\ \forall h\in H_t,(f_t(h))_*\lambda=\kappa_t(h)].
\]

1. **Objects/spaces:** natural-time history spaces, unit-interval action and sampling space, Markov kernel family and existential sampler f.
2. **Quantifiers/order:** κ and its all-time Markov instances first, then one f, then all-time measurability and all-time/all-history pushforward equalities. No observation law ν or horizon is an argument to this selection.
3. **Assumptions:** κ consists of kernels (including their kernel measurability) and is Markov at every time. No support restriction is needed beyond the codomain I; observations in histories remain arbitrary reals.
4. **Conclusion/metric:** existence of a jointly measurable uniform sampler representing each kernel as an exact equality of action measures for every h, not merely almost every reachable h.
5. **Constants/indices/initialization:** every natural time, uniform volume on [0,1]; at t0 the empty history still has a kernel and a sampler. No fixed initial action or finite terminal horizon.
6. **Probability/information:** this is a per-history sampling-law representation; it does not yet assert the law of the recursively generated process. The sampler can depend on the action/observation history but has no current observation input.
7. **Boundaries:** no unique or computable sampler is asserted. One uniform coordinate per call is the representation's sampling input; the statement is not supplied proof of its existence and is not a source-fidelity claim.

## q2 — measurable before-reveal rule and actual recursion consistency

Every jointly measurable sampler f gives measurable B rules. Its recursively generated finite action prefix agrees with the corresponding values of its one infinite prediction process, and the current prediction depends only on the tape through the current coordinate and observations strictly before the current time:
\[
\begin{gathered}
\forall f\in F,\quad [\forall t,\operatorname{uncurry}(f_t)\text{ measurable}]\Longrightarrow\\
(\forall t,B_t(f,\cdot)\text{ measurable})\ \land\\
\left[\forall t\ \forall u\in I^{\mathbb N}\ \forall y\in\mathbb R^{\mathbb N}\ \forall i\in\operatorname{Fin}t,
A_t(f,u_{<t},y_{<t})_i=P_i(f,(u,y))\right]\ \land\\
\left[\forall t\ \forall\omega=(u,y),\omega'=(u',y')\in\mathcal W,
(\forall i\le t,u_i=u'_i)\Rightarrow
(\forall i<t,y_i=y'_i)\Rightarrow P_t(f,\omega)=P_t(f,\omega')\right].
\end{gathered}
\]

1. **Objects/spaces:** a supplied jointly measurable sampler f, finite recursion A, before-reveal policy B, and actual infinite process P on the whole tape/observation space.
2. **Quantifiers/order:** f then its all-time joint measurability proof; conclusion is the three conjuncts above. Prefix consistency quantifies t, u, y, i in that order. Causality quantifies t, ω, ω′ before both matching-prefix premises.
3. **Assumptions:** only the given sampler's measurability; no kernel, Markov premise, probability measure, independence, legal observation support or common law.
4. **Conclusion/metric:** B measurability, pointwise equality of every entry of generated prefixes to the same P, and pointwise current-output invariance under changes outside the permitted prefixes.
5. **Constants/indices/initialization:** actions in A have length t and i<t; tape agreement includes index t, observation agreement excludes t. At t0 prefix consistency is vacuous and current output depends only on u0. No numerical initial action is required.
6. **Probability/information:** these are deterministic all-input properties, not AE statements. Previously sampled actions used in later calls are the actual A outputs. B's infinite-tape argument may contain future draws, but the asserted causality prevents their affecting P_t.
7. **Boundaries:** no kernel realization or distributional equality is concluded without the additional premises used later. This does not assert that action histories are arbitrary independent inputs to the generated trajectory; actual recursion fixes them.

## q3 — exact joint-law factorization at each round

For a jointly measurable sampler representing κ at every history, and any observation-stream probability law ν, the joint law of its generated history and current action is the history law composed with κ_t:
\[
\begin{gathered}
\forall\kappa\ [\forall t,\kappa_t\text{ Markov}]\ \forall f\in F,
[\forall t,\operatorname{uncurry}(f_t)\text{ measurable}]\Longrightarrow
[\forall t,h,(f_t(h))_*\lambda=\kappa_t(h)]\Longrightarrow\\
\forall\nu\in\operatorname{ProbabilityMeasure}(\mathbb R^{\mathbb N})\ \forall t\in\mathbb N,
\quad (C_t(f,\cdot),P_t(f,\cdot))_*M_\nu
=\bigl(C_t(f,\cdot)_*M_\nu\bigr)\otimes_m\kappa_t.
\end{gathered}
\]
The right side is the measure on H_t×I obtained by drawing h from the generated history law and then an action from κ_t(h); it is generally not a product of two independent marginal measures.

1. **Objects/spaces:** Markov kernels, supplied representing sampler, arbitrary observation probability law, product tape/observation measure and generated history/current-action pair.
2. **Quantifiers/order:** κ/Markov instances, f/joint measurability/full-history representation, ν, then t. The given f already represents κ before ν is chosen.
3. **Assumptions:** exactly those listed. ν need not have independent coordinates, identical marginals or feasible observations. Tape independence and freshness are part of the defined Mν, not additional inferred properties of ν.
4. **Conclusion/metric:** exact equality of two joint measures on H_t×I, using actual C and P from the same f recursion.
5. **Constants/indices/initialization:** all natural t; at t0 C is the unique empty history and the action law is its initial kernel. No horizon or loss constant.
6. **Probability/information:** measure equality, not pathwise equality of actions. The transition kernel conditions on generated past actions together with strict-past observations; current action can depend on this history. Observations' temporal dependence is allowed, but the entire observation stream remains independent of the tape under Mν.
7. **Boundaries:** this is not a claim for arbitrary joint laws coupling tape and observations or for an environment reacting to random actions. It states a one-round joint factorization for each t of a single consistent process, not an independently re-sampled algorithm for each t.

## q4 — conditional law up to history-law null sets

Under the same kernel representation premises and any ν, the conditional distribution of the current action given the generated history agrees with κ_t almost everywhere under that history's law:
\[
\begin{gathered}
\forall\kappa\ [\forall t,\kappa_t\text{ Markov}]\ \forall f\in F,
[\forall t,\operatorname{uncurry}(f_t)\text{ measurable}]\Longrightarrow
[\forall t,h,(f_t(h))_*\lambda=\kappa_t(h)]\Longrightarrow\\
\forall\nu\in\operatorname{ProbabilityMeasure}(\mathbb R^{\mathbb N})\ \forall t\in\mathbb N,
\quad \operatorname{condDistrib}_{M_\nu}(P_t\mid C_t)
=\kappa_t\quad (C_t)_*M_\nu\text{-a.e.}
\end{gathered}
\]

1. **Objects/spaces:** the same supplied kernel family, representing sampler, observation law and actual history/action maps; conditional kernels from H_t to I.
2. **Quantifiers/order:** κ/Markov, f/measurability/representation, ν, then t, then the asserted a.e. equality of kernel values.
3. **Assumptions:** identical to q3; neither iid targets nor interval-valued observations are required.
4. **Conclusion/metric:** equality of the conditional-distribution kernel to κ_t for history-law-almost every h, as measures on I.
5. **Constants/indices/initialization:** all t including zero, with its empty history. There is no fixed positive horizon requirement.
6. **Probability/information:** the AE reference measure is specifically \((C_t)_*M_\nu\), not volume on histories, the law ν alone or a universal all-history quantifier. q1's sampler representation holds at every history; this conditional-distribution equality has the usual null-history limitation.
7. **Boundaries:** no pointwise agreement at all unreachable histories is asserted. The exceptional sets may depend on ν and t; the statement does not produce one common exceptional history set across all ν or all changing history spaces.

## q5 — one universal sampler, consistent laws, and conditional expected-excess identity

For every Markov kernel family there is one sampler f, chosen before any observation law, that satisfies all sampling, measurability and deterministic consistency conclusions and, for every ν, both law conclusions at every time. For those ν whose coordinate process is independent, identically distributed and a.s. in [0,1], the same process additionally satisfies an exact finite expected-excess identity and nonnegativity at every horizon.

Define the following exact predicates as shorthand for the displayed q1–q4 formulas:
- \(J(f)\): joint measurability of every f_t.
- \(K(f,\kappa)\): \(\forall t,h,(f_t(h))_*\lambda=\kappa_t(h)\).
- \(B_m(f)\): measurability of every B_t.
- \(A_c(f)\): the all-t,u,y,i prefix equality displayed in q2.
- \(P_c(f)\): the all-t,ω,ω′ tape-≤t/observation-<t causality implication displayed in q2.
- \(L_t(f,\kappa,\nu)\): the exact joint-measure equality in q3.
- \(D_t(f,\kappa,\nu)\): the history-law-AE conditional-kernel equality in q4.

With \(Y_t(u,y)=y_t\), \(Q_t(u,y)=\operatorname{real}(P_t(f,(u,y)))\), \(m_\nu=\int y_0\,dM_\nu(u,y)\), and \(Y_t^\nu(y)=y_t\), the full conclusion is
\[
\begin{gathered}
\forall\kappa\ [\forall t,\kappa_t\text{ Markov}],\quad
\exists f\in F,\quad J(f)\land K(f,\kappa)\land B_m(f)\land A_c(f)\land P_c(f)\ \land\\
\forall\nu\in\operatorname{ProbabilityMeasure}(\mathbb R^{\mathbb N}),\quad
(\forall t,L_t(f,\kappa,\nu))\land(\forall t,D_t(f,\kappa,\nu))\ \land\\
\left[\operatorname{iIndepFun}_{\nu}(Y^\nu)\Longrightarrow
(\forall t,\operatorname{IdentDistrib}(Y_t^\nu,Y_0^\nu;\nu,\nu))\Longrightarrow
(\forall t,\ y_t\in[0,1]\ \nu\text{-a.e.})\Longrightarrow\\
\forall T\in\mathbb N,\quad
r(M_\nu,Y,Q,T)=\sum_{t<T}\int(Q_t-m_\nu)^2\,dM_\nu
\ \land\ 0\le r(M_\nu,Y,Q,T)\right].
\end{gathered}
\]

1. **Objects/spaces:** time-indexed Markov kernels, one existential sampler, its actual finite recursion and infinite prediction process, every probability law on real streams and, conditionally, their iid bounded coordinate processes and expected losses.
2. **Quantifiers/order:** κ and all Markov instances precede ∃f. The first five properties hold for that same f before ∀ν. Inside ∀ν, both all-time law properties are unconditional, followed by independence → identical marginals → a.s. support → ∀T excess conjunction. There is no ∀ν∃f or ∀T∃f weakening; no retuning f per horizon or law.
3. **Assumptions:** only Markov kernels are required for selecting f and the universal laws. The final loss conclusion requires three separate ν assumptions: joint family independence, identical distribution of each coordinate to coordinate zero, and per-coordinate a.s. [0,1] support. It does not require every real observation history to be feasible. Actions always lie in I by type, including at unreachable histories.
4. **Conclusion/metric:** one package of measurable kernel sampling, measurable B, pointwise actual recursion/causality, exact joint-law factorization, AE conditional laws, and the conditional finite-horizon identity/nonnegativity for literal r. Both sides of the loss identity use the same actual Q generated by f; no unrelated trace or law-dependent surrogate is substituted.
5. **Constants/indices/initialization:** infinite natural tape and time sequence, finite sums over t<T, squared loss and reference mean of observation zero under Mν. T0 yields empty sum and r=0. Initial action follows f0 and u0 at empty history, rather than a designated numerical constant. No division by T or rate constant appears.
6. **Probability/information:** tape and entire stream are independent under the product Mν. Each action may depend on all previously generated actions, strictly previous observations and its current fresh tape coordinate. Q's population-mean deviation is an expected error diagnostic, not an oracle input to f. b minimizes expected cumulative loss of one fixed feasible comparator after integrating both tape and observations; it is not a hindsight minimum inside expectation.
7. **Boundaries:** arbitrary ν receives the realization conclusions, but only iid a.s. bounded ν receives the stated loss guarantee. Nonnegative expected excess is neither vanishing regret nor a rate nor samplewise nonnegativity. No finite-horizon family inconsistency is allowed: prefix equality is pointwise and all times use one f. Conditional-kernel agreement retains its ν,t-dependent history-AE scope; there is no stronger universal null-set statement or action-adaptive environment guarantee.

## Ambiguities and limitations

No blocking semantic ambiguity was found in the literal definitions and target formulas. The name b denotes an outside-expectation real infimum even if informally described as a minimum; the supplied definition does not itself assert attainment. The joint-law operator in q3 is measure-kernel composition, not independence of history and action. The conditional law in q4 is history-law-AE, whereas the sampler's pushforward representation is every-history. The product observation model permits temporal dependence but not tape-dependent observations. Existence and all listed properties remain proposed theorem conclusions without proof evidence in the supplied files. No source acceptance or proof acceptance is assessed.
