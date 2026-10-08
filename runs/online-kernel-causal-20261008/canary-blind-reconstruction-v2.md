# Neutral canary reconstruction v2

Actor `/root/osd_blind`; requested GPT-6 Astra / medium, with no independent runtime model/effort attestation. This reused automated actor retains prior staged neutral-decoder/project history, including earlier interfaces. No absolute blindness, human review or external independence is claimed. Only the two designated v2 inputs were read this turn. This report reconstructs the twelve newly supplied clauses c2–c13; no c1 declaration occurs in the input. The q1–q5 interface is context, not re-reviewed proof evidence. No source, proof, package, chapter or Goal acceptance is assessed.

## Literal context and selected process

I denotes the unit-interval subtype. Histories are \(H_t=I^{\operatorname{Fin}t}\times\mathbb R^{\operatorname{Fin}t}\); samplers form \(F=\prod_t(H_t\to I\to I)\). The finite action recursion is
\[
A_0=(),\qquad A_{t+1}(f,u,y)=\operatorname{snoc}(a,f_t(a,y_{<t})(u_t)),\quad a=A_t(f,u_{<t},y_{<t}).
\]
Previously generated actions, rather than an unrelated supplied action trace, feed the next call. On \(\omega=(u,y)\in\mathcal W=I^{\mathbb N}\times\mathbb R^{\mathbb N}\),
\[
C_t(f,\omega)=(A_t(f,u_{<t},y_{<t}),y_{<t}),\quad
B_t(f,u,z)=f_t(A_t(f,u_{<t},z),z)(u_t),\quad
P_t(f,\omega)=B_t(f,u,y_{<t}).
\]
Let λ be uniform volume on I, \(R=\bigotimes_{t\in\mathbb N}\lambda\), and \(M_\nu=R\otimes\nu\). Thus fresh tape coordinates are mutually independent and the whole tape is independent of the whole observation stream. Arbitrary ν may have temporally dependent coordinates; the product model does not describe an observation law reacting to the tape or sampled actions.

The concrete action measures are
\[
\ell=\tfrac34\delta_0+\tfrac14\delta_1,\qquad h=\tfrac14\delta_0+\tfrac34\delta_1.
\]
Their weights in the Lean measures are nonnegative extended reals. Set \(S_0=\varnothing\) and
\[
S_{t+1}=\{(a,z)\in H_{t+1}:1<a_t+z_t\},\qquad
k_t(a,z)=\begin{cases}h,&(a,z)\in S_t,\\\ell,&(a,z)\notin S_t.\end{cases}
\]
The inequality is strict: sum exactly 1 uses the low law. At t0 the law is always ℓ. For positive times, the last generated action and last observation each affect which stochastic law is used. Neither branch is a deterministic action. Histories may contain arbitrary real observations, not only legal/binary ones.

The helper \(h1(a,z)\in H_1\) is the singleton action/observation history with those entries. The supplied \(f^*=\operatorname{Classical.choose}(q5(k))\) selects one existential witness from the q5 interface for this fixed k. That interface has order \(\forall k\ \exists f\ \forall\nu\), with deterministic all-time consistency and, inside each law, all-time law identities and all-horizon conditional loss claims. Therefore f* is chosen before every observation law and horizon, not retuned to either. This definition invokes an asserted interface; seeing `Classical.choose` does not verify q5's proof or an implementation of the sampler. Apart from the displayed Markov-instance tactic snippet, the supplied theorem headers have no proof bodies.

The observation law is \(c=\frac12\delta_0+\frac12\delta_1\) on ℝ and \(iLaw=\bigotimes_{t\in\mathbb N}c\). nStar packages this as a probability measure. Let \(m^*=M_{nStar}\), \(p_t^*=P_t(f^*,\cdot)\in I\), and \(Y_t^*(u,y)=y_t\). In this concrete product model the observations are iid fair binary values, with mean 1/2; their law is distinct from either action law. The sampler's pointwise outputs remain in I by type, whereas binary support of the actual outputs is stated almost everywhere in c9.

The exact benchmark and excess, with real-valued predictions Q, are
\[
b(\mu,Y,T)=\inf\{\int\sum_{t<T}(a-Y_t)^2\,d\mu:a\in[0,1]\},\qquad
r(\mu,Y,Q,T)=\int\sum_{t<T}(Q_t-Y_t)^2\,d\mu-b(\mu,Y,T).
\]
This is a real infimum of expected losses of fixed constant comparators, outside expectation; it is not expected samplewise hindsight minimum. The definition alone asserts no minimizer attainment or uniqueness. All fixed-comparator choices share the same a across times, tapes and observation samples. For the concrete claims abbreviate \(r_T^*=r(m^*,Y^*,\operatorname{real}\circ p^*,T)\), with the same actual process at every T. Empty sums give b0=r0=0. All expectations integrate both sources of randomness under the specified product law, and no horizon normalization occurs.

## c2 — sampler existence for k

There exists a jointly measurable sampler family representing the concrete stochastic kernel at every time and every history:
\[
\exists f\in F,\quad (\forall t,\operatorname{uncurry}(f_t)\text{ measurable})\land
(\forall t\ \forall h\in H_t,(f_t(h))_*\lambda=k_t(h)).
\]

1. **Objects:** concrete k, uniform seed coordinate, sampler family F.
2. **Quantifiers:** existential f first, then all-time measurability and all-time/all-history measure equality.
3. **Assumptions:** no explicit parameters or hypotheses; k and its supplied Markov structure are fixed context.
4. **Conclusion:** existence of a representing family; this clause does not identify its witness with f* syntactically.
5. **Constants/indices:** all natural times, including the low-law empty-history case at zero.
6. **Probability/information:** equality of pushforward action measures for each history, not merely AE under an observation law. Joint measurability concerns (history, uniform draw).
7. **Boundaries:** no horizon or ν is chosen here, no unique/computable sampler, and no proof of existence is supplied in the header.

## c3 — actual prefix consistency and causality of f*

The chosen family has measurable before-reveal rules, consistent generated action prefixes, and pointwise causal dependence:
\[
\begin{gathered}
(\forall t,B_t(f^*,\cdot)\text{ measurable})\ \land\\
(\forall t,u\in I^{\mathbb N},y\in\mathbb R^{\mathbb N},i\in\operatorname{Fin}t,
A_t(f^*,u_{<t},y_{<t})_i=P_i(f^*,(u,y)))\ \land\\
(\forall t,\omega=(u,y),\omega'=(u',y'),
[\forall i\le t,u_i=u'_i]\Rightarrow[\forall i<t,y_i=y'_i]\Rightarrow
P_t(f^*,\omega)=P_t(f^*,\omega')).
\end{gathered}
\]

1. **Objects:** fixed f*, its actual A/B/P constructions and arbitrary infinite tapes/observations.
2. **Quantifiers:** conjunction of all-t measurability, all-t,u,y,i equality and all-t,ω,ω′ prefix implications; no probability law is quantified.
3. **Assumptions:** none beyond fixed context; matching prefixes are local antecedents of the third conjunct only.
4. **Conclusion:** deterministic measurability, actual feedback-prefix equality and causal output invariance.
5. **Constants/indices:** tape indices include t; observation indices exclude t. At zero, action-prefix equality is vacuous and P0 depends on u0 only.
6. **Probability/information:** claims hold for every real observation history and tape, not only AE paths. Later actions use actual previous generated actions.
7. **Boundaries:** no claim that f* samples by a specific threshold implementation; no direct distribution or expected-loss result in this clause.

## c4 — joint history/action law for every ν

For every observation probability law and time, generated history followed by the current action has the kernel-composed law:
\[
\forall\nu\in\operatorname{ProbabilityMeasure}(\mathbb R^{\mathbb N})\ \forall t\in\mathbb N,
\quad(C_t(f^*,\cdot),P_t(f^*,\cdot))_*M_\nu
=((C_t(f^*,\cdot))_*M_\nu)\otimes_m k_t.
\]

1. **Objects:** fixed f*, arbitrary ν, product measure, generated history/current action, concrete kernel.
2. **Quantifiers:** ν then t, with f* already fixed before both.
3. **Assumptions:** ν is a probability measure; no temporal independence, identical marginals or observation bounds.
4. **Conclusion:** exact equality of measures on H_t×I; right side means draw history from its law then action from k_t(history).
5. **Constants/indices:** all t including zero; initial history is empty and its action law is ℓ.
6. **Probability/information:** measure-kernel composition is not a product of independent history/action marginals; action law depends on actual history. Tape independence from the entire stream is built into Mν.
7. **Boundaries:** no statement for arbitrary tape-correlated or action-responsive observation models, despite allowing arbitrary dependence within ν.

## c5 — conditional action law

For every ν and time, the conditional action law given generated history agrees with k_t for almost every history under its actual law:
\[
\forall\nu\ \forall t,\qquad
\operatorname{condDistrib}_{M_\nu}(P_t(f^*,\cdot)\mid C_t(f^*,\cdot))
=k_t\quad ((C_t(f^*,\cdot))_*M_\nu)\text{-a.e.}
\]

1. **Objects:** same fixed process, law ν and conditional kernels from H_t to I.
2. **Quantifiers:** ν, t, then AE equality with respect to that ν,t-specific history law.
3. **Assumptions:** only the probability-law type for ν, not iid or boundedness.
4. **Conclusion:** equality of kernel values as action measures at history-law-almost every h.
5. **Constants/indices:** t0 included; no horizon or numeric bound.
6. **Probability/information:** conditioning variable contains actual previous actions and strict-past observations. AE is on history space, not a universal all-history equality or uniform-volume statement.
7. **Boundaries:** exceptional histories may depend on ν and t. No single universal exceptional set, nor equality at all unreachable histories, is asserted.

## c6 — concrete finite expected-excess identity

For every horizon, the concrete process's expected fixed-comparator excess equals cumulative mean squared distance to the observation mean, and is nonnegative:
\[
\forall T\in\mathbb N,\quad
r_T^*=\sum_{t<T}\int(\operatorname{real}(p_t^*)-\int Y_0^*\,dm^*)^2\,dm^*
\quad\land\quad 0\le r_T^*.
\]

1. **Objects:** fixed f*, iid fair-binary observation law, product m*, actual p*, fixed benchmark and horizon.
2. **Quantifiers:** T only; all process choices precede it. Both conjuncts concern the same r*.
3. **Assumptions:** no free premises; iid support and law are concrete definitions here, not universal statements about arbitrary ν.
4. **Conclusion:** equality and nonnegativity of expected excess, not a pathwise or hindsight-regret assertion.
5. **Constants/indices:** squared deviations from observation-zero mean (1/2 in this model), t<T; T0 yields empty sum and zero.
6. **Probability/information:** integrals average over tape and outcomes; the predictor is the actual recursive process, not an oracle-mean predictor.
7. **Boundaries:** no upper rate, convergence, or vanishing average follows from nonnegativity. c11 later specifies a positive linear value.

## c7 — explicit one-step dependence on actions and observations

At the stated three singleton histories, the probability of action 1 is respectively one quarter, three quarters and one quarter:
\[
k_1(h1(0,1))(\{1\})=\tfrac14\ \land\
k_1(h1(1,1))(\{1\})=\tfrac34\ \land\
k_1(h1(1,0))(\{1\})=\tfrac14.
\]

1. **Objects:** three concrete H1 histories and their kernel masses at the singleton endpoint 1.
2. **Quantifiers:** a closed conjunction with no free parameters.
3. **Assumptions:** only context definitions; no reachability assumption for these histories.
4. **Conclusion:** exact ENNReal probability values. Changing the action from 0 to 1 with observation 1 changes the law; changing observation 0 to 1 with action 1 also changes it.
5. **Constants/indices:** time 1; sums 1, 2, 1 under the strict test 1<a+y; the equality boundary takes the low branch.
6. **Probability/information:** this is kernel dependence on prior action and prior observation, not dependence on current observation. Each branch remains randomized.
7. **Boundaries:** does not assert deterministic next actions or that these particular histories occur with a specified positive path probability.

## c8 — nondegenerate endpoint probabilities at every history

At every time and history, the mass of endpoint 1 is either one quarter or three quarters, and both endpoints have strictly positive mass:
\[
\forall t\in\mathbb N\ \forall h\in H_t,
\quad [k_t(h)(\{1\})=\tfrac14\ \lor\ k_t(h)(\{1\})=\tfrac34]
\land 0<k_t(h)(\{0\})\land0<k_t(h)(\{1\}).
\]

1. **Objects:** concrete kernel at arbitrary history/time and endpoint singleton masses.
2. **Quantifiers:** t then h, followed by a disjunction and two positivity conjuncts.
3. **Assumptions:** all real histories are allowed; no legal-history or AE restriction.
4. **Conclusion:** exact possible masses and positive probability of each endpoint. The definitions additionally locate all mass on the two endpoints; the displayed clause itself expresses the listed mass/positivity facts.
5. **Constants/indices:** ENNReal 1/4 and 3/4, strict positivity; t0 uses low law.
6. **Probability/information:** global stochastic nondegeneracy of both branches, independent of whether a history is reached under a chosen ν.
7. **Boundaries:** no common deterministic action or equal-probability action law; the action law is not the observation law c.

## c9 — AE binary support of actual predictions

At each natural time, the actual prediction is an endpoint almost surely under the concrete joint law:
\[
\forall t\in\mathbb N,\quad m^*\text{-a.e. }\omega,
\quad p_t^*(\omega)=0\ \lor\ p_t^*(\omega)=1.
\]

1. **Objects:** fixed actual prediction process and product m*.
2. **Quantifiers:** t first, then AE ω, then the endpoint disjunction. The displayed conclusion is per-time AE support.
3. **Assumptions:** no extra premise beyond the concrete context.
4. **Conclusion:** binary-valuedness almost surely for actual predictions, stronger than I-valuedness by type but not pointwise equality for every sample.
5. **Constants/indices:** endpoints 0 and 1, every t including zero.
6. **Probability/information:** support is under m*, not every-history/every-tape support of the selected sampler. Countability permits a simultaneous all-natural-times full-measure interpretation, but the exact clause is ∀t, AE ω and supplies no universal set across observation laws.
7. **Boundaries:** sampler values on null seed/path inputs are not constrained to endpoints by this clause; this is not a particular implementation of f*.

## c10 — exact current observation variance

Every observation coordinate has variance one quarter under the concrete joint law:
\[
\forall t\in\mathbb N,\qquad \operatorname{Var}_{m^*}(Y_t^*)=\tfrac14.
\]

1. **Objects:** real observation coordinate and product m*.
2. **Quantifiers:** arbitrary natural t; no other free input.
3. **Assumptions:** concrete iid fair-binary law, not an arbitrary bounded process.
4. **Conclusion:** exact observation variance, not prediction variance or conditional action variance.
5. **Constants/indices:** positive real 1/4 at all times including zero.
6. **Probability/information:** marginal variance under joint tape/stream averaging; observation law is independent of the tape.
7. **Boundaries:** does not claim observations are deterministic or that the action masses are 1/2; positivity is a nondegenerate feature of this canary.

## c11 — exact linear expected fixed-comparator excess

For every natural horizon, the concrete actual process has expected fixed-comparator excess exactly T/4:
\[
\forall T\in\mathbb N,\qquad r_T^*=\frac{T}{4}.
\]

1. **Objects:** one selected infinite process, concrete product law, literal fixed-expected benchmark and finite horizon.
2. **Quantifiers:** all T after fixed f*, k and nStar; no per-horizon family selection.
3. **Assumptions:** no additional premises, beyond the defined concrete objects.
4. **Conclusion:** exact real equality, not merely nonnegativity, a bound, or expected hindsight regret.
5. **Constants/indices:** T is coerced to ℝ and divided by 4; at T0 value is zero and every positive T gives positive excess. This is cumulative, not already normalized.
6. **Probability/information:** the actual history-dependent stochastic actions remain compared to a single constant comparator optimized outside expectation; same-process recursion is preserved.
7. **Boundaries:** this is linear excess and does not demonstrate no-regret or convergence of normalized excess to zero. No proof of the equality is supplied here.

## c12 — empty-horizon value

The concrete expected excess at horizon zero is zero:
\[
r_0^*=0.
\]

1. **Objects:** concrete expected-excess definition and empty horizon.
2. **Quantifiers:** closed numerical clause, no parameters.
3. **Assumptions:** fixed context only.
4. **Conclusion:** exact zero value.
5. **Constants/indices:** T=0; all loss sums are empty and benchmark image is {0}.
6. **Probability/information:** no action is scored, even though a time-zero action exists in the infinite process.
7. **Boundaries:** zero here is compatible with positive losses/excess at positive horizons; it does not mean initial action is zero or deterministic.

## c13 — positive two-round value

At horizon two the expected fixed-comparator excess is one half and strictly positive:
\[
r_2^*=\tfrac12\quad\land\quad 0<r_2^*.
\]

1. **Objects:** concrete actual process, product law and two-round expected excess.
2. **Quantifiers:** closed conjunction without free parameters.
3. **Assumptions:** fixed context only.
4. **Conclusion:** exact value together with strict positivity, not a samplewise lower bound.
5. **Constants/indices:** T=2 scores times 0 and 1; real value 1/2. The second prediction has genuine prior action and observation available through the recursion.
6. **Probability/information:** averages the actual stochastic process and compares to the fixed-expected benchmark, not a sample-selected comparator.
7. **Boundaries:** does not claim every individual two-round trajectory has positive excess or that the policy is optimal; it is a nonzero finite-horizon diagnostic.

## Ambiguity and evidence boundary

No blocking semantic ambiguity was found. The new numbered clauses are exactly c2–c13 (12 clauses); no missing c1 was invented. f* is a classical witness selected from the q5 statement for fixed k before ν and T; interface invocation is not verified implementation or proof evidence. Actual prior actions feed the history threshold. Both action laws remain genuinely stochastic, while conditional law and realized binary-support assertions retain their specified law-dependent AE scopes. The literal benchmark is outside expectation, giving the stated T/4 target rather than any silently substituted hindsight metric. All reconstruction and hash bindings are statement-only evidence; no acceptance verdict is issued.
