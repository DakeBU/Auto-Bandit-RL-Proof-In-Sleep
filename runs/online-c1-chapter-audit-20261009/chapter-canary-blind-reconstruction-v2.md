# Whole-unit canary statement reconstruction v2

Actor /root/osd_blind; requested GPT-6 Astra / medium, runtime model/effort not independently attested. This reused automated actor has prior staged decoder/project history. No absolute blindness, human review or external independence is claimed. Only the v2 packet/index and its two indexed inputs were read; undispatched v1 context was not read. These are 27 proposed theorem types, not supplied proof bodies or compilation evidence. Definition-level proof terms establishing subtype values or defining a kernel are not proofs of these targets. No source, chapter or program acceptance is assessed.

## Exact shared context and notation

Let \(I=[0,1]\), also used as a subtype for actions. \(\bar y_T=\sum_{t<T}y_t/T\), \(p^a_0(y)=a\), \(p^a_t(y)=\bar y_t\) for t>0, and \(p=p^{1/2}\). Actual predictions read only strict-past observations. State update is \((n,x)\mapsto(n+1,x+(z-x)/(n+1))\); \(S^a_0=(0,a)\) and \(S^a_{t+1}\) updates with y_t. Initialization is not an additional observation in later averages.
Define \(r_t=0\) at t0 and 1 otherwise (rising), \(f_t=1\) at t0 and 0 otherwise (falling). Let \(\mathbf c\) denote a constant-c stream.
For any supplied prediction q,
\[
R_T^y(q,u)=\sum_{t<T}(q_t-y_t)^2-\sum_{t<T}(u-y_t)^2,\quad
G_T(y,q)=\sum_{t<T}(q_t-y_t)^2-\inf_{u\in I}\sum_{t<T}(u-y_t)^2.
\]
Write \(G_T^a(y)=G_T(y,p^a(y))\). Comparator regret for general losses is the same signed difference of the two sums. Best regret uses the real image infimum over fixed feasible constants, not an arbitrary selected comparator. For stochastic Y,Q,
\[
B_T(\mu,Y)=\inf_{u\in I}\mathbb E_\mu\sum_{t<T}(u-Y_t)^2,\quad
E_T(\mu,Y,Q)=\mathbb E_\mu\sum_{t<T}(Q_t-Y_t)^2-B_T.
\]
The expected fixed minimum puts the infimum OUTSIDE integration; hindsight minimum \(h_T(\omega)=\inf_{u\in I}\sum_{t<T}(u-\omega_t)^2\) is instead minimized for each realized prefix before integration. No interchange is implicit. Bare definitions do not establish uniqueness or attainment. Natural ranges exclude their upper endpoint. Totalized division yields \(\bar y_0=0\), all zero-horizon regret values and ratios zero, whereas p0=1/2 or a.

Upper NoRegret \(U(y,q)\) means \(\forall u\in I,\forall\epsilon>0,\exists N,\forall T\ge N,R_T^y(q,u)/T\le\epsilon\). The threshold may depend on u,ε. Ordinary-limit NoRegret \(L(y,q)\) means \(\forall u\in I,\exists a\le0,R_T^y(q,u)/T\to a\). Ordinary limits use natural atTop and real neighborhoods; little-o controls magnitude. Upper bounds do not require ordinary limits.

The dyadic stream is \(d_0=0,\ d_{n+1}=1-d_{\lfloor n/2\rfloor}\), natural division on predecessor n. Demo loss on Bool is 0 for false, -2 for true at t0 and 3 for true at positive t. Demo leader is true exactly at n=1.
The domain probe has comparator source set [0,1], typed action domain W=[0,2], loss \(\ell_t(x)=-x\), constant played action2 and reference1. Its trace is legal in W without being legal in the smaller source set.

For the iid benchmark let \(c=\frac12\delta_0+\frac12\delta_1\) on ℝ, \(\nu=\bigotimes_{t\in\mathbb N}c\), \(Y_t(\omega)=\omega_t\), and \(Q_t(\omega)=p_t(\omega)\). These observations are iid fair binary coordinates. This law is different from repeating the SAME random coordinate at every time, as in C023.

For kernel cases let \(H_t=I^{\operatorname{Fin}t}\times\mathbb R^{\operatorname{Fin}t}\).
The low law is \(\ell=\frac34\delta_0+\frac14\delta_1\), high law \(h=\frac14\delta_0+\frac34\delta_1\) on I. At time0 the switch set is empty; at t+1 its condition is strictly \(1<a_t+y_t\). The kernel k chooses high inside this set and low outside; sum exactly1 selects low. Thus the intended inequality is precisely \(1<a_t+y_t\), with no added constant on the right.
A sampler family F maps (time, past actions/observations, current uniform coordinate) to I. Actual action recursion appends
\[
a_{t+1}=\operatorname{snoc}(a_t,F_t(a_t,y_{<t})(u_t)),
\]
with a0 empty and a_t recursively generated from the first t tape/observation coordinates. Causal policy computes that same action history; generated history is \((a_t,y_{<t})\), and prediction at t uses current tape u_t but no y_t.

The selected sampler is Classical.choose of the supplied existential HEADER at k. That header has order \(\forall k,\exists F,\forall\nu'\), and provides joint sampler measurability, every-history uniform pushforward representation, actual prefix consistency/causality, all-time joint/conditional law identities for every ν′, and an iid-support-conditional all-horizon expected excess identity. F is chosen once before law/horizon, not retuned. Referencing this header is not proof verification.
Uniform tape law is \(\rho=\bigotimes_t\operatorname{volume}_I\); kernelGameLaw(ν′)=ρ×ν′. The concrete kernel game uses the supplied iid observation law, here denoted ν, and \(M=\rho\times\nu\). Tape coordinates are fresh independent uniforms independent of the complete exogenous observation stream. Denote its selected actual real-valued prediction by \(Q^K_t\), target by \(Y^K_t(u,y)=y_t\), and expected fixed excess by \(E_T^K\). All actions are in I by type; endpoint support or conditional-law assertions remain probabilistic consequences of the interface, not arbitrary pointwise properties of a chosen sampler. Conditional kernel equality in the supporting header is AE under its actual history law, while uniform sampling representation is every-history. No action-responsive observation environment is included.

Finally, finiteActionMeasure is \(\sum_{b\in arms}\operatorname{ofReal}(p_b)\delta_b\); on Bool with both weights1/2 this is a fair seed law β. The seeded policy outputs1 for true and0 for false for EVERY history, retaining its one seed throughout. A history list is newest-first: reversing it gives chronological binary outcomes, default false past its length; causalPredict passes reversed strict prefixes to the policy. Path regret scores the full list length against that binary prefix's empirical mean. Rational harmonic \(H_n^\mathbb Q=\sum_{i<n}((i+1):\mathbb Q)^{-1}\), coerced to ℝ when displayed with a real logarithm.

## Individual targets

### C001

A feasible zero initialization can give one-round best regret1, strictly larger than1/4.

\[
G_1^0(\mathbf1)=1\land G_1^0(\mathbf1)>1/4.
\]

1. **Objects:** Constant-one stream, actual zero-initial predictor, feasible best comparator.
2. **Quantifiers/order:** Closed two-part conjunction.
3. **Assumptions:** No free premises; fixed feasible data.
4. **Conclusion/metric:** Exact value and strict inequality.
5. **Constants/indices/boundaries:** T1 scores t0 only; initial0; comparator infimum over I.
6. **Information/probability:** Deterministic, before observing first1.
7. **Excluded scope:** Does not transfer the half-initial1/4 constant to all initializations.

### C002

For falling observations, zero initialization increases two-round best regret by3/4 relative to half initialization.

\[
G_2^0(f)=G_2^{1/2}(f)+3/4.
\]

1. **Objects:** Same falling stream, two actual initialized predictors.
2. **Quantifiers/order:** Closed equality.
3. **Assumptions:** Fixed f=(1,0,...), initial0 and half.
4. **Conclusion/metric:** Exact positive correction.
5. **Constants/indices/boundaries:** T2; only first prediction differs.
6. **Information/probability:** Same realized comparator benchmark cancels between runs.
7. **Excluded scope:** Not a universal positive correction for other streams.

### C003

For rising observations, zero initialization improves two-round best regret by1/4.

\[
G_2^0(r)=1/2\land G_2^{1/2}(r)=3/4\land[(0-r_0)^2-(1/2-r_0)^2]=-1/4.
\]

1. **Objects:** Rising stream and two initialized actual traces.
2. **Quantifiers/order:** Closed three-part conjunction.
3. **Assumptions:** Fixed r0=0,r1=1.
4. **Conclusion/metric:** Two exact best-regret values and negative first-loss correction.
5. **Constants/indices/boundaries:** T2, first observation0; correction subtracts half loss.
6. **Information/probability:** Deterministic same stream.
7. **Excluded scope:** Correction is signed, not its absolute value.

### C004

Falling two-round regret is3/2 and satisfies the finite bound3; constant-one one-round regret satisfies bound1.

\[
G_2^0(f)=3/2\land G_2^0(f)\le3\land G_1^0(\mathbf1)\le1.
\]

1. **Objects:** Two concrete streams and actual zero-initial rule.
2. **Quantifiers/order:** Closed three-part conjunction.
3. **Assumptions:** No external conditions.
4. **Conclusion/metric:** Exact value and two upper bounds.
5. **Constants/indices/boundaries:** T2 bound3=1+4/2; T1 bound1 corresponds to empty reciprocal tail.
6. **Information/probability:** Deterministic best-comparator metrics.
7. **Excluded scope:** No tightness asserted for T2 or all-horizon theorem supplied.

### C005

Equal first observations give equal states at time1; differing current observations lead to different states at time2.

\[
S^0_1(r)=S^0_1(\mathbf0)\land r_1\ne0\land S^0_2(r)\ne S^0_2(\mathbf0).
\]

1. **Objects:** Actual state recurrence on rising/zero streams.
2. **Quantifiers/order:** Closed three-conjunct statement.
3. **Assumptions:** Shared initialization0 and explicit streams.
4. **Conclusion/metric:** Whole-state equality then inequality, plus differing observation.
5. **Constants/indices/boundaries:** State1 has read only index0; state2 includes index1.
6. **Information/probability:** Current observation affects next state, not current pre-reveal state.
7. **Excluded scope:** No claim future differences change earlier states.

### C006

The three-quarter initial state becomes mean0 after one observation and mean1/2 after two.

\[
S^{3/4}_0(r)=(0,3/4)\land S^{3/4}_1(r)=(1,0)\land S^{3/4}_2(r)=(2,1/2).
\]

1. **Objects:** Actual count/mean state pairs.
2. **Quantifiers/order:** Closed conjunction.
3. **Assumptions:** Fixed rising stream, initial3/4.
4. **Conclusion/metric:** Exact full state values.
5. **Constants/indices/boundaries:** Times0,1,2; initial not counted as data.
6. **Information/probability:** State after first observation discards initial mean.
7. **Excluded scope:** Not a supplied arbitrary trace or exponential moving average.

### C007

Every feasible initialization gives upper no-regret on the fixed dyadic stream.

\[
\forall a\in[0,1],\ U(d,p^a(d)).
\]

1. **Objects:** Fixed d, all feasible real initializations, fixed comparators.
2. **Quantifiers/order:** ∀initial then membership, then ∀u∈I,∀ε>0,eventually T.
3. **Assumptions:** Only initial feasibility; d fixed by definition.
4. **Conclusion/metric:** Comparatorwise eventual upper condition.
5. **Constants/indices/boundaries:** N may depend on initial,u,ε; T0 ratio0.
6. **Information/probability:** Same initialized strict-past rule for all horizons.
7. **Excluded scope:** Not ordinary convergence of each comparator ratio.

### C008

Three-quarter-initialized dyadic best regret has zero normalized ordinary limit.

\[
G_T^{3/4}(d)/T\longrightarrow0.
\]

1. **Objects:** Fixed actual rule and realized-best regret sequence.
2. **Quantifiers/order:** Closed natural-horizon limit.
3. **Assumptions:** Fixed feasible initial3/4, no convergence premise.
4. **Conclusion/metric:** Ordinary zero limit of best-regret ratio.
5. **Constants/indices/boundaries:** T0 total ratio0; initial remains fixed.
6. **Information/probability:** Deterministic stream with possibly oscillating means.
7. **Excluded scope:** Not convergence of all fixed-comparator ratios or empirical means.

### C009

Even with infeasible observations and initialization, the one-round initial-loss correction is -21/4.

\[
G_1^2(\mathbf3)=G_1^{1/2}(\mathbf3)-21/4.
\]

1. **Objects:** Real stream constantly3, initial2, feasible comparator set still I.
2. **Quantifiers/order:** Closed equality.
3. **Assumptions:** No feasibility hypotheses; displayed data outside I.
4. **Conclusion/metric:** Exact signed difference of best metrics.
5. **Constants/indices/boundaries:** T1, correction (2-3)^2-(1/2-3)^2=-21/4.
6. **Information/probability:** Deterministic same stream; only initial prediction.
7. **Excluded scope:** Not feasible-initial performance guarantee; regret can be negative against constrained comparator set.

### C010

At horizon zero both regrets vanish although the would-be first-loss correction is3/4.

\[
G_0^0(f)=0\land G_0^{1/2}(f)=0\land[(0-f_0)^2-(1/2-f_0)^2]=3/4.
\]

1. **Objects:** Empty scored prefix and falling first observation.
2. **Quantifiers/order:** Closed three-part conjunction.
3. **Assumptions:** Fixed data only.
4. **Conclusion/metric:** Zero metric values and nonzero correction separately.
5. **Constants/indices/boundaries:** No prediction is scored at T0; f0=1.
6. **Information/probability:** Deterministic; initial actions still defined but unscored.
7. **Excluded scope:** Shows positive-horizon correction identity cannot extend unchanged to zero.

### C011

Two-round regret to fixed zero differs from true feasible-best regret.

\[
R_2^f(p^0,0)=1\land G_2^0(f)=3/2.
\]

1. **Objects:** Same actual falling run, fixed comparator0 versus best value.
2. **Quantifiers/order:** Closed conjunction.
3. **Assumptions:** Fixed initial0, T2.
4. **Conclusion/metric:** Exact different signed metric values.
5. **Constants/indices/boundaries:** Values1 versus3/2, cumulative not normalized.
6. **Information/probability:** No expectation; best comparator may differ from0.
7. **Excluded scope:** Do not substitute a chosen comparator for the infimum.

### C012

The fair iid benchmark has variance1/4, two-round expected fixed excess1/4, and average excess1/8.

\[
\operatorname{Var}_\nu(Y_0)=1/4\land E_2(\nu,Y,Q)=1/4\land E_2(\nu,Y,Q)/2=1/8.
\]

1. **Objects:** iid fair-bit stream law, actual half-initial empirical-mean rule.
2. **Quantifiers/order:** Closed conjunction.
3. **Assumptions:** No supplied hypothesis; concrete product law.
4. **Conclusion/metric:** Variance and cumulative/average expected excess.
5. **Constants/indices/boundaries:** Horizon2; first prediction half, second Y0.
6. **Information/probability:** Expectation over iid observations; no private tape in this benchmark.
7. **Excluded scope:** Variance not a prediction variance; fixed expected minimum not hindsight minimum.

### C013

The least fixed expected two-round loss is1/2 and the constant-half oracle has zero expected excess.

\[
\operatorname{IsLeast}(\{\mathbb E_\nu\sum_{t<2}(u-Y_t)^2:u\in I\},1/2)\land E_2(\nu,Y,Q_t\equiv1/2)=0.
\]

1. **Objects:** Image of feasible fixed expected losses and constant-half predictor.
2. **Quantifiers/order:** Closed conjunction; comparator quantifiers inside IsLeast.
3. **Assumptions:** Concrete fair iid process.
4. **Conclusion/metric:** Least value includes attainment and all-comparator lower bound; zero excess.
5. **Constants/indices/boundaries:** T2, value1/2.
6. **Information/probability:** One comparator fixed before integration.
7. **Excluded scope:** No samplewise optimum or unknown-law learning algorithm; uniqueness not stated.

### C014

Expected hindsight optimum is1/4 while optimizing expected fixed loss yields1/2.

\[
\mathbb E_\nu h_2=1/4\land B_2(\nu,Y)=1/2.
\]

1. **Objects:** Two orders of infimum and integration.
2. **Quantifiers/order:** Closed numerical conjunction.
3. **Assumptions:** Concrete iid fair binary observations.
4. **Conclusion/metric:** Distinct exact benchmarks.
5. **Constants/indices/boundaries:** T2; constants1/4 and1/2.
6. **Information/probability:** First optimizes per sample before expectation; second fixes comparator across samples.
7. **Excluded scope:** No commutation of minimum and expectation; no predictor in statement.

### C015

For the supplied independent identically distributed coordinate process and its actual strict-past mean predictor, expected excess over the best fixed expected comparator, divided by horizon, converges ordinarily to zero. The unnormalized excess is also little-o of the horizon.

\[
\frac{E_T(\mathrm{meanPredict})}{T}\longrightarrow0,\qquad E_T(\mathrm{meanPredict})=o(T).
\]

1. **Objects:** The fixed iidLaw, observation process, and meanPredict; E is the expected-fixed metric defined above.
2. **Quantifiers/order:** A conjunction of two closed asymptotic assertions; the limit variable is natural T.
3. **Assumptions:** No additional premise in this closed type.
4. **Conclusion/metric:** Ordinary real convergence to zero and little-o (an absolute-magnitude asymptotic statement).
5. **Constants/indices/boundaries:** Natural T tends to infinity; real division at T=0 is totalized and does not alter the eventual assertions.
6. **Information/probability:** The same actual mean predictor is used in both clauses, with initial prediction 1/2 and strict-past averages thereafter; minimum is outside expectation.
7. **Excluded scope:** Does not assert a rate, a pointwise limit, a result for every predictor, or merely a one-sided upper condition.

### C016

The constant output 2 belongs to the larger output interval but not the smaller source interval. Its two-round regret against 1 is -2 under loss -x, and -4 when this loss is multiplied by 2.

\[
2\in[0,2]\ \land\ 2\notin[0,1]\ \land\ R_2(-x,2,1)=-2\ \land\ R_2(-2x,2,1)=-4.
\]

1. **Objects:** Subtype-valued output and referenceOne; domainLoss=-value; sourceV and outputW.
2. **Quantifiers/order:** A closed four-part conjunction.
3. **Assumptions:** No feasibility premise beyond the actual subtype of the given actions.
4. **Conclusion/metric:** Membership distinction and signed fixed-comparator regret equalities.
5. **Constants/indices/boundaries:** Horizon 2; scaling factor 2; signs remain negative.
6. **Information/probability:** Deterministic constant actions and losses; no probability or information assumption.
7. **Excluded scope:** No transfer of output legality into the smaller source domain; no claim that regret must be nonnegative.

### C017

The first two values of rising have empirical mean 1/2 and best feasible constant squared loss 1/2. At horizon zero every feasible constant has zero cumulative squared loss.

\[
e_2(r)=\frac12,\quad \inf_{u\in I}\sum_{t<2}(u-r_t)^2=\frac12,\quad \forall u\in I,\ \sum_{t<0}(u-r_t)^2=0.
\]

1. **Objects:** rising, empiricalMean, real sInf over I=[0,1], and empty finite sum.
2. **Quantifiers/order:** First two closed equalities, then universal u in I for the empty-prefix clause.
3. **Assumptions:** Only u∈I in the last clause.
4. **Conclusion/metric:** Empirical mean and finite-horizon infimum values; zero-horizon tie equality.
5. **Constants/indices/boundaries:** Indices 0 and 1 have observations 0 and 1; horizon zero has an empty sum.
6. **Information/probability:** Deterministic hindsight constant minimization.
7. **Excluded scope:** Does not assert uniqueness at horizon zero; does not replace the infimum with an expected benchmark.

### C018

Any real constant whose two-round squared loss on rising is no larger than the loss at the empirical mean must equal 1/2.

\[
\forall u\in\mathbb R,\quad \sum_{t<2}(u-r_t)^2\le \sum_{t<2}(e_2(r)-r_t)^2\ \Longrightarrow\ u=\frac12.
\]

1. **Objects:** All real constants and the empirical mean of the two-point sequence.
2. **Quantifiers/order:** Universal u, followed by implication from the loss comparison.
3. **Assumptions:** The stated no-larger-loss comparison; no u∈I premise.
4. **Conclusion/metric:** Uniqueness under the comparison, in the ambient real domain.
5. **Constants/indices/boundaries:** Horizon exactly 2; value 1/2.
6. **Information/probability:** Deterministic full-prefix comparison.
7. **Excluded scope:** Not a universal uniqueness assertion for every horizon or an existence producer in its own wording.

### C019

Using the specified Boolean demo leaders, the sum of each round's loss at the next leader is -2; evaluating both rounds at the final leader gives 0. The former is at most the latter.

\[
\sum_{t<2}\ell_t(L_{t+1})=-2,\quad \sum_{t<2}\ell_t(L_2)=0,\quad \sum_{t<2}\ell_t(L_{t+1})\le\sum_{t<2}\ell_t(L_2).
\]

1. **Objects:** demoLoss and demoLeader from the context, with Boolean actions.
2. **Quantifiers/order:** Closed conjunction of two values and their comparison.
3. **Assumptions:** No universal minimizer premise; the objects are fixed concrete functions.
4. **Conclusion/metric:** Three finite cumulative-loss statements.
5. **Constants/indices/boundaries:** L1=true and L2=false; true loses -2 at round 0 and 3 at later rounds; false loses 0.
6. **Information/probability:** The next leader L_(t+1) includes the current prefix endpoint; this is not the played strict-past leader L_t.
7. **Excluded scope:** No general theorem for arbitrary losses or leaders is stated here.

### C020

The half-initialized predictor has best-comparator squared regret 3/4 at horizon 2 on rising. This value is bounded by both 9/4 and 4+4 log 2.

\[
G_2^{1/2}(r)=\frac34,\qquad G_2^{1/2}(r)\le\frac94,\qquad G_2^{1/2}(r)\le4+4\log2.
\]

1. **Objects:** Actual meanPredict, rising, and squaredBestRegret.
2. **Quantifiers/order:** Closed three-part conjunction.
3. **Assumptions:** No extra assumptions.
4. **Conclusion/metric:** One exact regret value and two unnormalized upper bounds.
5. **Constants/indices/boundaries:** T=2, initialization 1/2; natural logarithm.
6. **Information/probability:** Deterministic played predictor versus the hindsight best feasible fixed constant.
7. **Excluded scope:** Not a proof of the corresponding bounds for arbitrary horizons or arbitrary initialization.

### C021

At round 1 of rising, replacing the actual current prediction by the next prefix mean reduces squared loss by 3/4, which is bounded by 4/(1+1)=2.

\[
(p_1-r_1)^2-(p_2-r_1)^2=\frac34,\qquad (p_1-r_1)^2-(p_2-r_1)^2\le\frac4{1+1}.
\]

1. **Objects:** p=meanPredict rising, with p1=0, p2=1/2, and r1=1.
2. **Quantifiers/order:** Two closed assertions.
3. **Assumptions:** No added premise.
4. **Conclusion/metric:** Signed one-step loss difference and its upper bound.
5. **Constants/indices/boundaries:** Round index 1, denominator 1+1=2; no zero division in this instance.
6. **Information/probability:** p1 uses strict past; p2 includes the observation r1 against which both losses are evaluated.
7. **Excluded scope:** Does not identify p2 as an available pre-observation prediction at round 1.

### C022

The actual predictor generated by the selected sampler has expected excess over the best fixed expected constant equal to T/4 at every horizon under the specified product game law. The one-step kernel assigns mass 1/4 to action 1 after history (0,1), and mass 3/4 after history (1,1).

\[
(\forall T\in\mathbb N,\ E_T^K=T/4)\ \land\ \kappa_1(\mathrm{oneHistory}(0,1))(\{1\})=\tfrac14\ \land\ \kappa_1(\mathrm{oneHistory}(1,1))(\{1\})=\tfrac34.
\]

1. **Objects:** selectedSampler, its recursive generated actions, concrete product gameLaw, and decisionKernel.
2. **Quantifiers/order:** One selected sampler is fixed from the supporting existential header before every observation law and before all T; the target universally quantifies T in its first conjunct.
3. **Assumptions:** Closed target with the supplied concrete definitions; the supporting existential is supplied as a header, not a verified proof.
4. **Conclusion/metric:** All-horizon expected-fixed excess identity and two conditional-kernel mass values.
5. **Constants/indices/boundaries:** T=0 gives 0; positive T yields positive linear excess. E is real-valued, whereas kernel masses use ENNReal.
6. **Information/probability:** Independent uniform tape and entire iid observation stream; actual prior generated actions are fed back. Strict switch condition is 1<last action+last observation, so equality at (0,1) uses lowLaw and (1,1) uses highLaw.
7. **Excluded scope:** No no-regret conclusion, no per-path identity, and no freedom to select a new sampler per horizon or law. The supplied supporting header is not accepted as proved.

### C023

Repeating the first random coordinate at both rounds gives expected-fixed excess -1/4 for the actual strict-past mean predictor. Using the two distinct iid coordinates gives +1/4 for that same predictor construction.

\[
E_2\bigl(Y_t=\omega_0,\ p_t=\mathrm{meanPredict}((\omega_0)_{s\ge0},t)\bigr)=-\frac14,\qquad E_2\bigl(Y_t=\omega_t,\ p_t=\mathrm{meanPredict}(\omega,t)\bigr)=\frac14.
\]

1. **Objects:** Two observation processes on the same iidLaw probability space, each with its own actually induced mean predictor and expected-fixed benchmark.
2. **Quantifiers/order:** Closed conjunction comparing two fully specified processes.
3. **Assumptions:** No independence premise is imposed on the repeated-coordinate process.
4. **Conclusion/metric:** Signed expected-fixed excess values, negative in the repeated-coordinate case.
5. **Constants/indices/boundaries:** Horizon 2; initial prediction 1/2; after the first repeated observation the next mean equals it.
6. **Information/probability:** Repeated coordinates have identical marginals but are dependent; the other process uses independent coordinates. Ambient iidLaw alone does not make arbitrary derived coordinates independent.
7. **Excluded scope:** No assertion that expected-fixed excess is always nonnegative without the relevant information and independence conditions; not a hindsight-minimum metric.

### C024

The half-initialized predictor on the dyadic sequence meets the one-sided upper no-regret condition and its best-comparator regret divided by T tends ordinarily to zero. Nevertheless, normalized regret against the particular constant 0 has no real limit, so the ordinary-limit-based condition fails.

\[
U(d,p^{1/2})\ \land\ G_T^{1/2}(d)/T\to0\ \land\ \neg\exists a\in\mathbb R,\ R_T(d,p^{1/2},0)/T\to a\ \land\ \neg L(d,p^{1/2}).
\]

1. **Objects:** The fixed dyadic sequence, half-initialized predictor, U, G, comparator regret, and L.
2. **Quantifiers/order:** Four closed conjuncts. U expands to every feasible u and every positive epsilon eventually in T; the third negates existence of any real limit at u=0; L requires a nonpositive limit for every feasible u.
3. **Assumptions:** No added hypothesis.
4. **Conclusion/metric:** Success of the upper condition and best-regret ordinary zero limit, together with failure of a specific comparator's ordinary limit and failure of L.
5. **Constants/indices/boundaries:** Natural T→∞; T=0 uses totalized division; u=0 is feasible.
6. **Information/probability:** Deterministic strict-past prediction and full-prefix hindsight best comparator.
7. **Excluded scope:** Upper no-regret is not ordinary convergence of every comparator regret. Does not claim failure of limits for every comparator.

### C025

There exists one Boolean vector of length two whose path regret, averaged over a fair Boolean seed driving the specified constant-action seeded policy, is at least log(4)/6.

\[
\exists v\in\mathrm{Bool}^2,\quad \frac{\log4}{6}\le \int_b \mathrm{pathRegret}(\mathrm{seededPolicy}(b),v.\mathrm{toList})\,d\mathrm{coinMeasure}(b).
\]

1. **Objects:** Length-two Boolean vector, fair finite seed law, seededPolicy, and pathRegret against the empirical mean of the binary path.
2. **Quantifiers/order:** The vector exists outside the seed integral; one fixed witness must serve the seed average.
3. **Assumptions:** No additional premise; this is a closed existential for the fixed seeded policy family.
4. **Conclusion/metric:** A lower bound on seed-averaged path comparator regret.
5. **Constants/indices/boundaries:** Length 2 and positive constant log4/6. The list is newest-first; reversal restores chronological binary observations.
6. **Information/probability:** One seed selects constant action 0 or 1 for the entire run. causalPredict passes only the newest-first strict history, although this particular policy ignores it. Comparator is the hindsight empirical mean of the fixed binary sequence.
7. **Excluded scope:** No witness depending on the realized seed, no pointwise seed lower bound, no universal horizon or universal policy theorem, and no fixed-expected-minimum benchmark.

### C026

The second rational harmonic number, coerced to the reals, is 3/2 and is bounded above by 1+log 2.

\[
(H_2:\mathbb R)=\frac32,\qquad (H_2:\mathbb R)\le1+\log2,\qquad H_n=\sum_{i<n}\frac1{i+1}\in\mathbb Q.
\]

1. **Objects:** The rational harmonic sequence and its real coercion; real natural logarithm.
2. **Quantifiers/order:** Closed conjunction at index 2.
3. **Assumptions:** No extra premise.
4. **Conclusion/metric:** Exact value and logarithmic upper comparison.
5. **Constants/indices/boundaries:** Terms have denominators 1 and 2; no zero denominator; the target does not quantify n or state a horizon-zero case.
6. **Information/probability:** Deterministic numerical statement.
7. **Excluded scope:** No asymptotic claim or general harmonic inequality is supplied by this target alone.

### C027

The affine expression 5+3T after subtracting 3T is little-o of T. At T=0, the separately written normalized affine expression minus 3 equals -3 because real division by zero is totalized.

\[
T\mapsto(5+3T)-3T=o_{T\to\infty}(T\mapsto T),\qquad \frac{5+3\cdot0}{0}-3=-3.
\]

1. **Objects:** Real-valued functions of natural T and a separate closed real expression at zero.
2. **Quantifiers/order:** Conjunction of an asymptotic assertion and a zero-input equality.
3. **Assumptions:** No assumptions.
4. **Conclusion/metric:** Constant residual 5 has magnitude little-o of T; the totalized zero-horizon normalized expression equals -3.
5. **Constants/indices/boundaries:** Constants 5 and 3; natural-to-real coercion in the first clause; real zero in the second.
6. **Information/probability:** No stochastic model or information structure.
7. **Excluded scope:** Does not assert the zero-horizon normalized expression equals an asymptotic limit or that algebraic cancellation across division by T is valid at T=0.

## Completeness and remaining scope

All 27 proposed closed target types C001–C027 have been reconstructed individually in prose, LaTeX, and seven semantic slots. The supplied context suffices for these readings; no additional context is requested. No unresolved mathematical-notation ambiguity was identified. In particular, the supporting existential header explains what the selected sampler is chosen to satisfy; this report does not verify that header or infer proof evidence from its use. The equations and implications above describe the requested proposition types, not established theorem truth. No proof execution, compilation, source matching, source acceptance, or chapter acceptance was performed.

