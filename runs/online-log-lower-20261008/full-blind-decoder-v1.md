# Complete neutral reconstruction B001-B064

Actor: `/root/osd_blind`. Requested model: GPT-6 Astra; reasoning effort: medium; no escalation. Runtime model and effort are unattested. No human review, external review, or external-independence attestation is claimed.

Prior staged history is disclosed: this reused decoder has earlier neutral-packet experience in current-support/policy, scalar absolute-loss, linearization, optimal-step, unit-scaling, foundations, sharp-prefix, state, regret-domain and an earlier staged lower-bound interface. That prior exposure remains inherited context; this is not a first-exposure decoder. For THIS reconstruction only full-neutral-packet-v2.lean and full-neutral-input-v2.json were read. No earlier packet, map, source, public module, source verdict or proof body was reread or consulted. The report below is based on the newly supplied full packet, with all 64 targets separately decoded.

The manifest declares closed target types and absent proofs. The actual text uses “def B... : Prop := ...”: these are universally quantified proposition descriptions (or closed tests), not proofs of the described propositions. The requested typechecking status is not independently verified by this decoder; no compiler is run. No source, proof, or acceptance verdict is supplied.

## Context: all actual definitions

The following notation is exact and is used to make each target formula readable. All h,k used as history variables range over finite Boolean lists (k(h) instead denotes true count); T,t range over naturals; A,F,G are total real-valued list functions unless another type is stated; real scalar variables are explicitly described in each slot. Natural counts in real formulas are coerced to real. In displayed numeric lists, 1 abbreviates true and 0 false; these are still Boolean lists. V_T is the finite type List.Vector Bool T, and F(v), w(v), R_A(v) abbreviate evaluation on v.toList, not a change of domain.

The four shared definitions are:
\[
r(\ell,p,u,T)=\sum_{t<T}\ell_t(p_t)-\sum_{t<T}\ell_t(u),\qquad
m(y,n)=\frac{\sum_{t<n}y_t}{n}.
\]
Here X is arbitrary, \(\ell:\mathbb N\to X\to\mathbb R\), \(p:\mathbb N\to X\), \(u:X\), and \(y:\mathbb N\to\mathbb R\). The comparator u is fixed across the second sum. Empty sums and totalized real division give m(y,0)=0. No infimum or absolute value is built into r.

P(arms,p) means \(\forall x\in arms,\ p(x)\ge0\) AND \(\sum_{x\in arms}p(x)=1\), with no requirement outside arms. With a measurable space on X,
\[
\operatorname{law}(arms,p)=\sum_{x\in arms}\operatorname{ENNReal.ofReal}(p(x))\,\delta_x.
\]
This is defined without P; negative weights would be truncated by ofReal. A normalized probability assertion requires the appropriate conditions, not the name “law.”

The twelve numbered context definitions are:

1. \(q(h)=f1(h)=(k(h)+1)/(n(h)+2)\), where \(k(h)=h.count(true)\) and \(n(h)=h.length\).
2. \(w(h)=f2(h)\), with \(w([])=1\) and
\[
w(b::h)=w(h)\bigl(\text{if }b\text{ then }q(h)\text{ else }1-q(h)\bigr).
\]
The head b is the newest bit, h the older history.
3. \(y^B_h(t)=f3(h,t)=(h.reverse[t]?).getD(false)\): chronological oldest-first stream, with false outside the finite list.
4. \(Y_h(t)=f4(h,t)=\mathbf1_{\{y^B_h(t)=true\}}\): real zero/one stream, including zero out of range.
5. \(x_t(A,y)=f5(A,y,t)=A([y_{t-1},\ldots,y_0])\): reverse of the chronological strict prefix, empty at t=0. The current y_t is not passed.
6. \(R_A(h)=f6(A,h)\):
\[
R_A(h)=r\bigl((t,x)\mapsto(x-Y_h(t))^2,\ (t\mapsto x_t(A,y^B_h)),\
\mu_h,\ n(h)\bigr),\qquad \mu_h=m(Y_h,n(h)).
\]
Thus it is signed actual-path regret against the empirical mean of the SAME whole sequence. It is neither loss against the changing online q(h) nor against an independently chosen sequence.
7. \(E_T[F]=f7(T,F)=\sum_{v\in V_T}w(v)F(v)\): a finite real weighted functional, defined without any normalization or measure input.
8. \(\nu_T=f8(T)=\operatorname{law}(\mathrm{univ}_{V_T},v\mapsto w(v))\), requiring a measurable-space instance on V_T. B007/B008 also require measurable singletons. The notation \(\mathsf M_T,\mathsf S_T\) in formulas denotes these exact two instances.
9. \(L_A(h)=f9(A,h)=\sum_{t<n(h)}(x_t(A,y^B_h)-Y_h(t))^2\): actual learner cumulative loss.
10. \(C(h)=f10(h)=\sum_{t<n(h)}(\mu_h-Y_h(t))^2\): full-sequence hindsight cumulative loss.
11. \(\nu=f11=\operatorname{law}(\mathrm{univ}_{Bool},b\mapsto1/2)\): specified two-atom seed measure.
12. \(A^b(h)=f12(b,h)=\mathbf1_b\): fixed seed-dependent predictor, ignoring h. One seed b defines one constant predictor across the whole sequence; it is not resampled by this definition.

Also let \(M_T=E_T[k]\), \(Q_T=E_T[k^2]\), and \(H_n=\sum_{j=1}^{n}1/j\), the real coercion of harmonic(n). H_0=0. This Q_T notation is a moment, not an additional premise.

For the random-seed statements define the fully expanded shorthand \(\mathcal C(\Omega,\mu,A)\): \(\Omega:\mathrm{Type}\ u\) has its supplied measurable space; \(\mu\) is a measure with IsProbabilityMeasure \(\mu\); \(A:\Omega\to List(Bool)\to\mathbb R\); for EVERY history h, \(\omega\mapsto A(\omega,h)\) is measurable; and for EVERY \(\omega,h\), \(A(\omega,h)\in[0,1]\). This is pointwise all-history boundedness, not merely almost-everywhere or on-path boundedness. \(A_\omega(h)=A(\omega,h)\). B045 requires only the measurable-space and per-history measurability part, not \(\mathcal C\)'s probability/boundedness parts.

## Semantic safeguards

Finite functional E_T is always finite algebraically for arbitrary real F on these finitely many vectors. P is the separate normalized-weight predicate; \(\nu_T\) is the measure construction; B007 certifies probability and B008 identifies its integral with E_T. Those concepts are not interchangeable by definition.

For arbitrary seed spaces the Bochner integral notation is totalized; merely writing an integral does not assert integrability or a meaningful expectation of a nonintegrable function. B045 and B046 separately describe measurability and integrability; B047/B048 have their full conditions. No undefined integral fallback is being used as an unstated proof device in this reconstruction.

The mathematical stream f3(h) exists for every natural index, but f5's exact actual input is the strict past in newest-first order. Full hindsight is used only by the comparator \(\mu_h\), not by the learner's explicit input. No computability, finite-query, stochastic independence of external parameter construction, or separate joint seed-target law is supplied. A fixed sequence outside the seed integral is the precise quantifier feature of the random-seed conclusions.

## Target reconstructions

Each target has seven semantic slots, plus an explicit LaTeX restatement in its conclusion slot. Slot 2 specifies the quantifier order and slot 3 every premise; thus no unmentioned regularity or positivity hypotheses are to be read into the formulas. A statement labeled “closed” has no free universal parameters beyond its displayed internal quantifiers.

## B001

1. **Objects.** h: finite Boolean list
2. **Quantifier order.** ∀h.
3. **Assumptions.** None.
4. **Conclusion.** 0<q(h)<1: the smoothed count ratio is strictly interior.

   \[
   \forall h,\quad 0<q(h)<1.
   \]

5. **Constants and indices.** q=(k+1)/(n+2); strict endpoints.
6. **Probability and feedback.** Only supplied history counts are used.
7. **Exclusions and boundaries.** Empty h gives 1/2; all-equal histories remain interior.

## B002

1. **Objects.** h and its two newest-bit extensions
2. **Quantifier order.** ∀h.
3. **Assumptions.** None.
4. **Conclusion.** w(false::h)+w(true::h)=w(h): children preserve parent mass.

   \[
   \forall h,\quad w(\mathrm{false}::h)+w(\mathrm{true}::h)=w(h).
   \]

5. **Constants and indices.** Children have length n+1.
6. **Probability and feedback.** New bit is the head; h is the older history.
7. **Exclusions and boundaries.** Empty parent allowed; this identity alone is not P.

## B003

1. **Objects.** h and real weight w(h)
2. **Quantifier order.** ∀h.
3. **Assumptions.** None.
4. **Conclusion.** 0≤w(h): every list weight is nonnegative.

   \[
   \forall h,\quad 0\le w(h).
   \]

5. **Constants and indices.** Non-strict zero lower bound.
6. **Probability and feedback.** A finite weight, not yet a normalization assertion.
7. **Exclusions and boundaries.** Includes empty h with weight 1; strictness is separately B041.

## B004

1. **Objects.** T∈N; F:List Bool→R
2. **Quantifier order.** ∀T ∀F.
3. **Assumptions.** None.
4. **Conclusion.** Σ_{v∈V_{T+1}}F(v)=Σ_{v∈V_T}[F(false::v)+F(true::v)]: enumerate all lists by newest head.

   \[
   \forall T,F,\quad \sum_{v\in V_{T+1}}F(v)=\sum_{v\in V_T}\bigl(F(\mathrm{false}::v)+F(\mathrm{true}::v)\bigr).
   \]

5. **Constants and indices.** Unweighted sums; no factor or w.
6. **Probability and feedback.** Pure finite enumeration, not expectation.
7. **Exclusions and boundaries.** T=0 valid; F arbitrary, including signed.

## B005

1. **Objects.** T and length-T weights
2. **Quantifier order.** ∀T∈N.
3. **Assumptions.** None.
4. **Conclusion.** Σ_{v∈V_T}w(v)=1: fixed-length total weight is one.

   \[
   \forall T,\quad\sum_{v\in V_T}w(v)=1.
   \]

5. **Constants and indices.** Exact unit total.
6. **Probability and feedback.** Finite normalization without measure-space inputs.
7. **Exclusions and boundaries.** T=0 has the single empty vector.

## B006

1. **Objects.** T and predicate P on V_T
2. **Quantifier order.** ∀T∈N.
3. **Assumptions.** None.
4. **Conclusion.** P(univ,w): ∀v∈V_T, w(v)≥0 and Σ_{v∈V_T}w(v)=1.

   \[
   \forall T,\quad P(V_T,w).
   \]

5. **Constants and indices.** Both nonnegative and unit-sum conditions.
6. **Probability and feedback.** Discrete normalized-weight predicate, not an integral.
7. **Exclusions and boundaries.** Includes T=0; no condition on other list lengths.

## B007

1. **Objects.** T, measurable space and measurable singletons on V_T
2. **Quantifier order.** ∀T ∀ supplied measurable-space/singleton instances.
3. **Assumptions.** Those two instances.
4. **Conclusion.** IsProbabilityMeasure(ν_T): ν_T has mass one.

   \[
   \forall T\ [\mathsf M_T]\ [\mathsf S_T],\quad\operatorname{IsProbabilityMeasure}(\nu_T).
   \]

5. **Constants and indices.** ν_T=f8(T); weights converted by ofReal.
6. **Probability and feedback.** Probability assertion for this particular atomic measure.
7. **Exclusions and boundaries.** T=0 valid; arbitrary law(arms,p) is not automatically normalized.

## B008

1. **Objects.** T, same measurable instances, F:List Bool→R
2. **Quantifier order.** ∀T ∀instances ∀F.
3. **Assumptions.** MeasurableSpace and MeasurableSingletonClass on V_T; no separate F premise.
4. **Conclusion.** ∫_{V_T} F(v) dν_T=E_T[F]: integral equals finite weighted functional.

   \[
   \forall T\ [\mathsf M_T]\ [\mathsf S_T]\ \forall F,\quad\int F(v)\,d\nu_T(v)=E_T[F].
   \]

5. **Constants and indices.** Identical weights w; values at length T only.
6. **Probability and feedback.** Finite measurable-singleton domain supports the stated real-integral identity.
7. **Exclusions and boundaries.** T=0 gives F([]); not an arbitrary infinite-domain integrability assertion.

## B009

1. **Objects.** T; real list functions F,G
2. **Quantifier order.** ∀T ∀F,G.
3. **Assumptions.** ∀h, n(h)=T ⇒ F(h)=G(h).
4. **Conclusion.** E_T[F]=E_T[G]: equal fixed-length values give equal weighted sums.

   \[
   \forall T,F,G,\quad(\forall h,\ n(h)=T\Rightarrow F(h)=G(h))\Rightarrow E_T[F]=E_T[G].
   \]

5. **Constants and indices.** No agreement required on other lengths.
6. **Probability and feedback.** Pointwise finite-functional extensionality.
7. **Exclusions and boundaries.** T=0 requires agreement at []; no probabilistic assumption.

## B010

1. **Objects.** T and real constant c
2. **Quantifier order.** ∀T ∀c∈R.
3. **Assumptions.** None.
4. **Conclusion.** E_T[h↦c]=c: constants are preserved.

   \[
   \forall T,c,\quad E_T[c]=c.
   \]

5. **Constants and indices.** Exact factor 1 from unit mass.
6. **Probability and feedback.** Finite weighted functional, without measurability input.
7. **Exclusions and boundaries.** c zero or negative and T=0 allowed.

## B011

1. **Objects.** T and real list functions F,G
2. **Quantifier order.** ∀T ∀F,G.
3. **Assumptions.** None.
4. **Conclusion.** E_T[F+G]=E_T[F]+E_T[G]: additivity.

   \[
   \forall T,F,G,\quad E_T[F+G]=E_T[F]+E_T[G].
   \]

5. **Constants and indices.** Pointwise addition, exact equality.
6. **Probability and feedback.** Finite sum algebra.
7. **Exclusions and boundaries.** No positivity or integrability premise; T=0 allowed.

## B012

1. **Objects.** T and real list functions F,G
2. **Quantifier order.** ∀T ∀F,G.
3. **Assumptions.** None.
4. **Conclusion.** E_T[F−G]=E_T[F]−E_T[G]: subtraction is preserved.

   \[
   \forall T,F,G,\quad E_T[F-G]=E_T[F]-E_T[G].
   \]

5. **Constants and indices.** Signed subtraction, no absolute value.
6. **Probability and feedback.** Finite sum algebra.
7. **Exclusions and boundaries.** Arbitrary signed functions; T=0 allowed.

## B013

1. **Objects.** T, real c, real list function F
2. **Quantifier order.** ∀T ∀c ∀F.
3. **Assumptions.** None.
4. **Conclusion.** E_T[cF]=c E_T[F]: scalar homogeneity.

   \[
   \forall T,c,F,\quad E_T[cF]=cE_T[F].
   \]

5. **Constants and indices.** c multiplies every value.
6. **Probability and feedback.** Finite real sum, no probability requirement in the type.
7. **Exclusions and boundaries.** c may be negative or zero.

## B014

1. **Objects.** T, real list function F, real divisor c
2. **Quantifier order.** ∀T ∀F ∀c.
3. **Assumptions.** None.
4. **Conclusion.** E_T[F/c]=E_T[F]/c: totalized scalar division commutes with finite weighting.

   \[
   \forall T,F,c,\quad E_T[F/c]=E_T[F]/c.
   \]

5. **Constants and indices.** Same divisor c everywhere.
6. **Probability and feedback.** Algebraic equality, not a bound.
7. **Exclusions and boundaries.** c=0 explicitly permitted: total real division makes both sides zero.

## B015

1. **Objects.** T and real list function F
2. **Quantifier order.** ∀T ∀F.
3. **Assumptions.** None.
4. **Conclusion.** E_{T+1}[F]=E_T[h↦(1−q(h))F(false::h)+q(h)F(true::h)]: weighted extension recursion.

   \[
   \forall T,F,\quad E_{T+1}[F]=E_T[h\mapsto(1-q(h))F(\mathrm{false}::h)+q(h)F(\mathrm{true}::h)].
   \]

5. **Constants and indices.** Complementary weights, no 1/2 replacement.
6. **Probability and feedback.** A next-bit conditional weighting description for this construction.
7. **Exclusions and boundaries.** T=0 valid; no independent-bit assumption.

## B016

1. **Objects.** T; M_T=E_T[k]
2. **Quantifier order.** ∀T∈N.
3. **Assumptions.** None.
4. **Conclusion.** M_{T+1}=M_T+(M_T+1)/(T+2): first-count-moment recursion.

   \[
   \forall T,\quad M_{T+1}=M_T+\frac{M_T+1}{T+2}.
   \]

5. **Constants and indices.** Offsets +1 and +2 exact.
6. **Probability and feedback.** Moment of the defined dependent-history weights.
7. **Exclusions and boundaries.** T=0 valid; denominator always positive.

## B017

1. **Objects.** T; M_T=E_T[k], Q_T=E_T[k²]
2. **Quantifier order.** ∀T∈N.
3. **Assumptions.** None.
4. **Conclusion.** Q_{T+1}=Q_T+(2Q_T+3M_T+1)/(T+2): second raw moment recursion.

   \[
   \forall T,\quad Q_{T+1}=Q_T+\frac{2Q_T+3M_T+1}{T+2}.
   \]

5. **Constants and indices.** Coefficients 2,3,1; denominator T+2.
6. **Probability and feedback.** Square inside expectation, not squared mean.
7. **Exclusions and boundaries.** T=0 valid; no binomial independence premise.

## B018

1. **Objects.** T and count k
2. **Quantifier order.** ∀T∈N.
3. **Assumptions.** None.
4. **Conclusion.** E_T[k]=T/2: expected number of true bits is half T.

   \[
   \forall T,\quad E_T[k]=T/2.
   \]

5. **Constants and indices.** Natural T coerced to real.
6. **Probability and feedback.** Finite weighted first moment.
7. **Exclusions and boundaries.** T=0 gives zero; does not establish independent fair bits.

## B019

1. **Objects.** T and k²
2. **Quantifier order.** ∀T∈N.
3. **Assumptions.** None.
4. **Conclusion.** E_T[k²]=T(2T+1)/6: exact second raw moment.

   \[
   \forall T,\quad E_T[k^2]=T(2T+1)/6.
   \]

5. **Constants and indices.** Denominator 6, not a variance.
6. **Probability and feedback.** Finite weighted count moment.
7. **Exclusions and boundaries.** T=0 gives zero; not the independent-binomial second moment.

## B020

1. **Objects.** T and q(h)(1−q(h))
2. **Quantifier order.** ∀T∈N.
3. **Assumptions.** None.
4. **Conclusion.** E_T[q(1−q)]=(T+3)/(6(T+2)).

   \[
   \forall T,\quad E_T[q(1-q)]=\frac{T+3}{6(T+2)}.
   \]

5. **Constants and indices.** Offsets +3,+2 and factor 6.
6. **Probability and feedback.** Moment of history-dependent next-bit parameter.
7. **Exclusions and boundaries.** At T=0 value 1/4; no positive-horizon restriction.

## B021

1. **Objects.** A:List Bool→R; Boolean streams y,z; t∈N
2. **Quantifier order.** ∀A ∀y,z ∀t.
3. **Assumptions.** ∀i<t, y_i=z_i.
4. **Conclusion.** x_t(A,y)=x_t(A,z): actual predictions agree under strict-prefix agreement.

   \[
   \forall A,y,z,t,\quad(\forall i<t,\ y_i=z_i)\Rightarrow x_t(A,y)=x_t(A,z).
   \]

5. **Constants and indices.** A receives [y_{t−1},…,y_0].
6. **Probability and feedback.** No current or future bit is passed; A fixed on both sides.
7. **Exclusions and boundaries.** At zero both A([]); no bound/measurability on A; external construction independence not asserted.

## B022

1. **Objects.** Nonempty list h; n=n(h), y=Y_h, mean μ_h
2. **Quantifier order.** ∀h with n>0; then ∀u∈[0,1].
3. **Assumptions.** n>0.
4. **Conclusion.** μ_h∈[0,1] ∧ ∀u∈[0,1], Σ_{t<n}(μ_h−y_t)²≤Σ_{t<n}(u−y_t)²: feasible hindsight mean minimizes these losses.

   \[
   \forall h,\quad n(h)>0\Rightarrow\left[\mu_h\in[0,1]\ \land\ \forall u\in[0,1],\ \sum_{t<n(h)}(\mu_h-Y_h(t))^2\le\sum_{t<n(h)}(u-Y_h(t))^2\right].
   \]

5. **Constants and indices.** Single full-prefix comparator μ_h throughout.
6. **Probability and feedback.** Hindsight uses all targets; not available to earlier predictions.
7. **Exclusions and boundaries.** Empty list excluded; no uniqueness or all-real-u claim in this target.

## B023

1. **Objects.** h:List Bool and real x
2. **Quantifier order.** ∀h ∀x∈R.
3. **Assumptions.** None.
4. **Conclusion.** q(h)(1−q(h))≤(1−q(h))x²+q(h)(x−1)²: weighted one-step loss lower bound.

   \[
   \forall h,x,\quad q(h)(1-q(h))\le(1-q(h))x^2+q(h)(x-1)^2.
   \]

5. **Constants and indices.** Gap is (x−q(h))²; no half coefficient.
6. **Probability and feedback.** For a fixed past h and arbitrary real prediction.
7. **Exclusions and boundaries.** x need not be in [0,1]; empty h allowed.

## B024

1. **Objects.** Boolean b, list h, natural t
2. **Quantifier order.** ∀b ∀h ∀t.
3. **Assumptions.** t<n(h).
4. **Conclusion.** y^B_{b::h}(t)=y^B_h(t): older chronological bits unchanged.

   \[
   \forall b,h,t,\quad t<n(h)\Rightarrow y^B_{b::h}(t)=y^B_h(t).
   \]

5. **Constants and indices.** Strict t<n, not t=n.
6. **Probability and feedback.** Prepending newest bit appends it chronologically.
7. **Exclusions and boundaries.** For empty h no qualifying t; default tail values not claimed equal here.

## B025

1. **Objects.** Boolean b and list h
2. **Quantifier order.** ∀b ∀h.
3. **Assumptions.** None.
4. **Conclusion.** y^B_{b::h}(n(h))=b: new head is the last chronological target.

   \[
   \forall b,h,\quad y^B_{b::h}(n(h))=b.
   \]

5. **Constants and indices.** Index n, child length n+1.
6. **Probability and feedback.** Confirms newest-first storage order.
7. **Exclusions and boundaries.** For h=[] reads index zero; no default is used at this valid index.

## B026

1. **Objects.** Boolean b, list h, t∈N
2. **Quantifier order.** ∀b ∀h ∀t.
3. **Assumptions.** t<n(h).
4. **Conclusion.** Y_{b::h}(t)=Y_h(t): old real-indicator targets unchanged.

   \[
   \forall b,h,t,\quad t<n(h)\Rightarrow Y_{b::h}(t)=Y_h(t).
   \]

5. **Constants and indices.** Only earlier n indices.
6. **Probability and feedback.** Indicator version of chronological prefix preservation.
7. **Exclusions and boundaries.** No claim for t=n; empty h gives vacuous scope.

## B027

1. **Objects.** A:List Bool→R and h
2. **Quantifier order.** ∀A ∀h.
3. **Assumptions.** None.
4. **Conclusion.** x_{n(h)}(A,y^B_h)=A(h): reconstructing the whole past returns the same newest-first list to A.

   \[
   \forall A,h,\quad x_{n(h)}(A,y^B_h)=A(h).
   \]

5. **Constants and indices.** Time n is after n targets, before any default future target.
6. **Probability and feedback.** Exact strict-past identity, not use of hindsight comparator.
7. **Exclusions and boundaries.** Empty h gives A([]); A arbitrary.

## B028

1. **Objects.** A, Boolean b and list h
2. **Quantifier order.** ∀A ∀b ∀h.
3. **Assumptions.** None.
4. **Conclusion.** x_{n(h)}(A,y^B_{b::h})=A(h): prediction for newest bit depends only on older h.

   \[
   \forall A,b,h,\quad x_{n(h)}(A,y^B_{b::h})=A(h).
   \]

5. **Constants and indices.** Current target b at chronological n excluded.
6. **Probability and feedback.** Actual input ordering, not an independent prediction path.
7. **Exclusions and boundaries.** h=[] allowed; A(h) does not explicitly depend on b.

## B029

1. **Objects.** A and h; R=f6, L=f9, C=f10
2. **Quantifier order.** ∀A ∀h.
3. **Assumptions.** None.
4. **Conclusion.** R_A(h)=L_A(h)−C(h): regret decomposes into same-path learner loss minus same-sequence hindsight loss.

   \[
   \forall A,h,\quad R_A(h)=L_A(h)-C(h).
   \]

5. **Constants and indices.** Exact subtraction; same n terms.
6. **Probability and feedback.** No change of predictions or comparator between components.
7. **Exclusions and boundaries.** Empty h all zero; signed R need not be nonnegative.

## B030

1. **Objects.** A, Boolean b, history h
2. **Quantifier order.** ∀A ∀b ∀h.
3. **Assumptions.** None.
4. **Conclusion.** L_A(b::h)=L_A(h)+(A(h)−1_b)²: append the actual current loss.

   \[
   \forall A,b,h,\quad L_A(b::h)=L_A(h)+(A(h)-\mathbf1_b)^2.
   \]

5. **Constants and indices.** New chronological index n(h); 1_b is 0 or 1.
6. **Probability and feedback.** Same A and old path; current prediction A(h) before b is used.
7. **Exclusions and boundaries.** Empty history allowed; no prediction bound required.

## B031

1. **Objects.** Boolean list h
2. **Quantifier order.** ∀h.
3. **Assumptions.** None.
4. **Conclusion.** Σ_{t<n(h)}Y_h(t)=k(h): chronological indicator sum equals true count.

   \[
   \forall h,\quad\sum_{t<n(h)}Y_h(t)=k(h).
   \]

5. **Constants and indices.** No extra tail/default contribution.
6. **Probability and feedback.** Finite reversal preserves counts.
7. **Exclusions and boundaries.** Empty h gives 0=0.

## B032

1. **Objects.** Boolean list h and natural t
2. **Quantifier order.** ∀h ∀t.
3. **Assumptions.** None.
4. **Conclusion.** Y_h(t)²=Y_h(t): binary indicators are idempotent.

   \[
   \forall h,t,\quad Y_h(t)^2=Y_h(t).
   \]

5. **Constants and indices.** All natural t, not only valid indices.
6. **Probability and feedback.** Includes false/zero default outside list.
7. **Exclusions and boundaries.** Empty and out-of-range queries yield zero; no probability required.

## B033

1. **Objects.** Nonempty list h, count k and length n
2. **Quantifier order.** ∀h with n>0.
3. **Assumptions.** n>0.
4. **Conclusion.** C(h)=k(h)−k(h)²/n(h): explicit hindsight squared loss.

   \[
   \forall h,\quad n(h)>0\Rightarrow C(h)=k(h)-k(h)^2/n(h).
   \]

5. **Constants and indices.** Real division by positive n.
6. **Probability and feedback.** Mean of same decoded binary sequence.
7. **Exclusions and boundaries.** Empty case excluded; totalized division does not remove this premise.

## B034

1. **Objects.** Positive T and hindsight loss C
2. **Quantifier order.** ∀T with T>0.
3. **Assumptions.** T>0.
4. **Conclusion.** E_T[C]=(T−1)/6: exact expected hindsight loss.

   \[
   \forall T,\quad T>0\Rightarrow E_T[C]=(T-1)/6.
   \]

5. **Constants and indices.** Real T−1, denominator 6.
6. **Probability and feedback.** Weighted full-sequence comparator loss, not learner loss.
7. **Exclusions and boundaries.** T=1 gives zero; T=0 excluded since RHS would −1/6.

## B035

1. **Objects.** T and real functions F,G on lists
2. **Quantifier order.** ∀T ∀F,G.
3. **Assumptions.** ∀h, n(h)=T ⇒ F(h)≤G(h).
4. **Conclusion.** E_T[F]≤E_T[G]: finite weighting preserves this order.

   \[
   \forall T,F,G,\quad(\forall h,\ n(h)=T\Rightarrow F(h)\le G(h))\Rightarrow E_T[F]\le E_T[G].
   \]

5. **Constants and indices.** Length-T pointwise comparison only.
6. **Probability and feedback.** Uses nonnegative weights, no integral assumptions.
7. **Exclusions and boundaries.** Arbitrary signs allowed; T=0 valid.

## B036

1. **Objects.** A and natural T
2. **Quantifier order.** ∀A ∀T.
3. **Assumptions.** None.
4. **Conclusion.** E_{T+1}[L_A]=E_T[L_A]+E_T[h↦(1−q(h))A(h)²+q(h)(A(h)−1)²]: cumulative-loss recursion.

   \[
   \forall A,T,\quad E_{T+1}[L_A]=E_T[L_A]+E_T[h\mapsto(1-q(h))A(h)^2+q(h)(A(h)-1)^2].
   \]

5. **Constants and indices.** Exactly one added current conditional loss.
6. **Probability and feedback.** Current A(h) shared across both possible next bits.
7. **Exclusions and boundaries.** A unbounded allowed, finite sums remain finite; T=0 valid.

## B037

1. **Objects.** A and T
2. **Quantifier order.** ∀A ∀T.
3. **Assumptions.** None.
4. **Conclusion.** E_T[L_A]+(T+3)/(6(T+2))≤E_{T+1}[L_A]: positive expected increment lower bound.

   \[
   \forall A,T,\quad E_T[L_A]+\frac{T+3}{6(T+2)}\le E_{T+1}[L_A].
   \]

5. **Constants and indices.** Same fraction as B020, non-strict inequality.
6. **Probability and feedback.** One-step weighted loss comparison on actual A(h).
7. **Exclusions and boundaries.** T=0 valid; no interval bound on A.

## B038

1. **Objects.** Natural T; harmonic H_n
2. **Quantifier order.** ∀T∈N.
3. **Assumptions.** None.
4. **Conclusion.** Σ_{t<T}(t+3)/(6(t+2))=T/6+(H_{T+1}−1)/6.

   \[
   \forall T,\quad\sum_{t<T}\frac{t+3}{6(t+2)}=\frac T6+\frac{H_{T+1}-1}{6}.
   \]

5. **Constants and indices.** Harmonic index T+1; subtract 1 exactly.
6. **Probability and feedback.** Scalar finite sum identity, not probabilistic.
7. **Exclusions and boundaries.** T=0 both sides zero because H_1=1.

## B039

1. **Objects.** A and T
2. **Quantifier order.** ∀A ∀T.
3. **Assumptions.** None.
4. **Conclusion.** Σ_{t<T}(t+3)/(6(t+2))≤E_T[L_A]: total expected learner-loss lower bound.

   \[
   \forall A,T,\quad\sum_{t<T}\frac{t+3}{6(t+2)}\le E_T[L_A].
   \]

5. **Constants and indices.** No comparator subtraction yet.
6. **Probability and feedback.** Actual strict-past A path inside L_A.
7. **Exclusions and boundaries.** T=0 both sides zero; no A bound needed.

## B040

1. **Objects.** A and positive T
2. **Quantifier order.** ∀A ∀T>0.
3. **Assumptions.** T>0 only.
4. **Conclusion.** H_{T+1}/6≤E_T[R_A]: finite weighted regret lower bound.

   \[
   \forall A,T,\quad T>0\Rightarrow H_{T+1}/6\le E_T[R_A].
   \]

5. **Constants and indices.** Harmonic T+1, factor 1/6; not averaged by T.
6. **Probability and feedback.** Same actual predictions and full-sequence empirical-mean comparator.
7. **Exclusions and boundaries.** T=0 excluded: RHS zero vs H_1/6 positive; not every sequence or every regret must satisfy bound.

## B041

1. **Objects.** List h and weight w(h)
2. **Quantifier order.** ∀h.
3. **Assumptions.** None.
4. **Conclusion.** 0<w(h): every finite list has strictly positive weight.

   \[
   \forall h,\quad0<w(h).
   \]

5. **Constants and indices.** Strict positivity, stronger than B003.
6. **Probability and feedback.** All finite sequences in this construction have positive support.
7. **Exclusions and boundaries.** Empty weight 1; no uniform positive lower constant across all lengths.

## B042

1. **Objects.** Real x,y
2. **Quantifier order.** ∀x,y∈R.
3. **Assumptions.** x∈[0,1], y∈[0,1].
4. **Conclusion.** (x−y)²∈[0,1]: squared deviation is between zero and one.

   \[
   \forall x,y\in\mathbb R,\quad[x\in[0,1]\land y\in[0,1]]\Rightarrow(x-y)^2\in[0,1].
   \]

5. **Constants and indices.** Inclusive endpoints, coefficient 1.
6. **Probability and feedback.** Deterministic pointwise bound.
7. **Exclusions and boundaries.** Endpoints may attain 1; no claim for arbitrary unbounded x,y.

## B043

1. **Objects.** T and real sequences p,y
2. **Quantifier order.** ∀T ∀p,y.
3. **Assumptions.** ∀t<T, p_t∈[0,1] and ∀t<T, y_t∈[0,1].
4. **Conclusion.** Σ_{t<T}(p_t−y_t)²∈[0,T]: total loss bounded by count.

   \[
   \forall T,p,y,\quad[(\forall t<T,p_t\in[0,1])\land(\forall t<T,y_t\in[0,1])]\Rightarrow\sum_{t<T}(p_t-y_t)^2\in[0,T].
   \]

5. **Constants and indices.** Real-coerced upper T.
6. **Probability and feedback.** Arbitrary deterministic sequences, no causality hypothesis.
7. **Exclusions and boundaries.** T=0 gives zero; later values unrestricted.

## B044

1. **Objects.** A and h
2. **Quantifier order.** ∀A ∀h.
3. **Assumptions.** ∀k:List Bool, A(k)∈[0,1].
4. **Conclusion.** |R_A(h)|≤n(h): actual regret has absolute finite bound.

   \[
   \forall A,h,\quad(\forall k,A(k)\in[0,1])\Rightarrow |R_A(h)|\le n(h).
   \]

5. **Constants and indices.** Absolute value, not just one-sided upper bound.
6. **Probability and feedback.** All-history A bound plus finite hindsight loss.
7. **Exclusions and boundaries.** Includes empty h with zero; bounds every history, not merely one path.

## B045

1. **Objects.** Measurable space Ω, family A:Ω→List Bool→R, fixed h
2. **Quantifier order.** ∀Ω ∀A satisfying condition ∀h.
3. **Assumptions.** ∀k, ω↦A(ω,k) measurable.
4. **Conclusion.** ω↦R_{A_ω}(h) is measurable.

   \[
   \forall\Omega\ [\mathsf M_\Omega]\ \forall A,h,\quad(\forall k,\operatorname{Measurable}(A(\cdot,k)))\Rightarrow\operatorname{Measurable}(\omega\mapsto R_{A_\omega}(h)).
   \]

5. **Constants and indices.** h is fixed; no measure μ needed.
6. **Probability and feedback.** Finite operations on actual per-seed strict-past predictions.
7. **Exclusions and boundaries.** No interval boundedness or integrability conclusion required here.

## B046

1. **Objects.** Probability space (Ω,μ), family A, fixed h
2. **Quantifier order.** ∀Ω,μ,A satisfying conditions ∀h.
3. **Assumptions.** μ probability; ∀k A(·,k) measurable; ∀ω,k A(ω,k)∈[0,1].
4. **Conclusion.** Integrable(ω↦R_{A_ω}(h),μ): actual seed-regret function is Bochner integrable.

   \[
   \forall\Omega,\mu,A,h,\quad\mathcal C(\Omega,\mu,A)\Rightarrow\operatorname{Integrable}(\omega\mapsto R_{A_\omega}(h),\mu).
   \]

5. **Constants and indices.** Finite bound n(h), no positive-length restriction.
6. **Probability and feedback.** Separately establishes legitimate integral meaning, beyond total integral notation.
7. **Exclusions and boundaries.** Empty h zero integrable; pointwise all-history bound, not only a.e.; no nonintegrable fallback being used.

## B047

1. **Objects.** Probability (Ω,μ), measurable bounded A, positive T
2. **Quantifier order.** ∀Ω,μ,A satisfying assumptions ∀T>0, THEN ∃v∈V_T.
3. **Assumptions.** μ probability; each A(·,h) measurable; every A(ω,h)∈[0,1]; T>0.
4. **Conclusion.** ∃v∈V_T, H_{T+1}/6≤∫_Ω R_{A_ω}(v)dμ(ω): one fixed sequence has large seed-averaged regret.

   \[
   \forall\Omega,\mu,A,T,\quad[\mathcal C(\Omega,\mu,A)\land T>0]\Rightarrow\exists v\in V_T,\quad H_{T+1}/6\le\int R_{A_\omega}(v)\,d\mu(\omega).
   \]

5. **Constants and indices.** Harmonic T+1, divisor 6.
6. **Probability and feedback.** Witness v outside seed integral; same A_ω trajectory inside R; integrability supported by stated conditions/B046.
7. **Exclusions and boundaries.** Not ∀ω∃v, not per-seed guarantee, not one v for all learners/horizons. No separate joint seed-target independence predicate supplied; T=0 excluded.

## B048

1. **Objects.** Same probability family as B047 and positive T
2. **Quantifier order.** ∀Ω,μ,A satisfying assumptions ∀T>0, THEN ∃v∈V_T.
3. **Assumptions.** μ probability; per-history measurability; pointwise all-seed/history [0,1] bound; T>0.
4. **Conclusion.** ∃v∈V_T, log(T+2)/6≤∫_Ω R_{A_ω}(v)dμ(ω).

   \[
   \forall\Omega,\mu,A,T,\quad[\mathcal C(\Omega,\mu,A)\land T>0]\Rightarrow\exists v\in V_T,\quad\log(T+2)/6\le\int R_{A_\omega}(v)\,d\mu(\omega).
   \]

5. **Constants and indices.** Natural log, real T+2, divisor 6.
6. **Probability and feedback.** Fixed witness before averaging over seed; hindsight comparator from same v.
7. **Exclusions and boundaries.** No a.s./high-probability claim, adaptive seed-specific target, average-by-T or anytime assertion; T=0 excluded.

## B049

1. **Objects.** Fixed h=[true,true,true]
2. **Quantifier order.** Closed numerical conjunction.
3. **Assumptions.** None.
4. **Conclusion.** q([true,true,true])=4/5 ∧ q([true,true,true])∈(0,1).

   \[
   q([1,1,1])=4/5\ \land\ q([1,1,1])\in(0,1).
   \]

5. **Constants and indices.** k=3,n=3.
6. **Probability and feedback.** Numerical ratio check, no universally quantified performance result.
7. **Exclusions and boundaries.** All-true history does not force q=1.

## B050

1. **Objects.** Four fixed length-two lists
2. **Quantifier order.** Closed conjunction.
3. **Assumptions.** None.
4. **Conclusion.** w([true,true])=1/3 ∧ w([false,false])=1/3 ∧ w([true,false])=1/6 ∧ w([false,true])=1/6.

   \[
   w([1,1])=1/3\ \land\ w([0,0])=1/3\ \land\ w([1,0])=1/6\ \land\ w([0,1])=1/6.
   \]

5. **Constants and indices.** Exact four real weights.
6. **Probability and feedback.** Newest-first list interpretation retained; weights not independent fair-coin 1/4.
7. **Exclusions and boundaries.** Does not alone assert symmetry/all-length formula beyond these lists.

## B051

1. **Objects.** Lengths zero and two
2. **Quantifier order.** Closed conjunction.
3. **Assumptions.** None.
4. **Conclusion.** Σ_{v∈V_0}w(v)=1 ∧ Σ_{v∈V_2}w(v)=1.

   \[
   \sum_{v\in V_0}w(v)=1\ \land\ \sum_{v\in V_2}w(v)=1.
   \]

5. **Constants and indices.** Unit total at both specified lengths.
6. **Probability and feedback.** Finite normalization canaries.
7. **Exclusions and boundaries.** Empty vector present at T=0; no empty sample space.

## B052

1. **Objects.** T=2 first and second count moments
2. **Quantifier order.** Closed conjunction.
3. **Assumptions.** None.
4. **Conclusion.** E_2[k]=1 ∧ E_2[k²]=5/3.

   \[
   E_2[k]=1\ \land\ E_2[k^2]=5/3.
   \]

5. **Constants and indices.** Second raw moment 5/3, not squared mean 1.
6. **Probability and feedback.** Finite weighted numerical tests.
7. **Exclusions and boundaries.** Does not itself quantify all T.

## B053

1. **Objects.** T=2 and q(1−q)
2. **Quantifier order.** Closed numerical statement.
3. **Assumptions.** None.
4. **Conclusion.** E_2[q(1−q)]=5/24.

   \[
   E_2[q(1-q)]=5/24.
   \]

5. **Constants and indices.** Exact fraction.
6. **Probability and feedback.** Finite functional, no extra sampled object.
7. **Exclusions and boundaries.** No asymptotic approximation or inequality.

## B054

1. **Objects.** A=q; lists [true,false] and [false,false]; time 1
2. **Quantifier order.** Closed equality.
3. **Assumptions.** None.
4. **Conclusion.** x_1(q,y^B_[true,false])=x_1(q,y^B_[false,false]): same prediction from same oldest false bit.

   \[
   x_1(q,y^B_{[1,0]})=x_1(q,y^B_{[0,0]}).
   \]

5. **Constants and indices.** Both equal q([false])=1/3.
6. **Probability and feedback.** Current chronological bits differ, yet strict-past input agrees.
7. **Exclusions and boundaries.** Not full-list equality or equal predictions after observing the differing current bit.

## B055

1. **Objects.** A=q, list [true,true,false], time 2
2. **Quantifier order.** Closed numerical statement.
3. **Assumptions.** None.
4. **Conclusion.** x_2(q,y^B_[true,true,false])=1/2.

   \[
   x_2(q,y^B_{[1,1,0]})=1/2.
   \]

5. **Constants and indices.** Chronological past [false,true], presented to A as [true,false].
6. **Probability and feedback.** Current third true bit is excluded from prediction.
7. **Exclusions and boundaries.** Using full h would instead give 3/5; target concerns actual strict past.

## B056

1. **Objects.** A=q and list [true,true]
2. **Quantifier order.** Closed numerical statement.
3. **Assumptions.** None.
4. **Conclusion.** R_q([true,true])=13/36.

   \[
   R_q([1,1])=13/36.
   \]

5. **Constants and indices.** Learner loss 1/4+1/9; hindsight constant-one loss zero.
6. **Probability and feedback.** Actual q([])=1/2 then q([true])=2/3 path.
7. **Exclusions and boundaries.** This is one-sequence value, not E_2 regret.

## B057

1. **Objects.** h=[true,false]
2. **Quantifier order.** Closed numerical statement.
3. **Assumptions.** None.
4. **Conclusion.** C([true,false])=1/2.

   \[
   C([1,0])=1/2.
   \]

5. **Constants and indices.** Mean 1/2; two deviations each 1/4.
6. **Probability and feedback.** Full-sequence hindsight loss, not prediction loss.
7. **Exclusions and boundaries.** Order reversal does not change this comparator loss.

## B058

1. **Objects.** A=q and T=1
2. **Quantifier order.** Closed inequality.
3. **Assumptions.** None.
4. **Conclusion.** 1/4≤E_1[R_q].

   \[
   1/4\le E_1[R_q].
   \]

5. **Constants and indices.** Exact lower constant 1/4; actual weighted value also 1/4.
6. **Probability and feedback.** Finite expected regret canary with zero singleton hindsight loss.
7. **Exclusions and boundaries.** Not a claim for empty horizon or arbitrary A by this closed test.

## B059

1. **Objects.** Bool finite arms and weights 1/2
2. **Quantifier order.** Closed P predicate.
3. **Assumptions.** None.
4. **Conclusion.** P(univ_Bool,b↦1/2): both weights nonnegative and sum one.

   \[
   P(\{\mathrm{false},\mathrm{true}\},b\mapsto1/2).
   \]

5. **Constants and indices.** Two arms, exact halves.
6. **Probability and feedback.** Normalization of seed weights for f11.
7. **Exclusions and boundaries.** No assertion about arbitrary real weight or seed type.

## B060

1. **Objects.** Boolean b and arbitrary history h
2. **Quantifier order.** ∀b:Bool ∀h:List Bool.
3. **Assumptions.** None.
4. **Conclusion.** A^b(h)∈[0,1]: the fixed-bit predictor f12 is bounded.

   \[
   \forall b,h,\quad A^b(h)\in[0,1].
   \]

5. **Constants and indices.** Values exactly 1 or 0.
6. **Probability and feedback.** Predictor ignores all history, retaining its seed choice.
7. **Exclusions and boundaries.** Every history including empty; not a newly resampled seed per round.

## B061

1. **Objects.** Fixed seed predictor evaluations and ν=f11
2. **Quantifier order.** Closed four-conjunct statement.
3. **Assumptions.** None.
4. **Conclusion.** A^true([])=1 ∧ A^false([])=0 ∧ ν({true})=1/2 ∧ ν({false})=1/2.

   \[
   A^{\mathrm{true}}([])=1\ \land\ A^{\mathrm{false}}([])=0\ \land\ \nu(\{\mathrm{true}\})=1/2\ \land\ \nu(\{\mathrm{false}\})=1/2.
   \]

5. **Constants and indices.** Measure halves are ENNReal; predictor values real.
6. **Probability and feedback.** Two-atom seed law and deterministic per-seed predictors.
7. **Exclusions and boundaries.** Singleton mass statement is distinct from a full independence assertion.

## B062

1. **Objects.** Fixed Bool seed law ν, family A^b, T=2
2. **Quantifier order.** Closed existential ∃v∈V_2 before seed integral.
3. **Assumptions.** None beyond fixed definitions.
4. **Conclusion.** ∃v∈V_2, 11/36≤∫_Bool R_{A^b}(v)dν(b).

   \[
   \exists v\in V_2,\quad11/36\le\int R_{A^b}(v)\,d\nu(b).
   \]

5. **Constants and indices.** 11/36=H_3/6; exact constant.
6. **Probability and feedback.** One v for both seed branches in the average, not seed-dependent selection.
7. **Exclusions and boundaries.** No specified witness in target; not per-seed lower bound or universal over sequences.

## B063

1. **Objects.** Same fixed Bool randomized learner, T=2
2. **Quantifier order.** Closed existential ∃v∈V_2.
3. **Assumptions.** None beyond fixed definitions.
4. **Conclusion.** ∃v∈V_2, log(4)/6≤∫_Bool R_{A^b}(v)dν(b).

   \[
   \exists v\in V_2,\quad\log4/6\le\int R_{A^b}(v)\,d\nu(b).
   \]

5. **Constants and indices.** Log 4, divisor 6.
6. **Probability and feedback.** Witness fixed before averaging; atomic finite integral.
7. **Exclusions and boundaries.** Not a high-probability or every-sequence statement.

## B064

1. **Objects.** Deterministic A=q and positive natural T
2. **Quantifier order.** ∀T>0, ∃v∈V_T.
3. **Assumptions.** T>0.
4. **Conclusion.** ∃v∈V_T, log(T+2)/6≤R_q(v): some target sequence forces this deterministic predictor's regret.

   \[
   \forall T,\quad T>0\Rightarrow\exists v\in V_T,\quad\log(T+2)/6\le R_q(v).
   \]

5. **Constants and indices.** Same horizon in length, log argument and regret.
6. **Probability and feedback.** Actual newest-first q predictions versus same sequence's hindsight mean; no seed average.
7. **Exclusions and boundaries.** Witness can depend on T; not one infinite sequence simultaneously for all T; T=0 excluded.

## Actual semantic observations, without a source/proof verdict

No internal semantic ambiguity in the supplied definitions prevents decoding. The main scope limits are substantive:

- B040, B047, B048 and B064 exclude zero horizon; their positive lower constants would not describe empty regret at T=0. The preceding finite-sum identities generally include T=0 unless explicitly excluded.
- B014 admits c=0 and is an algebraic total-division identity. It must not be silently rephrased with a positive-divisor premise.
- The deterministic lower-bound family through B040 does not require A to be bounded or measurable; the seed-integral family adds exactly the measurability and boundedness conditions shown.
- B046 is a target proposition asserting integrability, not an assumption automatically present in every earlier integral expression. Finite \(\nu_T\) and arbitrary seed \(\mu\) have distinct reasons for well-defined expectation interpretations.
- B047/B048 and the closed randomized tests fix an existential vector before seed averaging. They do not permit selecting a different vector after each seed, nor state that every seed has the lower bound. No explicit joint-law independence predicate appears.
- A closed numerical check is not a universal theorem. In particular B054/B055 preserve the reverse-list strict-past order, and B056 is one-list regret rather than a weighted expectation.
- The definitions and typed closed propositions supply mathematical statements only. The manifest's proof-absence declaration is consistent with the shown text. No target proof, source mapping, source-fidelity verdict, compilation result, acceptance, or chapter/Goal completion has been established by this decoder.

Requested runtime model/effort remain unattested. Reused staged history and absence of external/human independence certification are explicitly disclosed.

