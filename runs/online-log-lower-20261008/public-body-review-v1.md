# Distinct BODY source review: guessing logarithmic lower bound

Verdict: **accepted-with-explicit-delta**, for the actual candidate proof bodies only. No blocking mathematical or metadata repair found. Actor `/root/source_reviewer`; requested GPT-6 Astra / medium, runtime unattested. Prior staged source-review history, including this CONTRACT, is disclosed. This is not blind, human or external review.

All 679 fixed raw inputs and all 153 original applicable CONTRACT inputs were independently rehashed before and after the semantic review with no mismatch. Original CONTRACT receipt bindings also remain exact. The pinned PDF SHA is `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17`. I read printed pages 2–4 and directly viewed the printed-4/PDF16 image. Its statement is qualitative logarithmic unavoidability and explicitly does not provide a minimax-optimality proof. H(T+1)/6 and log(T+2)/6 are derived support constants, not printed or sharp constants. This audit does not close the source package or chapter.

## Actual producer and definition audit

Read all 48 public proof bodies, ten complete public definitions, the private vector cons equivalence, and all sixteen canary proofs/two fixtures plus the probability instance. The recursive weight is policy/seed independent, newest-first, strictly positive and genuinely normalized. The shared finite distribution and atomic measure are reused. Finite weighted algebra is distinguished from the seed integral. The stream reverses the list and pads after its end; the learner sees exactly the strict past, and current-bit prediction is reconstructed as A(h). The same stream and actual shared empirical mean appear throughout regret and its two loss components.

The first/second count recurrences produce T/2 and T(2T+1)/6. They yield conditional variance (T+3)/(6(T+2)). The actual causal loss recursion, nonnegative square, harmonic telescoping and actual mean optimum (T-1)/6 produce the deterministic expected-regret lower bound. No moment, minimum or regret-bound certificate is assumed. The deterministic finite-history helper permits arbitrary real predictions. Seed terminals additionally require probability, section measurability, and pointwise all-seed/all-history [0,1] predictions.

The randomized proof first proves absolute regret bounded by path length and measurable seed dependence, then integrability. It integrates the deterministic bound and interchanges an actually integrable finite weighted sum. Strict positivity and unit mass force one vector whose seed integral exceeds the bound. This vector is outside the seed integral: it is not selected per seed. No high-probability, almost-sure, uniform-seed, single-infinite-path or sharp minimax constant statement is obtained. Restricting adversarial labels to binary values suffices for a lower witness in the source real interval game. A policy is a supplied measurable causal seed family, not a proof that all possible randomized oracle implementations admit such a representation.

Canaries test dependent unequal path masses, genuine prefix/current-bit distinctions, actual regret 13/36, comparator loss 1/2, zero normalization, one-step 1/4, a nontrivial two-atom seed and both actual terminal calls. The deterministic specialization uses a Dirac seed. These are not replacements for universal producers.

## Evidence and limits

Actual public build: 3399 jobs, exit 0, 11.405 seconds; whole canary build v3: 3400 jobs, exit 0, 10.479 seconds, including replay/cache. The 76 named kernel checks contain only standard axioms (or smaller subsets), no sorryAx. All 64 header guards pass, but safe-verify does not compile Lean. Actual v3 compiles 64 closed proposition identities and twelve definition identities. The recursive weight equality is proved by list induction/funext; expectation/measure identities use it; the distinct nominal distribution records are equated by propext in both directions. Failed v1/v2 comparisons remain rejected history, not accepted aliases or proofs. Nonfatal linter warnings remain.

Independently checked all thirty specified dependencies against actual node value_dependencies: all present. The selected TEST-environment graph contains 76 nodes (64 proofs, 12 definitions) and 6800 direct references, not a full-library export. Earlier failed attempts and repairs stay preserved. No new compilation was run by this reviewer; these are inspected actual command/log/exit artifacts.

Combined roots, full harness, reader integration, rendered formulas, site, FINAL, native package acceptance and PR delivery remain pending. R1–R8 below are copied unchanged from CONTRACT and are not discharged here. Chapter1's sixteen source items are not a proof-total denominator; other Regret/NoRegret and remaining maintext obligations, Chapter2, Chapters3–16 and required appendices remain open. Whole Goal remains active; no merge/live claim.

## Per-target seven-slot comparison

The explicit semantic slots below are transcribed from the bound neutral reconstruction after comparison with actual complete types and bodies; the body findings and source/derived/test classification are this review's judgments, not decoder proof acceptance.

### B001 — `BanditRL.OnlineLearning.GuessingLower.probability_mem`

Verdict: accepted-with-explicit-delta. derived producer/helper supporting the qualitative source claim; not a separately printed theorem.

Actual body: Count bound and positive denominator give strict q endpoints.

- **objects**: h: finite Boolean list

- **quantifier_order**: ∀h.

- **assumptions**: None.

- **conclusion**: 0<q(h)<1: the smoothed count ratio is strictly interior.

   \[
   \forall h,\quad 0<q(h)<1.
   \]

- **constants_and_indices**: q=(k+1)/(n+2); strict endpoints.

- **probability_and_feedback**: Only supplied history counts are used.

- **exclusions_and_boundaries**: Empty h gives 1/2; all-equal histories remain interior.

### B002 — `BanditRL.OnlineLearning.GuessingLower.branch_mass`

Verdict: accepted-with-explicit-delta. derived producer/helper supporting the qualitative source claim; not a separately printed theorem.

Actual body: Ring identity preserves parent mass.

- **objects**: h and its two newest-bit extensions

- **quantifier_order**: ∀h.

- **assumptions**: None.

- **conclusion**: w(false::h)+w(true::h)=w(h): children preserve parent mass.

   \[
   \forall h,\quad w(\mathrm{false}::h)+w(\mathrm{true}::h)=w(h).
   \]

- **constants_and_indices**: Children have length n+1.

- **probability_and_feedback**: New bit is the head; h is the older history.

- **exclusions_and_boundaries**: Empty parent allowed; this identity alone is not P.

### B003 — `BanditRL.OnlineLearning.GuessingLower.pathWeight_nonneg`

Verdict: accepted-with-explicit-delta. derived producer/helper supporting the qualitative source claim; not a separately printed theorem.

Actual body: List induction gives nonnegative factors.

- **objects**: h and real weight w(h)

- **quantifier_order**: ∀h.

- **assumptions**: None.

- **conclusion**: 0≤w(h): every list weight is nonnegative.

   \[
   \forall h,\quad 0\le w(h).
   \]

- **constants_and_indices**: Non-strict zero lower bound.

- **probability_and_feedback**: A finite weight, not yet a normalization assertion.

- **exclusions_and_boundaries**: Includes empty h with weight 1; strictness is separately B041.

### B004 — `BanditRL.OnlineLearning.GuessingLower.sum_vectors_succ`

Verdict: accepted-with-explicit-delta. derived producer/helper supporting the qualitative source claim; not a separately printed theorem.

Actual body: Actual cons/head/tail equivalence enumerates both branches.

- **objects**: T∈N; F:List Bool→R

- **quantifier_order**: ∀T ∀F.

- **assumptions**: None.

- **conclusion**: Σ_{v∈V_{T+1}}F(v)=Σ_{v∈V_T}[F(false::v)+F(true::v)]: enumerate all lists by newest head.

   \[
   \forall T,F,\quad \sum_{v\in V_{T+1}}F(v)=\sum_{v\in V_T}\bigl(F(\mathrm{false}::v)+F(\mathrm{true}::v)\bigr).
   \]

- **constants_and_indices**: Unweighted sums; no factor or w.

- **probability_and_feedback**: Pure finite enumeration, not expectation.

- **exclusions_and_boundaries**: T=0 valid; F arbitrary, including signed.

### B005 — `BanditRL.OnlineLearning.GuessingLower.prefix_mass_one`

Verdict: accepted-with-explicit-delta. derived producer/helper supporting the qualitative source claim; not a separately printed theorem.

Actual body: Natural induction combines branch mass and vector enumeration.

- **objects**: T and length-T weights

- **quantifier_order**: ∀T∈N.

- **assumptions**: None.

- **conclusion**: Σ_{v∈V_T}w(v)=1: fixed-length total weight is one.

   \[
   \forall T,\quad\sum_{v\in V_T}w(v)=1.
   \]

- **constants_and_indices**: Exact unit total.

- **probability_and_feedback**: Finite normalization without measure-space inputs.

- **exclusions_and_boundaries**: T=0 has the single empty vector.

### B006 — `BanditRL.OnlineLearning.GuessingLower.prefix_distribution`

Verdict: accepted-with-explicit-delta. derived producer/helper supporting the qualitative source claim; not a separately printed theorem.

Actual body: Produces both shared distribution fields.

- **objects**: T and predicate P on V_T

- **quantifier_order**: ∀T∈N.

- **assumptions**: None.

- **conclusion**: P(univ,w): ∀v∈V_T, w(v)≥0 and Σ_{v∈V_T}w(v)=1.

   \[
   \forall T,\quad P(V_T,w).
   \]

- **constants_and_indices**: Both nonnegative and unit-sum conditions.

- **probability_and_feedback**: Discrete normalized-weight predicate, not an integral.

- **exclusions_and_boundaries**: Includes T=0; no condition on other list lengths.

### B007 — `BanditRL.OnlineLearning.GuessingLower.prefixMeasure_probability`

Verdict: accepted-with-explicit-delta. derived producer/helper supporting the qualitative source claim; not a separately printed theorem.

Actual body: Shared probability theorem receives produced normalized law.

- **objects**: T, measurable space and measurable singletons on V_T

- **quantifier_order**: ∀T ∀ supplied measurable-space/singleton instances.

- **assumptions**: Those two instances.

- **conclusion**: IsProbabilityMeasure(ν_T): ν_T has mass one.

   \[
   \forall T\ [\mathsf M_T]\ [\mathsf S_T],\quad\operatorname{IsProbabilityMeasure}(\nu_T).
   \]

- **constants_and_indices**: ν_T=f8(T); weights converted by ofReal.

- **probability_and_feedback**: Probability assertion for this particular atomic measure.

- **exclusions_and_boundaries**: T=0 valid; arbitrary law(arms,p) is not automatically normalized.

### B008 — `BanditRL.OnlineLearning.GuessingLower.pathExpectation_integral`

Verdict: accepted-with-explicit-delta. derived producer/helper supporting the qualitative source claim; not a separately printed theorem.

Actual body: Shared finite integral theorem receives produced distribution.

- **objects**: T, same measurable instances, F:List Bool→R

- **quantifier_order**: ∀T ∀instances ∀F.

- **assumptions**: MeasurableSpace and MeasurableSingletonClass on V_T; no separate F premise.

- **conclusion**: ∫_{V_T} F(v) dν_T=E_T[F]: integral equals finite weighted functional.

   \[
   \forall T\ [\mathsf M_T]\ [\mathsf S_T]\ \forall F,\quad\int F(v)\,d\nu_T(v)=E_T[F].
   \]

- **constants_and_indices**: Identical weights w; values at length T only.

- **probability_and_feedback**: Finite measurable-singleton domain supports the stated real-integral identity.

- **exclusions_and_boundaries**: T=0 gives F([]); not an arbitrary infinite-domain integrability assertion.

### B009 — `BanditRL.OnlineLearning.GuessingLower.pathExpectation_congr`

Verdict: accepted-with-explicit-delta. derived producer/helper supporting the qualitative source claim; not a separately printed theorem.

Actual body: Sum congruence uses only length-T equality.

- **objects**: T; real list functions F,G

- **quantifier_order**: ∀T ∀F,G.

- **assumptions**: ∀h, n(h)=T ⇒ F(h)=G(h).

- **conclusion**: E_T[F]=E_T[G]: equal fixed-length values give equal weighted sums.

   \[
   \forall T,F,G,\quad(\forall h,\ n(h)=T\Rightarrow F(h)=G(h))\Rightarrow E_T[F]=E_T[G].
   \]

- **constants_and_indices**: No agreement required on other lengths.

- **probability_and_feedback**: Pointwise finite-functional extensionality.

- **exclusions_and_boundaries**: T=0 requires agreement at []; no probabilistic assumption.

### B010 — `BanditRL.OnlineLearning.GuessingLower.pathExpectation_const`

Verdict: accepted-with-explicit-delta. derived producer/helper supporting the qualitative source claim; not a separately printed theorem.

Actual body: Unit mass cancels constant factor.

- **objects**: T and real constant c

- **quantifier_order**: ∀T ∀c∈R.

- **assumptions**: None.

- **conclusion**: E_T[h↦c]=c: constants are preserved.

   \[
   \forall T,c,\quad E_T[c]=c.
   \]

- **constants_and_indices**: Exact factor 1 from unit mass.

- **probability_and_feedback**: Finite weighted functional, without measurability input.

- **exclusions_and_boundaries**: c zero or negative and T=0 allowed.

### B011 — `BanditRL.OnlineLearning.GuessingLower.pathExpectation_add`

Verdict: accepted-with-explicit-delta. derived producer/helper supporting the qualitative source claim; not a separately printed theorem.

Actual body: Distributes multiplication over addition and finite sums.

- **objects**: T and real list functions F,G

- **quantifier_order**: ∀T ∀F,G.

- **assumptions**: None.

- **conclusion**: E_T[F+G]=E_T[F]+E_T[G]: additivity.

   \[
   \forall T,F,G,\quad E_T[F+G]=E_T[F]+E_T[G].
   \]

- **constants_and_indices**: Pointwise addition, exact equality.

- **probability_and_feedback**: Finite sum algebra.

- **exclusions_and_boundaries**: No positivity or integrability premise; T=0 allowed.

### B012 — `BanditRL.OnlineLearning.GuessingLower.pathExpectation_sub`

Verdict: accepted-with-explicit-delta. derived producer/helper supporting the qualitative source claim; not a separately printed theorem.

Actual body: Distributes signed subtraction.

- **objects**: T and real list functions F,G

- **quantifier_order**: ∀T ∀F,G.

- **assumptions**: None.

- **conclusion**: E_T[F−G]=E_T[F]−E_T[G]: subtraction is preserved.

   \[
   \forall T,F,G,\quad E_T[F-G]=E_T[F]-E_T[G].
   \]

- **constants_and_indices**: Signed subtraction, no absolute value.

- **probability_and_feedback**: Finite sum algebra.

- **exclusions_and_boundaries**: Arbitrary signed functions; T=0 allowed.

### B013 — `BanditRL.OnlineLearning.GuessingLower.pathExpectation_const_mul`

Verdict: accepted-with-explicit-delta. derived producer/helper supporting the qualitative source claim; not a separately printed theorem.

Actual body: Associativity and finite sum multiplication.

- **objects**: T, real c, real list function F

- **quantifier_order**: ∀T ∀c ∀F.

- **assumptions**: None.

- **conclusion**: E_T[cF]=c E_T[F]: scalar homogeneity.

   \[
   \forall T,c,F,\quad E_T[cF]=cE_T[F].
   \]

- **constants_and_indices**: c multiplies every value.

- **probability_and_feedback**: Finite real sum, no probability requirement in the type.

- **exclusions_and_boundaries**: c may be negative or zero.

### B014 — `BanditRL.OnlineLearning.GuessingLower.pathExpectation_div`

Verdict: accepted-with-explicit-delta. derived producer/helper supporting the qualitative source claim; not a separately printed theorem.

Actual body: Total real division identity including zero divisor.

- **objects**: T, real list function F, real divisor c

- **quantifier_order**: ∀T ∀F ∀c.

- **assumptions**: None.

- **conclusion**: E_T[F/c]=E_T[F]/c: totalized scalar division commutes with finite weighting.

   \[
   \forall T,F,c,\quad E_T[F/c]=E_T[F]/c.
   \]

- **constants_and_indices**: Same divisor c everywhere.

- **probability_and_feedback**: Algebraic equality, not a bound.

- **exclusions_and_boundaries**: c=0 explicitly permitted: total real division makes both sides zero.

### B015 — `BanditRL.OnlineLearning.GuessingLower.pathExpectation_succ`

Verdict: accepted-with-explicit-delta. derived producer/helper supporting the qualitative source claim; not a separately printed theorem.

Actual body: Actual vector partition and branch-weight recurrence.

- **objects**: T and real list function F

- **quantifier_order**: ∀T ∀F.

- **assumptions**: None.

- **conclusion**: E_{T+1}[F]=E_T[h↦(1−q(h))F(false::h)+q(h)F(true::h)]: weighted extension recursion.

   \[
   \forall T,F,\quad E_{T+1}[F]=E_T[h\mapsto(1-q(h))F(\mathrm{false}::h)+q(h)F(\mathrm{true}::h)].
   \]

- **constants_and_indices**: Complementary weights, no 1/2 replacement.

- **probability_and_feedback**: A next-bit conditional weighting description for this construction.

- **exclusions_and_boundaries**: T=0 valid; no independent-bit assumption.

### B016 — `BanditRL.OnlineLearning.GuessingLower.heads_succ`

Verdict: accepted-with-explicit-delta. derived producer/helper supporting the qualitative source claim; not a separately printed theorem.

Actual body: Count-cons algebra gives first moment recursion.

- **objects**: T; M_T=E_T[k]

- **quantifier_order**: ∀T∈N.

- **assumptions**: None.

- **conclusion**: M_{T+1}=M_T+(M_T+1)/(T+2): first-count-moment recursion.

   \[
   \forall T,\quad M_{T+1}=M_T+\frac{M_T+1}{T+2}.
   \]

- **constants_and_indices**: Offsets +1 and +2 exact.

- **probability_and_feedback**: Moment of the defined dependent-history weights.

- **exclusions_and_boundaries**: T=0 valid; denominator always positive.

### B017 — `BanditRL.OnlineLearning.GuessingLower.heads_sq_succ`

Verdict: accepted-with-explicit-delta. derived producer/helper supporting the qualitative source claim; not a separately printed theorem.

Actual body: Count-square expansion gives second moment recursion.

- **objects**: T; M_T=E_T[k], Q_T=E_T[k²]

- **quantifier_order**: ∀T∈N.

- **assumptions**: None.

- **conclusion**: Q_{T+1}=Q_T+(2Q_T+3M_T+1)/(T+2): second raw moment recursion.

   \[
   \forall T,\quad Q_{T+1}=Q_T+\frac{2Q_T+3M_T+1}{T+2}.
   \]

- **constants_and_indices**: Coefficients 2,3,1; denominator T+2.

- **probability_and_feedback**: Square inside expectation, not squared mean.

- **exclusions_and_boundaries**: T=0 valid; no binomial independence premise.

### B018 — `BanditRL.OnlineLearning.GuessingLower.expected_heads`

Verdict: accepted-with-explicit-delta. derived producer/helper supporting the qualitative source claim; not a separately printed theorem.

Actual body: Induction solves first moment.

- **objects**: T and count k

- **quantifier_order**: ∀T∈N.

- **assumptions**: None.

- **conclusion**: E_T[k]=T/2: expected number of true bits is half T.

   \[
   \forall T,\quad E_T[k]=T/2.
   \]

- **constants_and_indices**: Natural T coerced to real.

- **probability_and_feedback**: Finite weighted first moment.

- **exclusions_and_boundaries**: T=0 gives zero; does not establish independent fair bits.

### B019 — `BanditRL.OnlineLearning.GuessingLower.expected_heads_sq`

Verdict: accepted-with-explicit-delta. derived producer/helper supporting the qualitative source claim; not a separately printed theorem.

Actual body: Induction with actual first moment solves second.

- **objects**: T and k²

- **quantifier_order**: ∀T∈N.

- **assumptions**: None.

- **conclusion**: E_T[k²]=T(2T+1)/6: exact second raw moment.

   \[
   \forall T,\quad E_T[k^2]=T(2T+1)/6.
   \]

- **constants_and_indices**: Denominator 6, not a variance.

- **probability_and_feedback**: Finite weighted count moment.

- **exclusions_and_boundaries**: T=0 gives zero; not the independent-binomial second moment.

### B020 — `BanditRL.OnlineLearning.GuessingLower.expected_next_variance`

Verdict: accepted-with-explicit-delta. derived producer/helper supporting the qualitative source claim; not a separately printed theorem.

Actual body: Expands q(1-q) and substitutes both actual moments.

- **objects**: T and q(h)(1−q(h))

- **quantifier_order**: ∀T∈N.

- **assumptions**: None.

- **conclusion**: E_T[q(1−q)]=(T+3)/(6(T+2)).

   \[
   \forall T,\quad E_T[q(1-q)]=\frac{T+3}{6(T+2)}.
   \]

- **constants_and_indices**: Offsets +3,+2 and factor 6.

- **probability_and_feedback**: Moment of history-dependent next-bit parameter.

- **exclusions_and_boundaries**: At T=0 value 1/4; no positive-horizon restriction.

### B021 — `BanditRL.OnlineLearning.GuessingLower.causalPredict_prefix`

Verdict: accepted-with-explicit-delta. derived producer/helper supporting the qualitative source claim; not a separately printed theorem.

Actual body: List.ofFn congruence and reversal establish strict past.

- **objects**: A:List Bool→R; Boolean streams y,z; t∈N

- **quantifier_order**: ∀A ∀y,z ∀t.

- **assumptions**: ∀i<t, y_i=z_i.

- **conclusion**: x_t(A,y)=x_t(A,z): actual predictions agree under strict-prefix agreement.

   \[
   \forall A,y,z,t,\quad(\forall i<t,\ y_i=z_i)\Rightarrow x_t(A,y)=x_t(A,z).
   \]

- **constants_and_indices**: A receives [y_{t−1},…,y_0].

- **probability_and_feedback**: No current or future bit is passed; A fixed on both sides.

- **exclusions_and_boundaries**: At zero both A([]); no bound/measurability on A; external construction independence not asserted.

### B022 — `BanditRL.OnlineLearning.GuessingLower.binary_mean_minimizer`

Verdict: accepted-with-explicit-delta. derived producer/helper supporting the qualitative source claim; not a separately printed theorem.

Actual body: Shared actual mean membership and minimization for binary values.

- **objects**: Nonempty list h; n=n(h), y=Y_h, mean μ_h

- **quantifier_order**: ∀h with n>0; then ∀u∈[0,1].

- **assumptions**: n>0.

- **conclusion**: μ_h∈[0,1] ∧ ∀u∈[0,1], Σ_{t<n}(μ_h−y_t)²≤Σ_{t<n}(u−y_t)²: feasible hindsight mean minimizes these losses.

   \[
   \forall h,\quad n(h)>0\Rightarrow\left[\mu_h\in[0,1]\ \land\ \forall u\in[0,1],\ \sum_{t<n(h)}(\mu_h-Y_h(t))^2\le\sum_{t<n(h)}(u-Y_h(t))^2\right].
   \]

- **constants_and_indices**: Single full-prefix comparator μ_h throughout.

- **probability_and_feedback**: Hindsight uses all targets; not available to earlier predictions.

- **exclusions_and_boundaries**: Empty list excluded; no uniqueness or all-real-u claim in this target.

### B023 — `BanditRL.OnlineLearning.GuessingLower.conditional_square_lower`

Verdict: accepted-with-explicit-delta. derived producer/helper supporting the qualitative source claim; not a separately printed theorem.

Actual body: Nonnegative square of x-q proves conditional lower bound for every real x.

- **objects**: h:List Bool and real x

- **quantifier_order**: ∀h ∀x∈R.

- **assumptions**: None.

- **conclusion**: q(h)(1−q(h))≤(1−q(h))x²+q(h)(x−1)²: weighted one-step loss lower bound.

   \[
   \forall h,x,\quad q(h)(1-q(h))\le(1-q(h))x^2+q(h)(x-1)^2.
   \]

- **constants_and_indices**: Gap is (x−q(h))²; no half coefficient.

- **probability_and_feedback**: For a fixed past h and arbitrary real prediction.

- **exclusions_and_boundaries**: x need not be in [0,1]; empty h allowed.

### B024 — `BanditRL.OnlineLearning.GuessingLower.binaryStream_cons_prefix`

Verdict: accepted-with-explicit-delta. derived producer/helper supporting the qualitative source claim; not a separately printed theorem.

Actual body: Reverse-cons append indexing preserves strict prefix.

- **objects**: Boolean b, list h, natural t

- **quantifier_order**: ∀b ∀h ∀t.

- **assumptions**: t<n(h).

- **conclusion**: y^B_{b::h}(t)=y^B_h(t): older chronological bits unchanged.

   \[
   \forall b,h,t,\quad t<n(h)\Rightarrow y^B_{b::h}(t)=y^B_h(t).
   \]

- **constants_and_indices**: Strict t<n, not t=n.

- **probability_and_feedback**: Prepending newest bit appends it chronologically.

- **exclusions_and_boundaries**: For empty h no qualifying t; default tail values not claimed equal here.

### B025 — `BanditRL.OnlineLearning.GuessingLower.binaryStream_cons_last`

Verdict: accepted-with-explicit-delta. derived producer/helper supporting the qualitative source claim; not a separately printed theorem.

Actual body: Last append index is the new bit.

- **objects**: Boolean b and list h

- **quantifier_order**: ∀b ∀h.

- **assumptions**: None.

- **conclusion**: y^B_{b::h}(n(h))=b: new head is the last chronological target.

   \[
   \forall b,h,\quad y^B_{b::h}(n(h))=b.
   \]

- **constants_and_indices**: Index n, child length n+1.

- **probability_and_feedback**: Confirms newest-first storage order.

- **exclusions_and_boundaries**: For h=[] reads index zero; no default is used at this valid index.

### B026 — `BanditRL.OnlineLearning.GuessingLower.binaryValues_cons_prefix`

Verdict: accepted-with-explicit-delta. derived producer/helper supporting the qualitative source claim; not a separately printed theorem.

Actual body: Indicator conversion of actual prefix equality.

- **objects**: Boolean b, list h, t∈N

- **quantifier_order**: ∀b ∀h ∀t.

- **assumptions**: t<n(h).

- **conclusion**: Y_{b::h}(t)=Y_h(t): old real-indicator targets unchanged.

   \[
   \forall b,h,t,\quad t<n(h)\Rightarrow Y_{b::h}(t)=Y_h(t).
   \]

- **constants_and_indices**: Only earlier n indices.

- **probability_and_feedback**: Indicator version of chronological prefix preservation.

- **exclusions_and_boundaries**: No claim for t=n; empty h gives vacuous scope.

### B027 — `BanditRL.OnlineLearning.GuessingLower.causalPredict_history`

Verdict: accepted-with-explicit-delta. derived producer/helper supporting the qualitative source claim; not a separately printed theorem.

Actual body: List extensionality and double reversal reconstruct complete past.

- **objects**: A:List Bool→R and h

- **quantifier_order**: ∀A ∀h.

- **assumptions**: None.

- **conclusion**: x_{n(h)}(A,y^B_h)=A(h): reconstructing the whole past returns the same newest-first list to A.

   \[
   \forall A,h,\quad x_{n(h)}(A,y^B_h)=A(h).
   \]

- **constants_and_indices**: Time n is after n targets, before any default future target.

- **probability_and_feedback**: Exact strict-past identity, not use of hindsight comparator.

- **exclusions_and_boundaries**: Empty h gives A([]); A arbitrary.

### B028 — `BanditRL.OnlineLearning.GuessingLower.causalPredict_cons_last`

Verdict: accepted-with-explicit-delta. derived producer/helper supporting the qualitative source claim; not a separately printed theorem.

Actual body: Prefix identity and reconstructed history exclude current bit.

- **objects**: A, Boolean b and list h

- **quantifier_order**: ∀A ∀b ∀h.

- **assumptions**: None.

- **conclusion**: x_{n(h)}(A,y^B_{b::h})=A(h): prediction for newest bit depends only on older h.

   \[
   \forall A,b,h,\quad x_{n(h)}(A,y^B_{b::h})=A(h).
   \]

- **constants_and_indices**: Current target b at chronological n excluded.

- **probability_and_feedback**: Actual input ordering, not an independent prediction path.

- **exclusions_and_boundaries**: h=[] allowed; A(h) does not explicitly depend on b.

### B029 — `BanditRL.OnlineLearning.GuessingLower.pathRegret_eq_losses`

Verdict: accepted-with-explicit-delta. derived producer/helper supporting the qualitative source claim; not a separately printed theorem.

Actual body: Unfolded shared regret is exact same-path loss difference.

- **objects**: A and h; R=f6, L=f9, C=f10

- **quantifier_order**: ∀A ∀h.

- **assumptions**: None.

- **conclusion**: R_A(h)=L_A(h)−C(h): regret decomposes into same-path learner loss minus same-sequence hindsight loss.

   \[
   \forall A,h,\quad R_A(h)=L_A(h)-C(h).
   \]

- **constants_and_indices**: Exact subtraction; same n terms.

- **probability_and_feedback**: No change of predictions or comparator between components.

- **exclusions_and_boundaries**: Empty h all zero; signed R need not be nonnegative.

### B030 — `BanditRL.OnlineLearning.GuessingLower.pathLearnerLoss_cons`

Verdict: accepted-with-explicit-delta. derived producer/helper supporting the qualitative source claim; not a separately printed theorem.

Actual body: Range-successor split and prefix identities produce current actual loss.

- **objects**: A, Boolean b, history h

- **quantifier_order**: ∀A ∀b ∀h.

- **assumptions**: None.

- **conclusion**: L_A(b::h)=L_A(h)+(A(h)−1_b)²: append the actual current loss.

   \[
   \forall A,b,h,\quad L_A(b::h)=L_A(h)+(A(h)-\mathbf1_b)^2.
   \]

- **constants_and_indices**: New chronological index n(h); 1_b is 0 or 1.

- **probability_and_feedback**: Same A and old path; current prediction A(h) before b is used.

- **exclusions_and_boundaries**: Empty history allowed; no prediction bound required.

### B031 — `BanditRL.OnlineLearning.GuessingLower.binaryValues_sum`

Verdict: accepted-with-explicit-delta. derived producer/helper supporting the qualitative source claim; not a separately printed theorem.

Actual body: List induction gives true-count sum.

- **objects**: Boolean list h

- **quantifier_order**: ∀h.

- **assumptions**: None.

- **conclusion**: Σ_{t<n(h)}Y_h(t)=k(h): chronological indicator sum equals true count.

   \[
   \forall h,\quad\sum_{t<n(h)}Y_h(t)=k(h).
   \]

- **constants_and_indices**: No extra tail/default contribution.

- **probability_and_feedback**: Finite reversal preserves counts.

- **exclusions_and_boundaries**: Empty h gives 0=0.

### B032 — `BanditRL.OnlineLearning.GuessingLower.binaryValues_sq`

Verdict: accepted-with-explicit-delta. derived producer/helper supporting the qualitative source claim; not a separately printed theorem.

Actual body: Both Boolean cases including default give idempotence.

- **objects**: Boolean list h and natural t

- **quantifier_order**: ∀h ∀t.

- **assumptions**: None.

- **conclusion**: Y_h(t)²=Y_h(t): binary indicators are idempotent.

   \[
   \forall h,t,\quad Y_h(t)^2=Y_h(t).
   \]

- **constants_and_indices**: All natural t, not only valid indices.

- **probability_and_feedback**: Includes false/zero default outside list.

- **exclusions_and_boundaries**: Empty and out-of-range queries yield zero; no probability required.

### B033 — `BanditRL.OnlineLearning.GuessingLower.pathBestLoss_count`

Verdict: accepted-with-explicit-delta. derived producer/helper supporting the qualitative source claim; not a separately printed theorem.

Actual body: Actual shared mean decomposition at zero yields count formula.

- **objects**: Nonempty list h, count k and length n

- **quantifier_order**: ∀h with n>0.

- **assumptions**: n>0.

- **conclusion**: C(h)=k(h)−k(h)²/n(h): explicit hindsight squared loss.

   \[
   \forall h,\quad n(h)>0\Rightarrow C(h)=k(h)-k(h)^2/n(h).
   \]

- **constants_and_indices**: Real division by positive n.

- **probability_and_feedback**: Mean of same decoded binary sequence.

- **exclusions_and_boundaries**: Empty case excluded; totalized division does not remove this premise.

### B034 — `BanditRL.OnlineLearning.GuessingLower.expected_pathBestLoss`

Verdict: accepted-with-explicit-delta. derived producer/helper supporting the qualitative source claim; not a separately printed theorem.

Actual body: Same-length expectation identities plus both moments.

- **objects**: Positive T and hindsight loss C

- **quantifier_order**: ∀T with T>0.

- **assumptions**: T>0.

- **conclusion**: E_T[C]=(T−1)/6: exact expected hindsight loss.

   \[
   \forall T,\quad T>0\Rightarrow E_T[C]=(T-1)/6.
   \]

- **constants_and_indices**: Real T−1, denominator 6.

- **probability_and_feedback**: Weighted full-sequence comparator loss, not learner loss.

- **exclusions_and_boundaries**: T=1 gives zero; T=0 excluded since RHS would −1/6.

### B035 — `BanditRL.OnlineLearning.GuessingLower.pathExpectation_mono`

Verdict: accepted-with-explicit-delta. derived producer/helper supporting the qualitative source claim; not a separately printed theorem.

Actual body: Nonnegative weights multiply pointwise comparison.

- **objects**: T and real functions F,G on lists

- **quantifier_order**: ∀T ∀F,G.

- **assumptions**: ∀h, n(h)=T ⇒ F(h)≤G(h).

- **conclusion**: E_T[F]≤E_T[G]: finite weighting preserves this order.

   \[
   \forall T,F,G,\quad(\forall h,\ n(h)=T\Rightarrow F(h)\le G(h))\Rightarrow E_T[F]\le E_T[G].
   \]

- **constants_and_indices**: Length-T pointwise comparison only.

- **probability_and_feedback**: Uses nonnegative weights, no integral assumptions.

- **exclusions_and_boundaries**: Arbitrary signs allowed; T=0 valid.

### B036 — `BanditRL.OnlineLearning.GuessingLower.expected_pathLearnerLoss_succ`

Verdict: accepted-with-explicit-delta. derived producer/helper supporting the qualitative source claim; not a separately printed theorem.

Actual body: Actual loss recursion and branch identity give expected increment.

- **objects**: A and natural T

- **quantifier_order**: ∀A ∀T.

- **assumptions**: None.

- **conclusion**: E_{T+1}[L_A]=E_T[L_A]+E_T[h↦(1−q(h))A(h)²+q(h)(A(h)−1)²]: cumulative-loss recursion.

   \[
   \forall A,T,\quad E_{T+1}[L_A]=E_T[L_A]+E_T[h\mapsto(1-q(h))A(h)^2+q(h)(A(h)-1)^2].
   \]

- **constants_and_indices**: Exactly one added current conditional loss.

- **probability_and_feedback**: Current A(h) shared across both possible next bits.

- **exclusions_and_boundaries**: A unbounded allowed, finite sums remain finite; T=0 valid.

### B037 — `BanditRL.OnlineLearning.GuessingLower.expected_pathLearnerLoss_step`

Verdict: accepted-with-explicit-delta. derived producer/helper supporting the qualitative source claim; not a separately printed theorem.

Actual body: Pointwise square lower bound and produced variance.

- **objects**: A and T

- **quantifier_order**: ∀A ∀T.

- **assumptions**: None.

- **conclusion**: E_T[L_A]+(T+3)/(6(T+2))≤E_{T+1}[L_A]: positive expected increment lower bound.

   \[
   \forall A,T,\quad E_T[L_A]+\frac{T+3}{6(T+2)}\le E_{T+1}[L_A].
   \]

- **constants_and_indices**: Same fraction as B020, non-strict inequality.

- **probability_and_feedback**: One-step weighted loss comparison on actual A(h).

- **exclusions_and_boundaries**: T=0 valid; no interval bound on A.

### B038 — `BanditRL.OnlineLearning.GuessingLower.variance_sum`

Verdict: accepted-with-explicit-delta. derived producer/helper supporting the qualitative source claim; not a separately printed theorem.

Actual body: Harmonic successor induction and positive denominators.

- **objects**: Natural T; harmonic H_n

- **quantifier_order**: ∀T∈N.

- **assumptions**: None.

- **conclusion**: Σ_{t<T}(t+3)/(6(t+2))=T/6+(H_{T+1}−1)/6.

   \[
   \forall T,\quad\sum_{t<T}\frac{t+3}{6(t+2)}=\frac T6+\frac{H_{T+1}-1}{6}.
   \]

- **constants_and_indices**: Harmonic index T+1; subtract 1 exactly.

- **probability_and_feedback**: Scalar finite sum identity, not probabilistic.

- **exclusions_and_boundaries**: T=0 both sides zero because H_1=1.

### B039 — `BanditRL.OnlineLearning.GuessingLower.expected_pathLearnerLoss_lower`

Verdict: accepted-with-explicit-delta. derived producer/helper supporting the qualitative source claim; not a separately printed theorem.

Actual body: Induction sums actual incremental lower bounds.

- **objects**: A and T

- **quantifier_order**: ∀A ∀T.

- **assumptions**: None.

- **conclusion**: Σ_{t<T}(t+3)/(6(t+2))≤E_T[L_A]: total expected learner-loss lower bound.

   \[
   \forall A,T,\quad\sum_{t<T}\frac{t+3}{6(t+2)}\le E_T[L_A].
   \]

- **constants_and_indices**: No comparator subtraction yet.

- **probability_and_feedback**: Actual strict-past A path inside L_A.

- **exclusions_and_boundaries**: T=0 both sides zero; no A bound needed.

### B040 — `BanditRL.OnlineLearning.GuessingLower.expected_pathRegret_lower`

Verdict: accepted-with-explicit-delta. derived producer/helper supporting the qualitative source claim; not a separately printed theorem.

Actual body: Subtracts produced expected optimum from produced learner lower bound.

- **objects**: A and positive T

- **quantifier_order**: ∀A ∀T>0.

- **assumptions**: T>0 only.

- **conclusion**: H_{T+1}/6≤E_T[R_A]: finite weighted regret lower bound.

   \[
   \forall A,T,\quad T>0\Rightarrow H_{T+1}/6\le E_T[R_A].
   \]

- **constants_and_indices**: Harmonic T+1, factor 1/6; not averaged by T.

- **probability_and_feedback**: Same actual predictions and full-sequence empirical-mean comparator.

- **exclusions_and_boundaries**: T=0 excluded: RHS zero vs H_1/6 positive; not every sequence or every regret must satisfy bound.

### B041 — `BanditRL.OnlineLearning.GuessingLower.pathWeight_pos`

Verdict: accepted-with-explicit-delta. derived producer/helper supporting the qualitative source claim; not a separately printed theorem.

Actual body: List induction uses strict q and complement positivity.

- **objects**: List h and weight w(h)

- **quantifier_order**: ∀h.

- **assumptions**: None.

- **conclusion**: 0<w(h): every finite list has strictly positive weight.

   \[
   \forall h,\quad0<w(h).
   \]

- **constants_and_indices**: Strict positivity, stronger than B003.

- **probability_and_feedback**: All finite sequences in this construction have positive support.

- **exclusions_and_boundaries**: Empty weight 1; no uniform positive lower constant across all lengths.

### B042 — `BanditRL.OnlineLearning.GuessingLower.square_loss_mem`

Verdict: accepted-with-explicit-delta. derived producer/helper supporting the qualitative source claim; not a separately printed theorem.

Actual body: Interval bounds give squared loss at most one.

- **objects**: Real x,y

- **quantifier_order**: ∀x,y∈R.

- **assumptions**: x∈[0,1], y∈[0,1].

- **conclusion**: (x−y)²∈[0,1]: squared deviation is between zero and one.

   \[
   \forall x,y\in\mathbb R,\quad[x\in[0,1]\land y\in[0,1]]\Rightarrow(x-y)^2\in[0,1].
   \]

- **constants_and_indices**: Inclusive endpoints, coefficient 1.

- **probability_and_feedback**: Deterministic pointwise bound.

- **exclusions_and_boundaries**: Endpoints may attain 1; no claim for arbitrary unbounded x,y.

### B043 — `BanditRL.OnlineLearning.GuessingLower.square_loss_sum_mem`

Verdict: accepted-with-explicit-delta. derived producer/helper supporting the qualitative source claim; not a separately printed theorem.

Actual body: Finite sum of actual pointwise interval bounds.

- **objects**: T and real sequences p,y

- **quantifier_order**: ∀T ∀p,y.

- **assumptions**: ∀t<T, p_t∈[0,1] and ∀t<T, y_t∈[0,1].

- **conclusion**: Σ_{t<T}(p_t−y_t)²∈[0,T]: total loss bounded by count.

   \[
   \forall T,p,y,\quad[(\forall t<T,p_t\in[0,1])\land(\forall t<T,y_t\in[0,1])]\Rightarrow\sum_{t<T}(p_t-y_t)^2\in[0,T].
   \]

- **constants_and_indices**: Real-coerced upper T.

- **probability_and_feedback**: Arbitrary deterministic sequences, no causality hypothesis.

- **exclusions_and_boundaries**: T=0 gives zero; later values unrestricted.

### B044 — `BanditRL.OnlineLearning.GuessingLower.pathRegret_abs_le`

Verdict: accepted-with-explicit-delta. derived producer/helper supporting the qualitative source claim; not a separately printed theorem.

Actual body: Zero case separate; feasible mean and bounded predictions bound both losses.

- **objects**: A and h

- **quantifier_order**: ∀A ∀h.

- **assumptions**: ∀k:List Bool, A(k)∈[0,1].

- **conclusion**: |R_A(h)|≤n(h): actual regret has absolute finite bound.

   \[
   \forall A,h,\quad(\forall k,A(k)\in[0,1])\Rightarrow |R_A(h)|\le n(h).
   \]

- **constants_and_indices**: Absolute value, not just one-sided upper bound.

- **probability_and_feedback**: All-history A bound plus finite hindsight loss.

- **exclusions_and_boundaries**: Includes empty h with zero; bounds every history, not merely one path.

### B045 — `BanditRL.OnlineLearning.GuessingLower.pathRegret_measurable`

Verdict: accepted-with-explicit-delta. derived producer/helper supporting the qualitative source claim; not a separately printed theorem.

Actual body: Finite sum of measurable squared section evaluations.

- **objects**: Measurable space Ω, family A:Ω→List Bool→R, fixed h

- **quantifier_order**: ∀Ω ∀A satisfying condition ∀h.

- **assumptions**: ∀k, ω↦A(ω,k) measurable.

- **conclusion**: ω↦R_{A_ω}(h) is measurable.

   \[
   \forall\Omega\ [\mathsf M_\Omega]\ \forall A,h,\quad(\forall k,\operatorname{Measurable}(A(\cdot,k)))\Rightarrow\operatorname{Measurable}(\omega\mapsto R_{A_\omega}(h)).
   \]

- **constants_and_indices**: h is fixed; no measure μ needed.

- **probability_and_feedback**: Finite operations on actual per-seed strict-past predictions.

- **exclusions_and_boundaries**: No interval boundedness or integrability conclusion required here.

### B046 — `BanditRL.OnlineLearning.GuessingLower.pathRegret_integrable`

Verdict: accepted-with-explicit-delta. derived producer/helper supporting the qualitative source claim; not a separately printed theorem.

Actual body: Measurability and uniform absolute finite bound under probability measure.

- **objects**: Probability space (Ω,μ), family A, fixed h

- **quantifier_order**: ∀Ω,μ,A satisfying conditions ∀h.

- **assumptions**: μ probability; ∀k A(·,k) measurable; ∀ω,k A(ω,k)∈[0,1].

- **conclusion**: Integrable(ω↦R_{A_ω}(h),μ): actual seed-regret function is Bochner integrable.

   \[
   \forall\Omega,\mu,A,h,\quad\mathcal C(\Omega,\mu,A)\Rightarrow\operatorname{Integrable}(\omega\mapsto R_{A_\omega}(h),\mu).
   \]

- **constants_and_indices**: Finite bound n(h), no positive-length restriction.

- **probability_and_feedback**: Separately establishes legitimate integral meaning, beyond total integral notation.

- **exclusions_and_boundaries**: Empty h zero integrable; pointwise all-history bound, not only a.e.; no nonintegrable fallback being used.

### B047 — `BanditRL.OnlineLearning.GuessingLower.randomized_harmonic_lower`

Verdict: accepted-with-explicit-delta. derived producer/helper supporting the qualitative source claim; not a separately printed theorem.

Actual body: Integrates deterministic lower bound with produced integrability; finite interchange and strict normalized average force one fixed vector.

- **objects**: Probability (Ω,μ), measurable bounded A, positive T

- **quantifier_order**: ∀Ω,μ,A satisfying assumptions ∀T>0, THEN ∃v∈V_T.

- **assumptions**: μ probability; each A(·,h) measurable; every A(ω,h)∈[0,1]; T>0.

- **conclusion**: ∃v∈V_T, H_{T+1}/6≤∫_Ω R_{A_ω}(v)dμ(ω): one fixed sequence has large seed-averaged regret.

   \[
   \forall\Omega,\mu,A,T,\quad[\mathcal C(\Omega,\mu,A)\land T>0]\Rightarrow\exists v\in V_T,\quad H_{T+1}/6\le\int R_{A_\omega}(v)\,d\mu(\omega).
   \]

- **constants_and_indices**: Harmonic T+1, divisor 6.

- **probability_and_feedback**: Witness v outside seed integral; same A_ω trajectory inside R; integrability supported by stated conditions/B046.

- **exclusions_and_boundaries**: Not ∀ω∃v, not per-seed guarantee, not one v for all learners/horizons. No separate joint seed-target independence predicate supplied; T=0 excluded.

### B048 — `BanditRL.OnlineLearning.GuessingLower.randomized_log_lower`

Verdict: accepted-with-explicit-delta. derived producer/helper supporting the qualitative source claim; not a separately printed theorem.

Actual body: Actual harmonic witness and log-harmonic inequality preserve fixed-vector quantifier.

- **objects**: Same probability family as B047 and positive T

- **quantifier_order**: ∀Ω,μ,A satisfying assumptions ∀T>0, THEN ∃v∈V_T.

- **assumptions**: μ probability; per-history measurability; pointwise all-seed/history [0,1] bound; T>0.

- **conclusion**: ∃v∈V_T, log(T+2)/6≤∫_Ω R_{A_ω}(v)dμ(ω).

   \[
   \forall\Omega,\mu,A,T,\quad[\mathcal C(\Omega,\mu,A)\land T>0]\Rightarrow\exists v\in V_T,\quad\log(T+2)/6\le\int R_{A_\omega}(v)\,d\mu(\omega).
   \]

- **constants_and_indices**: Natural log, real T+2, divisor 6.

- **probability_and_feedback**: Fixed witness before averaging over seed; hindsight comparator from same v.

- **exclusions_and_boundaries**: No a.s./high-probability claim, adaptive seed-specific target, average-by-T or anytime assertion; T=0 excluded.

### B049 — `GuessingLogLowerProbe.unbalanced_probability`

Verdict: accepted-with-explicit-delta. validation-only canary.

Actual body: Exact 4/5 plus produced strict probability.

- **objects**: Fixed h=[true,true,true]

- **quantifier_order**: Closed numerical conjunction.

- **assumptions**: None.

- **conclusion**: q([true,true,true])=4/5 ∧ q([true,true,true])∈(0,1).

   \[
   q([1,1,1])=4/5\ \land\ q([1,1,1])\in(0,1).
   \]

- **constants_and_indices**: k=3,n=3.

- **probability_and_feedback**: Numerical ratio check, no universally quantified performance result.

- **exclusions_and_boundaries**: All-true history does not force q=1.

### B050 — `GuessingLogLowerProbe.correlated_two_step_masses`

Verdict: accepted-with-explicit-delta. validation-only canary.

Actual body: Exact dependent two-bit masses differ from IID quarters.

- **objects**: Four fixed length-two lists

- **quantifier_order**: Closed conjunction.

- **assumptions**: None.

- **conclusion**: w([true,true])=1/3 ∧ w([false,false])=1/3 ∧ w([true,false])=1/6 ∧ w([false,true])=1/6.

   \[
   w([1,1])=1/3\ \land\ w([0,0])=1/3\ \land\ w([1,0])=1/6\ \land\ w([0,1])=1/6.
   \]

- **constants_and_indices**: Exact four real weights.

- **probability_and_feedback**: Newest-first list interpretation retained; weights not independent fair-coin 1/4.

- **exclusions_and_boundaries**: Does not alone assert symmetry/all-length formula beyond these lists.

### B051 — `GuessingLogLowerProbe.zero_and_two_normalization`

Verdict: accepted-with-explicit-delta. validation-only canary.

Actual body: Invokes actual normalization at zero and two.

- **objects**: Lengths zero and two

- **quantifier_order**: Closed conjunction.

- **assumptions**: None.

- **conclusion**: Σ_{v∈V_0}w(v)=1 ∧ Σ_{v∈V_2}w(v)=1.

   \[
   \sum_{v\in V_0}w(v)=1\ \land\ \sum_{v\in V_2}w(v)=1.
   \]

- **constants_and_indices**: Unit total at both specified lengths.

- **probability_and_feedback**: Finite normalization canaries.

- **exclusions_and_boundaries**: Empty vector present at T=0; no empty sample space.

### B052 — `GuessingLogLowerProbe.correlated_moments`

Verdict: accepted-with-explicit-delta. validation-only canary.

Actual body: Invokes actual moments at two.

- **objects**: T=2 first and second count moments

- **quantifier_order**: Closed conjunction.

- **assumptions**: None.

- **conclusion**: E_2[k]=1 ∧ E_2[k²]=5/3.

   \[
   E_2[k]=1\ \land\ E_2[k^2]=5/3.
   \]

- **constants_and_indices**: Second raw moment 5/3, not squared mean 1.

- **probability_and_feedback**: Finite weighted numerical tests.

- **exclusions_and_boundaries**: Does not itself quantify all T.

### B053 — `GuessingLogLowerProbe.averaged_variance`

Verdict: accepted-with-explicit-delta. validation-only canary.

Actual body: Invokes actual variance at two.

- **objects**: T=2 and q(1−q)

- **quantifier_order**: Closed numerical statement.

- **assumptions**: None.

- **conclusion**: E_2[q(1−q)]=5/24.

   \[
   E_2[q(1-q)]=5/24.
   \]

- **constants_and_indices**: Exact fraction.

- **probability_and_feedback**: Finite functional, no extra sampled object.

- **exclusions_and_boundaries**: No asymptotic approximation or inequality.

### B054 — `GuessingLogLowerProbe.same_past_different_current`

Verdict: accepted-with-explicit-delta. validation-only canary.

Actual body: Actual prefix theorem under different current bits.

- **objects**: A=q; lists [true,false] and [false,false]; time 1

- **quantifier_order**: Closed equality.

- **assumptions**: None.

- **conclusion**: x_1(q,y^B_[true,false])=x_1(q,y^B_[false,false]): same prediction from same oldest false bit.

   \[
   x_1(q,y^B_{[1,0]})=x_1(q,y^B_{[0,0]}).
   \]

- **constants_and_indices**: Both equal q([false])=1/3.

- **probability_and_feedback**: Current chronological bits differ, yet strict-past input agrees.

- **exclusions_and_boundaries**: Not full-list equality or equal predictions after observing the differing current bit.

### B055 — `GuessingLogLowerProbe.actual_last_prediction`

Verdict: accepted-with-explicit-delta. validation-only canary.

Actual body: Actual last-prediction history identity.

- **objects**: A=q, list [true,true,false], time 2

- **quantifier_order**: Closed numerical statement.

- **assumptions**: None.

- **conclusion**: x_2(q,y^B_[true,true,false])=1/2.

   \[
   x_2(q,y^B_{[1,1,0]})=1/2.
   \]

- **constants_and_indices**: Chronological past [false,true], presented to A as [true,false].

- **probability_and_feedback**: Current third true bit is excluded from prediction.

- **exclusions_and_boundaries**: Using full h would instead give 3/5; target concerns actual strict past.

### B056 — `GuessingLogLowerProbe.nondegenerate_actual_regret`

Verdict: accepted-with-explicit-delta. validation-only canary.

Actual body: Actual learner recursion and comparator count yield 13/36.

- **objects**: A=q and list [true,true]

- **quantifier_order**: Closed numerical statement.

- **assumptions**: None.

- **conclusion**: R_q([true,true])=13/36.

   \[
   R_q([1,1])=13/36.
   \]

- **constants_and_indices**: Learner loss 1/4+1/9; hindsight constant-one loss zero.

- **probability_and_feedback**: Actual q([])=1/2 then q([true])=2/3 path.

- **exclusions_and_boundaries**: This is one-sequence value, not E_2 regret.

### B057 — `GuessingLogLowerProbe.actual_optimal_loss`

Verdict: accepted-with-explicit-delta. validation-only canary.

Actual body: Actual comparator count yields 1/2.

- **objects**: h=[true,false]

- **quantifier_order**: Closed numerical statement.

- **assumptions**: None.

- **conclusion**: C([true,false])=1/2.

   \[
   C([1,0])=1/2.
   \]

- **constants_and_indices**: Mean 1/2; two deviations each 1/4.

- **probability_and_feedback**: Full-sequence hindsight loss, not prediction loss.

- **exclusions_and_boundaries**: Order reversal does not change this comparator loss.

### B058 — `GuessingLogLowerProbe.one_step_harmonic_endpoint`

Verdict: accepted-with-explicit-delta. validation-only canary.

Actual body: Actual expected-regret terminal at one gives 1/4.

- **objects**: A=q and T=1

- **quantifier_order**: Closed inequality.

- **assumptions**: None.

- **conclusion**: 1/4≤E_1[R_q].

   \[
   1/4\le E_1[R_q].
   \]

- **constants_and_indices**: Exact lower constant 1/4; actual weighted value also 1/4.

- **probability_and_feedback**: Finite expected regret canary with zero singleton hindsight loss.

- **exclusions_and_boundaries**: Not a claim for empty horizon or arbitrary A by this closed test.

### B059 — `GuessingLogLowerProbe.coin_distribution`

Verdict: accepted-with-explicit-delta. validation-only canary.

Actual body: Produces two fair seed weights nonnegative and summing one.

- **objects**: Bool finite arms and weights 1/2

- **quantifier_order**: Closed P predicate.

- **assumptions**: None.

- **conclusion**: P(univ_Bool,b↦1/2): both weights nonnegative and sum one.

   \[
   P(\{\mathrm{false},\mathrm{true}\},b\mapsto1/2).
   \]

- **constants_and_indices**: Two arms, exact halves.

- **probability_and_feedback**: Normalization of seed weights for f11.

- **exclusions_and_boundaries**: No assertion about arbitrary real weight or seed type.

### B060 — `GuessingLogLowerProbe.seeded_policy_bounds`

Verdict: accepted-with-explicit-delta. validation-only canary.

Actual body: Boolean case split gives all-history bounds.

- **objects**: Boolean b and arbitrary history h

- **quantifier_order**: ∀b:Bool ∀h:List Bool.

- **assumptions**: None.

- **conclusion**: A^b(h)∈[0,1]: the fixed-bit predictor f12 is bounded.

   \[
   \forall b,h,\quad A^b(h)\in[0,1].
   \]

- **constants_and_indices**: Values exactly 1 or 0.

- **probability_and_feedback**: Predictor ignores all history, retaining its seed choice.

- **exclusions_and_boundaries**: Every history including empty; not a newly resampled seed per round.

### B061 — `GuessingLogLowerProbe.genuine_coin_policy`

Verdict: accepted-with-explicit-delta. validation-only canary.

Actual body: Distinct seed predictions and both singleton masses prove nontrivial seed.

- **objects**: Fixed seed predictor evaluations and ν=f11

- **quantifier_order**: Closed four-conjunct statement.

- **assumptions**: None.

- **conclusion**: A^true([])=1 ∧ A^false([])=0 ∧ ν({true})=1/2 ∧ ν({false})=1/2.

   \[
   A^{\mathrm{true}}([])=1\ \land\ A^{\mathrm{false}}([])=0\ \land\ \nu(\{\mathrm{true}\})=1/2\ \land\ \nu(\{\mathrm{false}\})=1/2.
   \]

- **constants_and_indices**: Measure halves are ENNReal; predictor values real.

- **probability_and_feedback**: Two-atom seed law and deterministic per-seed predictors.

- **exclusions_and_boundaries**: Singleton mass statement is distinct from a full independence assertion.

### B062 — `GuessingLogLowerProbe.seeded_fixed_sequence_endpoint`

Verdict: accepted-with-explicit-delta. validation-only canary.

Actual body: Invokes actual randomized harmonic producer with genuine coin law.

- **objects**: Fixed Bool seed law ν, family A^b, T=2

- **quantifier_order**: Closed existential ∃v∈V_2 before seed integral.

- **assumptions**: None beyond fixed definitions.

- **conclusion**: ∃v∈V_2, 11/36≤∫_Bool R_{A^b}(v)dν(b).

   \[
   \exists v\in V_2,\quad11/36\le\int R_{A^b}(v)\,d\nu(b).
   \]

- **constants_and_indices**: 11/36=H_3/6; exact constant.

- **probability_and_feedback**: One v for both seed branches in the average, not seed-dependent selection.

- **exclusions_and_boundaries**: No specified witness in target; not per-seed lower bound or universal over sequences.

### B063 — `GuessingLogLowerProbe.seeded_log_endpoint`

Verdict: accepted-with-explicit-delta. validation-only canary.

Actual body: Invokes actual randomized logarithmic producer with genuine coin law.

- **objects**: Same fixed Bool randomized learner, T=2

- **quantifier_order**: Closed existential ∃v∈V_2.

- **assumptions**: None beyond fixed definitions.

- **conclusion**: ∃v∈V_2, log(4)/6≤∫_Bool R_{A^b}(v)dν(b).

   \[
   \exists v\in V_2,\quad\log4/6\le\int R_{A^b}(v)\,d\nu(b).
   \]

- **constants_and_indices**: Log 4, divisor 6.

- **probability_and_feedback**: Witness fixed before averaging; atomic finite integral.

- **exclusions_and_boundaries**: Not a high-probability or every-sequence statement.

### B064 — `GuessingLogLowerProbe.deterministic_fixed_sequence_endpoint`

Verdict: accepted-with-explicit-delta. validation-only canary.

Actual body: Dirac seed specialization invokes actual randomized endpoint.

- **objects**: Deterministic A=q and positive natural T

- **quantifier_order**: ∀T>0, ∃v∈V_T.

- **assumptions**: T>0.

- **conclusion**: ∃v∈V_T, log(T+2)/6≤R_q(v): some target sequence forces this deterministic predictor's regret.

   \[
   \forall T,\quad T>0\Rightarrow\exists v\in V_T,\quad\log(T+2)/6\le R_q(v).
   \]

- **constants_and_indices**: Same horizon in length, log argument and regret.

- **probability_and_feedback**: Actual newest-first q predictions versus same sequence's hindsight mean; no seed average.

- **exclusions_and_boundaries**: Witness can depend on T; not one infinite sequence simultaneously for all T; T=0 excluded.

## Unchanged future reader requirements

```json
[
  {
    "id": "R1",
    "requirement": "Attribute the qualitative logarithmic-unavoidability sentence to printed4/PDF16, explicitly note that no minimax-optimality proof is printed there, and label H(T+1)/6 and log(T+2)/6 as derived support constants, not printed or sharp constants.",
    "status": "future mandatory"
  },
  {
    "id": "R2",
    "requirement": "Show the actual newest-first recursive path law q=(heads+1)/(length+2), w(empty)=1 and branch multiplication; it depends on neither policy nor seed. Normalization/nonnegativity and the shared finite-action probability/integral construction must be produced, not assumed.",
    "status": "future mandatory"
  },
  {
    "id": "R3",
    "requirement": "Explain strict-past causalPredict reversal and current-label-after-output order, source1/Lean0 indexing, and the SAME pathRegret/shared comparatorRegret and empirical-mean comparator. Prove actual binary mean feasibility/minimality rather than assuming an argmin or using a different trajectory.",
    "status": "future mandatory"
  },
  {
    "id": "R4",
    "requirement": "Display the complete randomized quantifier order: every probability seed law and per-history measurable, pointwise all-seed/all-history [0,1]-valued policy; every positive T; exists ONE fixed binary sequence outside the seed integral. Explain integrability production, not Bochner fallback; no seed-dependent witness, almost-sure/high-probability/uniform-seed or one-infinite-sequence guarantee.",
    "status": "future mandatory"
  },
  {
    "id": "R5",
    "requirement": "Expose the actual count moments, variance, cumulative causal-loss bridge, expected optimum and finite normalized-average bad-sequence producer; no desired-regret/moment/normalization/minimum certificate may stand in as a terminal premise. Distinguish proof dependencies from a teaching plan.",
    "status": "future mandatory"
  },
  {
    "id": "R6",
    "requirement": "Retain all boundary conditions: T0 law/moments are total, lower terminals require T>=1, q(empty)=1/2, binary adversary labels are legal source labels while learner outputs are real [0,1], deterministic intermediate may be unbounded, cumulative regret is signed and coefficients/index shifts are exact.",
    "status": "future mandatory"
  },
  {
    "id": "R7",
    "requirement": "Provide meaningful actual validation canaries for causality, small-horizon normalization/moments and nondegenerate regret, deterministic and nontrivial seeded terminal use, and distinguish them from the universal producer. Verify complete rendered formulas, assumptions and actual pixels at FINAL without treating typechecks as theorem proofs.",
    "status": "future mandatory"
  },
  {
    "id": "R8",
    "requirement": "Reuse the shared Regret/Mean/finite-action probability definitions; preserve old source statements/cards/registry/scanner/pins. Limit acceptance to C1-LOG-UNAVOIDABLE after full proofs and gates; keep all other Chapter1/fullRegret/NoRegret/six main gaps,16sourceitems/nullproof-total, Chapter2, unenumerated3–16 and necessary appendices open with Goal ACTIVE. No main/live/merge or chapter completion.",
    "status": "future mandatory"
  }
]
```

## Raw input bindings

| Path | SHA-256 |
|---|---|
| `docs/contracts/online-guessing-log-lower-v1/.gitattributes` | `705fd4d6451a31d36b3df7de96f83f30ac976c9b4a6d1e51671d8e2f33e2d0da` |
| `docs/contracts/online-guessing-log-lower-v1/contract-v1.md` | `0a23cc844787b8a791772a75a620b0a7cc23cfdb9e471c14283db1bf4e3db28e` |
| `docs/contracts/online-guessing-log-lower-v1/dependency-DAG-v1.json` | `132ddc62d6b873ea47515276d43ba218a5266d9bd26b86dcfd67e01e2a3339fd` |
| `docs/contracts/online-guessing-log-lower-v1/planned-definitions-v1.lean.txt` | `5c219f792d87961c27eefee4e5b8f782af2ba64269d0e7cbbe0b74268d233d8f` |
| `docs/contracts/online-guessing-log-lower-v1/planned-public-headers-v1.json` | `71ecce15fe375431ef6a2d4625cbb4bf650a996fe6b3dc9fb366fe76066cc7af` |
| `docs/contracts/online-guessing-log-lower-v1/planned-statement-fingerprints-v1.json` | `e3dbb0e1b07fd1f395a66029b0f9d183588de82260966cfdf3481524158b68ef` |
| `docs/contracts/online-guessing-log-lower-v1/semantic-signature-v1.json` | `22d425631c72598e6bba4afb50fba79c56a360d9cad1c1e17139fb17e4607516` |
| `docs/contracts/online-guessing-log-lower-v1/source-card-v1.json` | `523fac217e3c033e00a70bbcf7648f086b393dc899b7828d49bcca8c0c175046` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/.gitattributes` | `705fd4d6451a31d36b3df7de96f83f30ac976c9b4a6d1e51671d8e2f33e2d0da` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/00_context.md` | `f16dfbc895cbaf527e58edf7b9a5d4774cb8696d600f447849a0163317dc9ac9` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/10_upper_director.md` | `365defa6f22de3e812efe5c52393f25899287217095d0839e5b9fd82403e2a03` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/20_middle_formalizer.md` | `52ffa12d81864241bf858ab92f1c2fe608d76a1bddc9ac705cea2d59475dd4e7` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/30_lower_architect.md` | `d5527c533e797cb655480b555edf5b32c5b92a0625494944915c1015f0d89f17` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/base-PR190-fresh-v1.json` | `0f526d8beff1c97326f6f1552a29e3e57c66bb8d65a0b07d21212d50b1736323` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/blind-binding-audit-v1.json` | `90b49ed300a4dcf4b8d1396b7e8f12e47b0c83ee4b1798c925dcbeec2bb2ba90` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/blind-decoder-receipt-v1.json` | `7e776bdae1d712a05c495b3219afba05645e4181881dc09b69c53738aed38e2c` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/blind-decoder-v1.md` | `7da5da4fe209bc8d03fc2d0a60cb79eeaea9aeb585cc2580ef83204448802480` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/canonical-worktree-audit-v1.json` | `e28832f1613443ab34a8d121165e987c008224f73cf4aa4cdddeaf0253806952` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/common_v1.py` | `30514a76aab40ec784ad69729e945cd3ec81a77222e6009e9890b3296d129797` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/current-API-types-v1-exit.json` | `7456b0028a5f7ba05a99300d6ac3ade44f8225a1c12e76f2a31478d8d9033dd8` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/current-API-types-v1.log` | `37c49c54ae39dbfb8a4e32bf51b0545bc436cc132a23537f8cc6afb5ba350b72` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/current-lean-version-v1-exit.json` | `6e8e0ba4800053dd0abd5ebac077b875c84a1c0b52e2984180dd829bb1475337` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/current-lean-version-v1.log` | `e77960cdfb8d64df3da4367afc3bd4c528ba980f6bc7e4cea99129226781ba10` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/current-mathlib-pin-v1-exit.json` | `90b922c872951fd3ed458724fd40dcd61a0c3aa06f0651c1936c17169d4f0f6a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/current-mathlib-pin-v1.log` | `884fab88619a3d1adcafe89eecddd2d98f4be5c6fa61262862134dde9e51d225` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/draft-event-v1-exit.json` | `b2fe4b491880ae2881a409f596ec715570f3a302f9a060f228774655c485b197` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/draft-event-v1.log` | `3ee05ac5189421283bbaf6918b607a99b126dd374a62b54610a12e6822b56a66` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/draft-freeze-v1.json` | `f65ba8ba162e972b885130b0d7b31ec51eff38420bcd195d7bfa01371d24ef5d` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/existing-shared-distribution-v1-exit.json` | `6f938ff4063c24ed2444144b6bf9fd4dc142741988065b00c126cd14ab41761d` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/existing-shared-distribution-v1.log` | `8a43f2f600188fa07f414764697e33dec20202a91952fc1e35b53ff486d6d40d` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/existing-shared-mean-v1-exit.json` | `81c12838907ea69b8a15c45a722ed1bbd8874c8eab24125df7897fe7acaa822f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/existing-shared-mean-v1.log` | `d28a2e86b3aab003e639c06fb152abea410d2cacf03132c74151e8ef332e85d5` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/existing-shared-regret-v1-exit.json` | `29a57e652c2c0753fcc1441f9f263cae6fbf4f8e86832d0a590a409660fb3c4c` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/existing-shared-regret-v1.log` | `01a55234e05ff55ec3c90a70a795b611362b756389cac7436eb6a29bb4d4bd8e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/fresh-fetch-v1-exit.json` | `fae9139d75dcb786cb176d2208f41039ee63d6221ddfeef2e3b156b5a358c20d` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/fresh-fetch-v1.log` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/help-frontier-refresh-v1-exit.json` | `6cd7cd30e2ad0223b0bba3d694ecf98844ef82d9f3f15cf80524aed0ae0fcedc` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/help-frontier-refresh-v1.log` | `bff73ff554907d7c5dd50b99f2491f5675e93afb29829e402ec383fb52fe3cdc` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/help-frontier-shadow-v1-exit.json` | `74da8f3eb10ace738bb5780c306d2df4d1c7ac74b89507a4c55428ea28c65715` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/help-frontier-shadow-v1.log` | `ad548f6e24b3214fbf5796c632caa24debbaa21c6622f7dab8abe268f521de7d` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/help-lifecycle-event-v1-exit.json` | `edb92cdef23e05737503788a9dad64cdbab51db475ea8b4fabf4a59315844584` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/help-lifecycle-event-v1.log` | `b1e8b438a9b725793b9888d206e98a971ace3df200ec90ed9cb63eab26b28507` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/help-list-lean-decls-v1-exit.json` | `26f441532e701869657195de5433eff92f0321ccb872b3f02dc10906fbd36187` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/help-list-lean-decls-v1.log` | `258218f16a12b1a530d85ae83e6c2449237af8a0a1153bb35de40245d665b131` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/help-list-mathlib-v1-exit.json` | `f88b81aa2fe34dae0d5679fc6a6793c8f477ad744196f2513523f59b0dbc7d8d` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/help-list-mathlib-v1.log` | `eedc3e9609fdc7a3bcf76443a33933477de80dcc4ec9906b64a691e29b207e9d` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/help-memory-record-v1-exit.json` | `4e9341031a8fe1d892afe7d6472ca4bf5b34d079a600cad062350cd0177c7ebc` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/help-memory-record-v1.log` | `89e8a7b2bb8d4fd593f0705289ca3c4c63015e48d0e8c9cbe5b71cf2c7cc44f4` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/help-new-task-v1-exit.json` | `4b4fa3596b295c5c7f4c36a6d87c1ce0126e5d0c034e99f7a8a3b9a2b69c4346` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/help-new-task-v1.log` | `25eb9342c3094bee57187630bd149d2c522fc9f7ac7e65bebe5c198eba60ed99` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/help-retrieval-record-v1-exit.json` | `7884a447850748fd831d8d1a7ef74956bcea38eebb14f07551a941713c55a21e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/help-retrieval-record-v1.log` | `73ac93f120215511ff0370d7ce100a9d0e83598ad882bcc5773cd1dc889b5321` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/help-safe-verify-v1-exit.json` | `9bd7d2930ac9f0faf4388643ced4d028418cbe7535f51c1bf217e75fc266a4f5` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/help-safe-verify-v1.log` | `1773541c625f225e5a9abc61985c3ad19e871cf31aa0cf89cc440b3d8398862c` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/help-statement-fence-v1-exit.json` | `29c9a276e91b1bf3228b16d13be380527822f0478bcc19886893f1b7a1e9baae` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/help-statement-fence-v1.log` | `4f4fca9dfaac7a7c3de8025d3d0f7c4ba58d1f4b33feb08d19e12229942dba75` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/help-trial-log-v1-exit.json` | `50013d7c03df29ff98efe4c0c1870465561d55b1eae50575bd7b81935a6de482` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/help-trial-log-v1.log` | `ea7bd7e4d64216b46f554a90e02a3d58b4fcbe72766c2f7b316b656b94d19b32` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/initialize-v1.py` | `929eabf22c92b1fa0f01b21939f3e1e2b4bb06174f5124072ddd2bdca5e6d45e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/leaves/current-API-types-v1.lean` | `dea443167bdbbf62e5ef80b46f4b966041ede4004310e0e22b857eef3da96eb3` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/leaves/planned-types-v1.lean` | `da892db4900b09111c196a8a73296e73ead89a46d285374f283cf3c7329d64f2` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/memory_digest.md` | `11243e4c33a482cfede7015f744667a20a200b217cd8f9127feed8ddfc59c6b5` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/neutral-input-v1.json` | `b552f75a7d0869e20a95329907a9158ecb576abec329fa16537f3804336e5604` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/neutral-packet-v1.lean` | `9e632a51200cec25fffe42fc315c001f1035184a3198fda41d6476aaf83829eb` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/neutral-types-v1-exit.json` | `8352dbeb2e241e34d4fcfaf17e78a8264387dd916a6823f25b423706f8c317bc` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/neutral-types-v1.log` | `bd3e2f0f20da5b91dc8c4720874efd5f9c43abab339db0ae2eb86dd4083f5cd8` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/new-task-v1-exit.json` | `622d0a0d3002fae08f5573e597110fd3db415fc75dd2f33894ea0219e6fbda3f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/new-task-v1.log` | `fe35702b9bc82a45b3a0bee7502dd92662b07e4bfb4ea20719052c44751114bb` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/owned-commit-paths-v1.json` | `953d6d35e4fdc08b5270e7cf9f41c93d168c33817ff890d7efddceb3d6e3235f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/paper-boundary-v1.json` | `4b85e7690280863c2a4b3eaab46118453ac1aec397ef8563c47f7567bd57b4f5` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/planned-types-v1-exit.json` | `603e456a7cf0a72f8602f7240d5896e544b08f19294eac185a482f200a82aede` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/planned-types-v1.log` | `f9baaa155154964d0bc943e737d745f4f228697ef5fad1918a0252ca5a395098` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/preparation-schema-repair-event-v2-exit.json` | `5a3380762592129b0c1c3054761012ee1c1fb1829dbc02dc21b2c83c50055a66` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/preparation-schema-repair-event-v2.log` | `6b6964034f245bbb3e05a8ccaf75e04fd204609606e4584e265c0ab834a037de` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/preparation-schema-repair-v2.json` | `8d017374ebbcf95b4644af514f4328ef513aa0a83a0bce4e737567ad72e32dc7` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/prepare-contract-v1.py` | `0583d2a148c0117b4df45b57be54f4e1937fe6167142d9ec2a4a8c5ffeeef245` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/prepare-source-review-v1.py` | `cad7aba07946e8f52a3ce5ee0326f03997ae232324323e01d421756c71229cc2` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/prepare-source-review-v2.log` | `db3044b6eb40f5dea862cc3548b6e9b36a68bb327c295f04f1ee83a1fd70c8d9` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/prepare-source-review-v2.py` | `13e70ff91438487763c010d44a2cbf1bc86388fede21c4e5ef34a8039fef2006` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/render-source-v1-exit.json` | `79d760d045846b1beb52168b846f23f5444ed834aa5d8d001c91c9d7f5baa843` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/render-source-v1.log` | `3d3bffa7502670613201c5ad954d0784675f2b142a158dcc60dbcb4ba470ffe4` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/render-source-v1.py` | `07881acee8d6890d3590215c36e014186dec1f538cb7764030d90c87e0a46290` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/repair-preparation-v2.py` | `7c182e3b8ce4f5060b6ba5ebd9999dfc62b5a82be6f512200ce43b2345af8273` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/retrieval-initial-v1.json` | `bc0c72a6da5164e8d96140617a3e3afaa28ecb5486df993aff95b0b52f8bb08a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/BanditRLProof--OnlineGuessingComparison.lean.raw` | `0fc28f4459d2cffb5afcf795898dd152508ddb06acb356cb08d1dd72e09f7f14` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/BanditRLProof--OnlineGuessingLower.lean.raw` | `a09390e250f7e55e8e9d282995faedaf186ecf67d8c1aa177e6f8d08ee5428e7` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/BanditRLProof--OnlineGuessingOGD.lean.raw` | `12792af1571fde0fe37796686b044f0df0990ca3d808a89431804605d0ee8d00` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/BanditRLProof--OnlineGuessingSubgradient.lean.raw` | `95d206190d443939115037f9bf6d0eeb1e3229f3ae52eb4150927fbe69e89348` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/BanditRLProof--OnlineGuessingSubgradientPolicy.lean.raw` | `ed32d846509d0dc34eb05ce6fad5d3af8aa6dbf92a8c8a78cc8859b0e42e6b0e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/BanditRLProof--OnlineLearningAsymptotic.lean.raw` | `4d704d07b9616ca48a1ee56d47af7f5f8ca9e3797d2a9b47d373038a25d79d59` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/BanditRLProof--OnlineLearningFoundations.lean.raw` | `e23ebdca2f7ce21a16173c93390fd24d16ba36e403c9d084233f7480e75408b8` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/BanditRLProof--OnlineLearningFTL.lean.raw` | `8c3574c657f08e0c5291f0689105f9459e92187502f092f4d36d848e52ab4219` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/BanditRLProof--OnlineLearningFTLState.lean.raw` | `fa33c10252eb5cd51b3ea4cdffb10fa95c37416f3098ceb76d9d58f465ff1765` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/BanditRLProof--OnlineLearningHistory.lean.raw` | `3412177ab7dd0ac0e350d8fde7f91e61640d55743d1f17d15c62a65dd4492fc7` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/BanditRLProof--OnlineLearningIID.lean.raw` | `92af24e6a2c2b1054503492b2bad97cd17ccea2217439f6d2f8a7bedb0de3d5e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/BanditRLProof--OnlineLearningInformation.lean.raw` | `72bef017a43c293d0d3c449707e4a0e058f4655c2483b54c3120d7b41c98135a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/BanditRLProof--OnlineLearningMean.lean.raw` | `811dcf3741e3d6dee19b2c4a9f43f4b266808b89843a1719e00f239a4687258b` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/BanditRLProof--OnlineLearningRegret.lean.raw` | `0bac6b6e454c5d7bd2244fc115bc8df8cbd9b5505302aa81d03baaeeeec204dc` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/BanditRLProof--OnlineLearningStochastic.lean.raw` | `0242481022883958afef677654fadd3f6e37b381f3fe463e3605f3eb0542f2bd` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/BanditRLProof.lean.raw` | `55cfcdaf2b28f0e55ef4326060c861919e9dc3f69fbaac31c6563e4d16135e67` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/CONTRACT-review-conversion-windows--ONLINE-GUESSING-LOG-LOWER-20261008.md.raw` | `8ac3c529d2e0db67496c33287304b664da646d9dad7b322ce790eebb8f27f29f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/CONTRACT-review-proof-blueprints--ONLINE-GUESSING-LOG-LOWER-20261008.md.raw` | `35d1ba3f61ca2c2591fc43f9e48b06f62af79c575df79bca620066806a2c6e85` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/CONTRACT-review-proof-obligations--ONLINE-GUESSING-LOG-LOWER-20261008.md.raw` | `e2500ef474fc22411d9cd2cc1f50e5e6cfdf4994146259d9c2b13c2b21010cae` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/CONTRACT-review-research-wiki--retrieval-index--ONLINE-GUESSING-LOG-LOWER-20261008.md.raw` | `35d1ba3f61ca2c2591fc43f9e48b06f62af79c575df79bca620066806a2c6e85` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/CONTRACT-review-tasks--ONLINE-GUESSING-LOG-LOWER-20261008.md.raw` | `85d024f10253eaee51f640ef421f30e9461f77a76e8a2f8d1906cf31f11f98c2` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/docs--contracts--online-book-v1--coverage.json.raw` | `fd7580c2d0ec040352317d3c53dc583a6b9b75a68b4026ebf3b38f7010a98f1e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/docs--contracts--online-book-v1--source-inventory.json.raw` | `a2a504cf40d73f9c5e36f00fc1ef3b949ccaf5a558ab603c1c2a86007f30efa7` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/lake-manifest.json.raw` | `87c3e616f86244550ef39e7415186b11c1d4cf4bef20173196a619d9d4d48f48` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/lakefile.lean.raw` | `0164f3b5b5bdcbb237ab15ae8b44da83e183f4b97d5f3832aa4a57f27dc69d45` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/lean-toolchain.raw` | `b15a57f8ea4c890197465ce1156667ae13d9ed4ab8a9f263a920bf010d967d82` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/MANIFEST.md.raw` | `4a3e05afd265f465fccf76becdf7a749f3dd63f74f1c33fc6339241d57b437fd` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/prior-readonly-online-log-lower-api-v1.lean.raw` | `ab3262aa37cc810d80eb1e563a1b5bb87b2bd376c902908eff33338f3f2a15e8` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/prior-readonly-online-log-lower-api-v1.log.raw` | `488aa9920f2845ca46d32ca53c4855cbae1d5428357aed91becb1b1614c02dd8` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/prior-readonly-online-log-lower-api-v2-exit.json.raw` | `ba0385d9ddf16ad0af1baebf830dd33d38ea9f40965c8a15a9f8e7b966b841ad` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/prior-readonly-online-log-lower-api-v2.log.raw` | `4ef33c0c17b9fcdd99519fe1b852626506a9cd01e320efc9a3a7b3e9a15f7989` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/runs--active_frontier.json.raw` | `567e5873aa2549a83f2820d758069213808da822a93087129877385a1addf7c3` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/runs--lifecycle_memory.jsonl.raw` | `94be3ceb994768191ceb6a7545935c8d16c044511dfe8c4482e2fde493eaa5f8` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/runs--lifecycle_sessions.jsonl.raw` | `124dc2affbd0c75ef90455bcc17db55523eb71b3bcaac72fc4e5e18eddfb90a3` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/runs--online-regret-domains-20261007--accepted-decision-v1.json.raw` | `99e8ecc2c266d70624085d23f56d4faa16ce9cf15bee9145c34e3dd8744b9a67` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/runs--online-regret-domains-20261007--delivery-obligations-overlay-v1.json.raw` | `c95e61f5bf8bb41819c0795a469c27decaff36ccf1adb84344618ac1986e0dca` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/runs--online-regret-domains-20261007--final-reader-receipt-v1.json.raw` | `abae24c08ec1d21238d5e63b0ffc2305c39ec84c9648416bd7e42a05d1af975a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/runs--trials.jsonl.raw` | `b96cac6f18b967cb8ef8710eac9596c3de8897a80c1f856f3965eca8b8528b08` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/Tests.lean.raw` | `a2e1fc1ff9d41b4c27f443b1865962908ba87291b921476aef681e02bef8eba8` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/website--content--chapters.json.raw` | `e471c0acacb9e48f3cfa24849a4cd3d4385317cf1c21c53d7fff8a3959c26300` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/website--content--declaration-boundaries.json.raw` | `6806d5fc69f3ebd42814f502f27afc1295369a80d3c0fbb6f7c59f6c57fdbbe9` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/website--content--highlights.json.raw` | `9ea5f8ecf47579a85d72268c44d6c00ece458b60ee57102bc16887456cd45ea3` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/website--content--readings.json.raw` | `fbda5ccc1ed0b1e65fe2cf69e8bd984cfb0934ec0970bbe9c41232ae66f4ed7c` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/website--scripts--build_site.py.raw` | `4fe18b8b9a543ff5256a278f49d160424b30ba2185c946f3d6081ad5460ccaff` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/source-contract-review-packet-v1.md` | `1fc97be3ad5fb13fa239ec4a91d8540fc98a9e09552550583296c3cf7185a557` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/source-pdf14-v1.txt` | `3f9d01aee6e81504b7ca2ef0d9657bc1ee30f36eb54a957b8018c4d0c3e2ac66` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/source-pdf15-v1.txt` | `037b6d907a868c339b881162333f6e56352cbebf285902eb6ed628ff4f8bd947` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/source-pdf16-v1.png` | `d2620e7f6c8d60839ae426eddb470eb56f226807ad6b744f73d15267e5252657` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/source-pdf16-v1.txt` | `b8fe01f6c31bf15cfb67ea948a832f97e2c77f9e1f569a36fd9fa72e831796ee` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/source-pdf17-v1.txt` | `164b4ca2261475aeadaf633ce67afbf8a221f612b8f4db801c36ea75081263e8` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/source-pdf18-v1.txt` | `bec2bd23e52551c2f353a7dec52c99582185e812f99a24f55983f209007eb484` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/source-pixel-review-v1.json` | `b059ec6ab119a98390b4c84bb078beae85e797991f5d46a52279a315a31e4ebd` |
| `BanditRLProof/OnlineLearningRegret.lean` | `0bac6b6e454c5d7bd2244fc115bc8df8cbd9b5505302aa81d03baaeeeec204dc` |
| `BanditRLProof/OnlineLearningMean.lean` | `811dcf3741e3d6dee19b2c4a9f43f4b266808b89843a1719e00f239a4687258b` |
| `BanditRLProof/OnlineLearningFTLState.lean` | `fa33c10252eb5cd51b3ea4cdffb10fa95c37416f3098ceb76d9d58f465ff1765` |
| `BanditRLProof/Exp3ConditionalMoments.lean` | `e0d4683319f42d26745fa8f411d50fd2c0abf6f75f19d81177cc9b03814935ba` |
| `BanditRLProof/OnlineGuessingLower.lean` | `a09390e250f7e55e8e9d282995faedaf186ecf67d8c1aa177e6f8d08ee5428e7` |
| `.lake/packages/mathlib/Mathlib/Data/List/Count.lean` | `b0ffe1488d210796008404520d9c99985a98cbc7cf87964686033d115ccf1613` |
| `.lake/packages/mathlib/Mathlib/Data/Fintype/Vector.lean` | `6c08ffb94f10060c874848b7c1fa0059b2a4de12924ef3afcf20df1a15e1a2af` |
| `.lake/packages/mathlib/Mathlib/Data/Vector/Basic.lean` | `27e556fa56f351a80d7a945c21ae50bd3ff116271ffdafe5b01ddde33538989b` |
| `.lake/packages/mathlib/Mathlib/NumberTheory/Harmonic/Bounds.lean` | `92f1c8224c4353a057c306ea1b8f35ff51e02b82462916fcd5820491fce11db5` |
| `.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean` | `ce6b984f1a4b0ba00688574d9e90785a5d5a7f7c27c3230c501909792d0e2495` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/freeze-source-review-v3.py` | `a1d0d96076bc65d043a0e83404430d04acdb46d06cd777703aa8ce9a93c264b2` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/preparation-freeze-repair-event-v3-exit.json` | `ff4c4f1e374c400f1c65d74319dc29bf0a82deb065a9e6392ca457c8f4b01666` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/preparation-freeze-repair-event-v3.log` | `6acecb07e1ccef404f5003c671a2257a0bbaefa3e296558049230b4e15fca788` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/preparation-freeze-repair-v3.json` | `918b01bdbbea27dd5202d646068d82974665b89ca522d23b874c2e624490682f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/prepare-source-review-v2-exit.json` | `ddc67e05cd057ffcd945a68bfdca44fc01b10d4f2bec813cb6b93e66d6c0a354` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/source-contract-inputs-v1.json` | `a1cb1ec67a2fda334e6c009dfa656ea26d9286d09f2b813e9a31d909ab5bdce7` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/source-contract-review-packet-v2.md` | `005022cef77d5217094b0e1d75846b199455af2c1adcf64ceb8b3f8c62dabaeb` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/30_lower-ready-leaf-v1.md` | `b57a7b8220602fcb5f72d281750f6ac121dd77008d67a705d58243d8af0e723e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/actual-canary-lookup-v1-exit.json` | `63c83bfd324a1210dc60bd966e66ce3095c3bd9c4b04182b6c444b8eb65f4bd0` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/actual-canary-lookup-v1.log` | `cc5e84979160d14765f648d0ae2f40f743b5bdcd1aaedfb1604584372fcf971a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/actual-public-canary-header-fingerprints-v1.json` | `306a1dd9159d54059e07a2a70e254222417c48f1e863fd37377328a08aa7886e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/actual-public-canary-headers-v1.json` | `e5d17ab2218c3d0c1acde897ac7906e5df1972afbdb6831cd01135222e167874` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/actual-public-lookup-v1-exit.json` | `a4ccb3f9468ccc1bfdaec8be7104818119f75b554844f1ed687bdbb507b7de96` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/actual-public-lookup-v1.log` | `ecd2bb0015b9b0e2cc63e380d43ea8e0ed4bb20a212babf2af076556021c1fe7` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/all-axioms-v1-exit.json` | `5e1c86720d70d6fb357b2eaa78a7b404a4b95de7a08546c3c269ebe26a5e0a9f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/all-axioms-v1.log` | `e8da576aa82eeebdb06a9b5240a4fe746d82efa81ced51edd4bee05047d8987b` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/all-exact-types-v1-exit.json` | `601e5e938c4ae60862387ca88323785ff885aa24eb520e2847f83e94af1100b2` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/all-exact-types-v1.log` | `164febaff3ca2a52855a50bd6809f7906e5cd74b7470c4bb142e1a63737a0a4f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/all-exact-types-v2-exit.json` | `e63bc65dd357e79b302ba0e422813939859e187ddf22d522f69ac700a673f09c` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/all-exact-types-v2.log` | `808d70857f279efa6802eb3ad9685902be4987d83dc13c2b41ded3d0a8db748c` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/all-exact-types-v3-exit.json` | `ab218e7597df05ffb5eb7778c64b02c3cbccb57821883f273fdcc966937c4d45` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/all-exact-types-v3.log` | `2f2a5df2d51a97a1ee92ae37a77e8330ccb7d8392c38a0b2b1f90ce6e95f93fa` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/attempt-causal-v1.py` | `2845c45b7abce2e5610d80ae218ac93d00255297ddeac7da62ab78895e8c62ea` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/attempt-causal-v2.py` | `d835aab0197ed201fa57a1eacaff971ebfb2c74fac92980b488622e7d5df6a52` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/attempt-deterministic-v1.py` | `4ed13ecbcb3b82ad3c618d387f183e28425fad15ac94ac33e1083ad046887bce` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/attempt-deterministic-v2.py` | `90fba9e6100a007b96043dcdc8f7415db80cd44206c1481a12fc96db7c2e0cb8` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/attempt-law-v1.py` | `8d97050531fa96861b69ac4de7bd02b21c40f657bca0e9d0e1b496ddbb799c29` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/attempt-law-v2.py` | `371a65699cf2384531c0fa3063beea7a57e58a407a1f09ffcc6a89c2febf6154` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/attempt-loss-bridge-v1.py` | `06a3c776dac6a9520bab88de8f24ae339e9a7f66dad764cf8517a4233a192fc6` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/attempt-loss-bridge-v2.py` | `4e0af2f644fb061726a9a24264e4f9d8f0903bfc50dd772fcd9b8c1f9160d5dd` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/attempt-moments-v1.py` | `758f2ac348ac7257d1cfd288582eaccaa152617ebcaf63986fc797b14e37ab57` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/attempt-moments-v2.py` | `a6164ade146ed1ee5b93723e438455ffd8d61446ee9d6dfc2862d48a84486acb` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/attempt-seeded-v1.py` | `14099e59389d64343bb65e68b05b3e45ae79982ee24dd6e667a9293063db2a19` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/attempt-seeded-v2.py` | `a6f9f27261d296b44ef5515778a791c44923c630182175d32998912706040673` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/attempt-seeded-v3.py` | `98fdedfe91af4de6184dfbb690282fcc52bda9d691be4ed97873f1cb32dc837f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/audit-first-leaf-v1.py` | `9ade07fc521b393723eb040907a365e4e25d701ccfd5c82c34fdb224acaf49a0` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/audit-full-bodies-v1.py` | `09452ccd0ab1b1c36e571ab02524c740c917a19c999ffb92bbe59cb7ac729a6b` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/audit-resume-v2.json` | `21cf2998cf5b0e41bb242e51e29750c6110a5dd4ec544d17b6d0ad5a38d158e7` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/body-bindings-v1.json` | `4d4a9d9b897ac1c40fa43d3dfc00e1bdf547d80bdc6f852027990660ae353e3a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/body-review-packet-v1.md` | `40bdb263b6e94d424d0c2e59dc1a31062039ce78d260eee34a2f9ecfa72ebc79` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/canary-repair-v2.json` | `3751f4058f4c9bc7d2c1db71f5ebc4a1c718616d0c39efc0232493bca5019f6c` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/canary-repair-v3.json` | `877b24fc4a62e7ecdd0ef5f57e90019ed88fc0cd82e78102705f918a8c759121` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/candidate-event-v1-exit.json` | `123a80f75860855ef2d656c66db49b6b202ffea080c414a667e660c982b41e08` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/candidate-event-v1.log` | `dfdc91130b93596addf327ab7837603bcbdf76015588981ab5cae13f8be34c83` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/causal-addition-v1.lean.txt` | `d42f3f5dd8b2a30c10cf3ab114bc8dbfc4d1de7738a843100aaab19b22734046` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/causal-attempt-v1-exit.json` | `8746e7ac0892e25d6b845e0b8ee967a01f478011bddb31376d0e894e85d8fc2e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/causal-attempt-v1.log` | `f020f64b5a524aa54dd27754578b7199d1c5b2c29827211148c621f0672a83a9` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/causal-attempt-v2-exit.json` | `e54180807ccdb6b85adbbc8d331401c06179b05a7187dbd82e3fdb9265da4270` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/causal-attempt-v2.log` | `36a7a5c032f8ec626453940d08fbc21250140e6c2c59fb9168b714659714caab` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/causal-repair-v2.json` | `8b3b84d6f0676e7be706a18e17fd512ed712a1df49214e2f9a47f396e7eae5ab` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/compiled-value-graph-v1-exit.json` | `725e37156e0b37b6ac7f553d8c9d60c98fc7d06e060962f548f25289d1b2bb4c` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/compiled-value-graph-v1.json` | `45192e33e2ac82ff3dacf3d496eddc83938e2bbcf3f0fe853dfb6f338ff9af42` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/compiled-value-graph-v1.log` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/compiled-worker-trial-v1-exit.json` | `721ae5ae2130e9724298a44220f630ec1466dfaf0c340faee1c2e62614115a87` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/compiled-worker-trial-v1.log` | `7829e31cf502d8937c9aecf70feba76ed03aaa86be1c79aff225664aa28624a3` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/deterministic-addition-v1.lean.txt` | `d4d5ed132abc1f1575f056e06f34f9714402de8eb25dba0cf10a135c2ebf2339` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/deterministic-attempt-v1-exit.json` | `c3aad12e489bcb9febd7e82bcb21cde33af93a7a9965ed834fe300d85170f80e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/deterministic-attempt-v1.log` | `185bd1753d4f4d7cc714e0c8f20fc2659c3c3f3ddab58994043586c9476b0e92` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/deterministic-attempt-v2-exit.json` | `c5700fbbc04f716aa363945b8342a58ed2ebff68b0fdab50f020f3b2c16b7757` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/deterministic-attempt-v2.log` | `fe4a595b4754ef17259786aa9fb717e19a6abb97fae6650e0a19e4e215fd50f2` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/deterministic-repair-v2.json` | `a3e2b3da86ebcbc0c03473ca61cd90aa32436467ac2266de46ea0c63b50a2ecb` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/exact-bindings-repair-v2.json` | `cda994e67e0b7814c040a4844c6f558d51451db85883b7cfde58eaa2e4f4fa55` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/exact-bindings-repair-v3.json` | `d00862db5b847492b3dcd3836623d436fb7ebff35c89b9c917eee33b12070f82` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/first-probability-build-v1-exit.json` | `60322f76fcf9629a47627246246072b0fb448feec31a573f2b3ad8ac135421e2` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/first-probability-build-v1.log` | `ab1447cbdb342869b02cf20ae4cd7a403b575c2b02342c079deae2a94111fd92` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-blind-binding-audit-v1.json` | `e35b541b28e715000e037f3ef6c01ebbddced542ef6cb887c9cdbf174c84f3dc` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-blind-decoder-receipt-v1.json` | `06635e31076a1b8afcafd1d267c51102a008ce0d4d6b79e773e5ae5a177b15cb` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-blind-decoder-v1.md` | `6bd2f1e9089ffad38ede7956edcd12f76daace096c4d38cebc7e46261b625ee2` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-bindings-v1.json` | `60a4e5d42f704cc8898616cb1bc811320842999627947e7bfe3c0e73ddee2b95` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-canary-actual_last_prediction-v1-exit.json` | `39f85ef161d37da2f638ebbd120af6d3dcd8cc00a3e9ffd9a5c85db8402fb89f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-canary-actual_last_prediction-v1.log` | `eb35337cf17b98c4f391c413a1300b05f0f086eb60ab10f5311cfeb55030ae04` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-canary-actual_optimal_loss-v1-exit.json` | `8c382652247bf5d8f298e387736aff8d9b891b4624e4701802612ea693d90bf9` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-canary-actual_optimal_loss-v1.log` | `b44865089fb6d8ef72a45864f35788b2dc83296e879f0aeab84cf70e262c4dff` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-canary-averaged_variance-v1-exit.json` | `f58ffea966302830f46c0ff322d0ea3a65fc8ac63238eaeffded338f707fdf21` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-canary-averaged_variance-v1.log` | `cd0116be33c31f1ea14596026ec0141d9f8ce13c53627a0c11bb510fc422eefd` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-canary-coin_distribution-v1-exit.json` | `02124648435fdbd5bce7f19e338a1c925add173801abd546fc1c19f20ac0e3e1` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-canary-coin_distribution-v1.log` | `a3e6c96339a71ba424bec5f933f5b47974acd5375be25c6a6c5ffe9fe07eca13` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-canary-correlated_moments-v1-exit.json` | `f24617370cc9438621f3257d4f64b33ddbfbba6bda0be048e30ccaf9be4a3420` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-canary-correlated_moments-v1.log` | `07f30506cf97b2f9918fedd39d85791dfda083f62215527003f9ea579b643806` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-canary-correlated_two_step_masses-v1-exit.json` | `c11a46064cf8137d78720a20a83134bb37c83b0a08d81e3d27bae29e4d0e8d88` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-canary-correlated_two_step_masses-v1.log` | `b974b971ddc9844258db7c33f1b01de3f60342ba86a33a0140eeaf1308bb8de0` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-canary-deterministic_fixed_sequence_endpoint-v1-exit.json` | `9e7341341acf394f122a4820c21b7f1de5af3a8234065e5f40c116afb145af36` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-canary-deterministic_fixed_sequence_endpoint-v1.log` | `14289960c57278a284d41a08f49361082b3cf3c0043c2c37bab608e0806786fc` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-canary-genuine_coin_policy-v1-exit.json` | `6703d32eb280d33ea23ccae3ec48feeb458b90ca88b1a32df7d4087673153f06` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-canary-genuine_coin_policy-v1.log` | `418d203f2cd8d5e840c7d09a02574eead04f4332f12c222b8779cef82bf9519f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-canary-nondegenerate_actual_regret-v1-exit.json` | `a7f20890480e4934b1722ad832049e5a6f57673b61071cf5c75a5ee6b0b5b45b` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-canary-nondegenerate_actual_regret-v1.log` | `4cef9d41feddde0fdbe751d247a4c3e2bb374cfe292d11f9d05ec2f6a4fe17be` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-canary-one_step_harmonic_endpoint-v1-exit.json` | `61936040206b95c59ea68f40c687502d1efdced121272bdfe6eccd1529499162` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-canary-one_step_harmonic_endpoint-v1.log` | `b6e042bf31b992eb5eefcbcd4497abc9570d025af65b5e55cee75a08cbeb622b` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-canary-same_past_different_current-v1-exit.json` | `4356c0a9a3cca6f30692a264be8860d17617b2f74d3f5ad5de380cafa85dabca` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-canary-same_past_different_current-v1.log` | `6f7cc918fb1edc9da52182f56f439e063ba35eb6b44f6b260f65f4121d15cbc0` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-canary-seeded_fixed_sequence_endpoint-v1-exit.json` | `76a221ef0a2f21add68f99ed6005d582d00becc49f48fc9cbf3b809484002da7` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-canary-seeded_fixed_sequence_endpoint-v1.log` | `287956efcb01811ed40848f5e5f80bf80a368aab957e1568a71bbe5aec0910a7` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-canary-seeded_log_endpoint-v1-exit.json` | `020da27ac3a5a006b42ee8658b6767da6779d986d2ee1d558d08419327436190` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-canary-seeded_log_endpoint-v1.log` | `8c15ce1ef0ef0ea51fbbc3fba537644ba8929448e22d6d0602d6fdb27c75de41` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-canary-seeded_policy_bounds-v1-exit.json` | `73df3d09dad7f721946e27a5ad2e76c471afff0783a0882d20b77bb6dedc9364` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-canary-seeded_policy_bounds-v1.log` | `1b58c61359e161f7cd6dab9a6ae99ae8aac3c69ae59ddd6c5f82a2ae0ee54792` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-canary-unbalanced_probability-v1-exit.json` | `6065d276779ef663a64d15df7a9d2043dbd3ae8d3e7cb7b5fec2514d10b0972c` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-canary-unbalanced_probability-v1.log` | `a5b0425f6a482efa3ec04b9782d2fe3ef2b8f61af9a86163be8f48bfbf53992e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-canary-zero_and_two_normalization-v1-exit.json` | `b3f72bbfe40aa581ba691ad2d2494ffe841363e82cd20fc4ed2e96fd2b6af807` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-canary-zero_and_two_normalization-v1.log` | `1fc3717ec967f62a2b5e18842f056e9fd8e492113c874548a46a06fe1c149094` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-binary_mean_minimizer-v1-exit.json` | `b7261c165d863615dd037aabc263a31bf5ce07fee425b7004266e11f0bb39a8c` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-binary_mean_minimizer-v1.log` | `7be4701c0b532001fa0ba9f5bbdd80cef24c7294df76e29ef1c5ad4c67e4706e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-binaryStream_cons_last-v1-exit.json` | `05cd928e6f83b4e7cbe1f02b06b4bdb85ab906efad688c0efee226380814a464` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-binaryStream_cons_last-v1.log` | `2f7ba7ba982ecbb8383f64558013c9f6b8d8da2679081648538e5689f68caaed` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-binaryStream_cons_prefix-v1-exit.json` | `ee7ef4160c40e35624ecc41034d0d33e1a0ed0e3566347ed7a940d3d469bb73b` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-binaryStream_cons_prefix-v1.log` | `76a87605c8a5f4991cae60acc074e059dfb873dbc5da098c62c5259328d17ef0` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-binaryValues_cons_prefix-v1-exit.json` | `cef1dc5f2972bb1ea3120badaf5de6b652f6ec23753aef46348d111e75329ecf` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-binaryValues_cons_prefix-v1.log` | `5defbc45d0de6bdf4c1b218357cb835756fdddfa651811b4d3b8937a9782f7d5` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-binaryValues_sq-v1-exit.json` | `6117ce37117f57418adb22ab6bcf046dbb8a8e012e6dd51be77be30ab2d76c2e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-binaryValues_sq-v1.log` | `af1380f4b62406c7f6eb61d5ece50d03efa245055d434f292c2f098e77306141` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-binaryValues_sum-v1-exit.json` | `43fd58664a053b644924184829d41af201466e7a813351ef0672a7b5e897cefd` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-binaryValues_sum-v1.log` | `04e352056cbe3196b291f507a5514b974a2cb1aed02390a028d91fd6f099ef15` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-branch_mass-v1-exit.json` | `142c136cec2a816925fce8aa05b52ff9b124f98b644a84f0a7b81d160f91a665` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-branch_mass-v1.log` | `0fc960fb23895a0e1f4a5df4238b7b955584b497b89a4adb591689b3885c03b8` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-causalPredict_cons_last-v1-exit.json` | `8fceea5e597ef4ac7cb8e31ea3e330ec2d92cfc01a99f4c42f3cfb1bd44ddeb5` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-causalPredict_cons_last-v1.log` | `9a530eb34b692b57dc315641c5c99561b28664ffe8b4acc899ada70a46159bc7` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-causalPredict_history-v1-exit.json` | `ea5bc404fba9a11c36f3e2597084fc1c3ab34a3c6988adbfafdf14941390861e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-causalPredict_history-v1.log` | `ae48dab6f010feb3ce4ea04c3e08ec678bcc510f80cf0431729af47febd908a4` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-causalPredict_prefix-v1-exit.json` | `19845690bce71c3f3de860c81d51954e25bb5fe1c2382357dd45651fbeb681d8` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-causalPredict_prefix-v1.log` | `a668c0d93ecda21f0ba07f6ed2e0ed869d2737581051862b140581c4d83211de` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-conditional_square_lower-v1-exit.json` | `93bc6a17b4f5a090853c2ac15fd0c23adfee154c7d922fdbcfdecec7976a6b6d` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-conditional_square_lower-v1.log` | `8d7fc639588c905eb30c31a5bf7586909d7589f38868334712b5e55147cecb65` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-expected_heads-v1-exit.json` | `f7d43d2c3b9b6008490cef4037963ca9b432b16974fbd6b95fde8b082dc7fc80` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-expected_heads-v1.log` | `6e986e5e344d440978a757ac910c8415977e065d431523f8f622c97852ed16cf` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-expected_heads_sq-v1-exit.json` | `6ff4e8142c0e765f82202ec2fb3a3b47bb4d41e419de043d4069ed3721f597a7` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-expected_heads_sq-v1.log` | `9f7c760029113246d65199d19d35496f443be4950f34cdeace78408f33360f75` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-expected_next_variance-v1-exit.json` | `a38fb38624cdde153b101343497768f42434cbd7430117d2a17badadf06947c8` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-expected_next_variance-v1.log` | `e16774e4b4372b7c71f977f9095465a56d304d31f5b3723423b29e427e8a930c` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-expected_pathBestLoss-v1-exit.json` | `40aaeec4d5171859c5138ec5d2775faa20494ce838972b037d9c394cca0d5efa` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-expected_pathBestLoss-v1.log` | `2b271ad6e09a5d2eafad8a363fbe03e3dfa2a7a19f6d9f3ffffa5ff684289d4f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-expected_pathLearnerLoss_lower-v1-exit.json` | `9dd60ba2919e45def343aa20a2bae8d9303d9e6b9f9edc5122ba941e3e7f3aed` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-expected_pathLearnerLoss_lower-v1.log` | `fefba652cfd806d5fb9cab32aee489f1e355e1c5498df0a5c1bebac822325d82` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-expected_pathLearnerLoss_step-v1-exit.json` | `f2aeb68bb8e71d8a08cabf2927eba635a0f516b7adb90221535c68c52c16d5a3` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-expected_pathLearnerLoss_step-v1.log` | `9f989c750f4f19bae6eff515b1d674b424ab01b958e0554cef22f5ab3fa9e909` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-expected_pathLearnerLoss_succ-v1-exit.json` | `842d8677ae220b457f03f54246c26d4144550897b5c15f636ace0bf555a5036c` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-expected_pathLearnerLoss_succ-v1.log` | `9f26d92153000e372476d018e5e2ff41a9da393cca428a2e841a9398690f31cd` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-expected_pathRegret_lower-v1-exit.json` | `cf5ea5b192374768604345c33b664b6df635c37947bdc48c8d7d907ef0c54c58` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-expected_pathRegret_lower-v1.log` | `1dd0e54f05b4940a54efff4554392e5dca1de659b4d52113de676b973c3a1af6` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-heads_sq_succ-v1-exit.json` | `859bbfbd34a60217dc17ab8f5644ff8c07cf35653fe1c62687237cae9a5de057` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-heads_sq_succ-v1.log` | `879f81447ba8ee5a9750329310ee7fa0bb29a365de6129afb6640e9cb1013ba7` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-heads_succ-v1-exit.json` | `ab1533964b3d67152d1f741921934f550a5a74a224b669ea0c252fa962782f45` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-heads_succ-v1.log` | `d1aae01e383cba0025e7e2710c98e21446417c108fbf3d6f40aec8d4cb66ad0f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-pathBestLoss_count-v1-exit.json` | `5de8f5edca4644b708f256d31af20b5b6a887752cc1f02a56d947729a7b0a564` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-pathBestLoss_count-v1.log` | `2475dde4d92d339d1f11aebd061916974c2b43651e7ac194157feb36f738ca11` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-pathExpectation_add-v1-exit.json` | `c82984b143bc0217a6011e2a7e86cfc66ba56e2ea2cfc79c6dabf04956baca86` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-pathExpectation_add-v1.log` | `f577281e555f8b05234fbec2a8dbde5d55bf3d676cc6237c15d1c44e9158c64c` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-pathExpectation_congr-v1-exit.json` | `dd72a724f1538f66a1188ade9ad7d927f9ed0aa1e5d1acc3ae5068a0843b87ef` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-pathExpectation_congr-v1.log` | `73c885a9ded4757ad04b780a6b6a124e262f29316a960ed2a3c81286606563d6` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-pathExpectation_const-v1-exit.json` | `2e9ad195ba2d5b30d0dc01f2f958d561f9d408bb693e2801cdd89ede2cdd5942` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-pathExpectation_const-v1.log` | `3340581b5b736e5856c12902b1a9fb979d8516d861cb5dd8eac52faf06176c57` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-pathExpectation_const_mul-v1-exit.json` | `290049476c474eade95bb5daed81e7b2104c75df817092cdb9ba48d2b14ef558` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-pathExpectation_const_mul-v1.log` | `96cde615dcc84e317126df3a954cd0935bdce9d3fbf2445e9316622accb680da` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-pathExpectation_div-v1-exit.json` | `cf455dc5dbf8a64ceb789402bf95992c810326a06f0fae8deb3722232ab3f447` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-pathExpectation_div-v1.log` | `62b35b6f7c4c781ea1ce4c7d73cc2760b0f316e44a8c5c0cff5e729b547ef71f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-pathExpectation_integral-v1-exit.json` | `10327be00131c8446c09beecd8f41acef1721dcddb70b334d8df025dacdc729a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-pathExpectation_integral-v1.log` | `50abc0d8a9ae38cb5c27d2dbcc38406aa930e195bd4a4ae1c99a6ac4bdf72f42` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-pathExpectation_mono-v1-exit.json` | `c4a7f7a4424f28d216b7f3aa7d3c7b80e0e99ae830ec1eeae705e7356be03a0f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-pathExpectation_mono-v1.log` | `8913a5b80c4d1ebfb8efae9175231b4606a14b94edf1a6c3fb641b5d6052a9b9` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-pathExpectation_sub-v1-exit.json` | `51a7846c84fec598939a5bcb319d96aabe4c02835dae147eaa658fa02ae789e6` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-pathExpectation_sub-v1.log` | `65e4a2adeb15e26e7dabaa5173f1d0117ee4e18404a2e1fb4cadc90190c98fbc` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-pathExpectation_succ-v1-exit.json` | `5d9a7804074a38d10b7c8d37b78b220e90691b5bf17b523764a25320d58438bf` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-pathExpectation_succ-v1.log` | `34f817f0bcb20926be84971033bdb7fc50f3979a3d0549c0b938e2aefd4010df` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-pathLearnerLoss_cons-v1-exit.json` | `d4d8fac354a4291668a1b4133c6e7a4f27bf0b703cde2466e2d6c27efe414212` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-pathLearnerLoss_cons-v1.log` | `40bfd04d99f6fa8aba254c8381d43b11c994098930344d1184a89a12a3c8f363` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-pathRegret_abs_le-v1-exit.json` | `1b318431eddc759f817b93426098f714c88de5cd8269bc330ef8b6f8a8414563` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-pathRegret_abs_le-v1.log` | `ad0aaa1eda2952c1ad81ad38554d1bd92666db36bce7727228b16abbb433355c` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-pathRegret_eq_losses-v1-exit.json` | `d16068cf77b8c322de06bcb74c033a8ef4b3b0f13ee8ae212a19fabd1e0cf67b` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-pathRegret_eq_losses-v1.log` | `60145a1970ed1a4a8c5e5a6e77de99b5f4d30e890f4df1f46fa5f04694c8faa5` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-pathRegret_integrable-v1-exit.json` | `09027e8a3eb19fc36511113ef4ba9540a75d394f30481d8eb11529f6689718d9` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-pathRegret_integrable-v1.log` | `e9bd6ce5d6560465f40555027638cee0ab82b1e17aa342684fb458fbc2bed019` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-pathRegret_measurable-v1-exit.json` | `6b8c633341da2e9a086d1e06b8ee6c95f15b2e41a486ffdd1cfa47836f243800` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-pathRegret_measurable-v1.log` | `661aef7e26dfb09e72c321b979eda8a1094aca099da14195b861d1eefc6fd9dc` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-pathWeight_nonneg-v1-exit.json` | `e6ff6c71bc2c9ce3438f36c79eb95d853d52cc3c18893f58a6b45fbb6abbb510` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-pathWeight_nonneg-v1.log` | `8eb25ee2e174d81a0fd649c4a1125695ed34c4bb387d98696c744684ab50380c` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-pathWeight_pos-v1-exit.json` | `bec4a890056f5c28749571dd59fe1a0ef94410767f24d11cb8843a5484dc8926` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-pathWeight_pos-v1.log` | `593accc425345ca8dc160da93e5165f98123df8925bf8819add76b58ed7bb003` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-prefix_distribution-v1-exit.json` | `84a9f2b01fd07bd6085be6761d5b198cdf8920863b65c9d0177655319cfc3444` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-prefix_distribution-v1.log` | `1c3dc60440e044be0c5cf998a6e93aec53e76c1fc99a51a06fcf40234c8369f5` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-prefix_mass_one-v1-exit.json` | `770c9fc16172bfd8669a102e76d81daa55a9baa34401c133d9b391be2a603459` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-prefix_mass_one-v1.log` | `0edfaa93175c72f80aab0ce4064267afde8862567a0d89d4578310ee983b7dbf` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-prefixMeasure_probability-v1-exit.json` | `df527897835d2abbb77ece5bada688ae3fab66184d008458414f7b31f702b7f3` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-prefixMeasure_probability-v1.log` | `78c1bba6364077a300c03cd9692d8361d034ac7eb32e07a9b964255432d81cae` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-probability_mem-v1-exit.json` | `54c0204f36316ac3b7144293d6df607895824e1c3b30f37f99630fe1f88e4474` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-probability_mem-v1.log` | `a05905f2ee0733b9118deb80dee7f9c90792f16a2e1c2d323d6839e03daccbf7` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-randomized_harmonic_lower-v1-exit.json` | `0c9e6b795f03a70496099ec5d057a636c920361808379d285e1c94f8c88def42` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-randomized_harmonic_lower-v1.log` | `ef87aef6f25f31fa6ef7922c80bfe14717dd1933aea4919843b808282a7ca7a4` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-randomized_log_lower-v1-exit.json` | `b9686d343ea4a5cbf278c743817107c5a9b0a1b3c4df4da7740c0c3dc28acd00` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-randomized_log_lower-v1.log` | `22f031693461e6e1605a2cb5d15519befd6bfb697b5b2609c2ac2ba9e39e6931` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-square_loss_mem-v1-exit.json` | `8fecacddcc8a8e5f4213f1ed582cfe811e7233085f7233aa6941add17c2e287f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-square_loss_mem-v1.log` | `e22555d6d31217cb9ec7d2983cdfc6f71f61fb0d09da54b54bdd2918f20b25b2` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-square_loss_sum_mem-v1-exit.json` | `3e3ded22a8d87174f694875b2db4ccd8a01ed57751865e15c27a09012a408211` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-square_loss_sum_mem-v1.log` | `38419bebb830f17cce439502c372f501baaa9b5bfba4eb77be7e534017453c90` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-sum_vectors_succ-v1-exit.json` | `06b7115cca66d0f4f1943e11ba888c18e87ddb680853163d05cdee68184e41b6` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-sum_vectors_succ-v1.log` | `61ab253f88274cba4474222b75da09a3c2f0d9af6308c6a59a8563c9061e9d42` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-variance_sum-v1-exit.json` | `02048b40f3b474b0c0f076a4524eabcb600da3c2e5ecc848934437230739f79c` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-fence-public-variance_sum-v1.log` | `9425c2aebf30238453d20e93f05f874c3232ec3d2c1b563b6f394ff9e11f918b` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-header-fences-v1/canary-actual_last_prediction.json` | `eb35337cf17b98c4f391c413a1300b05f0f086eb60ab10f5311cfeb55030ae04` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-header-fences-v1/canary-actual_optimal_loss.json` | `b44865089fb6d8ef72a45864f35788b2dc83296e879f0aeab84cf70e262c4dff` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-header-fences-v1/canary-averaged_variance.json` | `cd0116be33c31f1ea14596026ec0141d9f8ce13c53627a0c11bb510fc422eefd` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-header-fences-v1/canary-coin_distribution.json` | `a3e6c96339a71ba424bec5f933f5b47974acd5375be25c6a6c5ffe9fe07eca13` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-header-fences-v1/canary-correlated_moments.json` | `07f30506cf97b2f9918fedd39d85791dfda083f62215527003f9ea579b643806` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-header-fences-v1/canary-correlated_two_step_masses.json` | `b974b971ddc9844258db7c33f1b01de3f60342ba86a33a0140eeaf1308bb8de0` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-header-fences-v1/canary-deterministic_fixed_sequence_endpoint.json` | `14289960c57278a284d41a08f49361082b3cf3c0043c2c37bab608e0806786fc` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-header-fences-v1/canary-genuine_coin_policy.json` | `418d203f2cd8d5e840c7d09a02574eead04f4332f12c222b8779cef82bf9519f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-header-fences-v1/canary-nondegenerate_actual_regret.json` | `4cef9d41feddde0fdbe751d247a4c3e2bb374cfe292d11f9d05ec2f6a4fe17be` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-header-fences-v1/canary-one_step_harmonic_endpoint.json` | `b6e042bf31b992eb5eefcbcd4497abc9570d025af65b5e55cee75a08cbeb622b` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-header-fences-v1/canary-same_past_different_current.json` | `6f7cc918fb1edc9da52182f56f439e063ba35eb6b44f6b260f65f4121d15cbc0` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-header-fences-v1/canary-seeded_fixed_sequence_endpoint.json` | `287956efcb01811ed40848f5e5f80bf80a368aab957e1568a71bbe5aec0910a7` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-header-fences-v1/canary-seeded_log_endpoint.json` | `8c15ce1ef0ef0ea51fbbc3fba537644ba8929448e22d6d0602d6fdb27c75de41` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-header-fences-v1/canary-seeded_policy_bounds.json` | `1b58c61359e161f7cd6dab9a6ae99ae8aac3c69ae59ddd6c5f82a2ae0ee54792` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-header-fences-v1/canary-unbalanced_probability.json` | `a5b0425f6a482efa3ec04b9782d2fe3ef2b8f61af9a86163be8f48bfbf53992e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-header-fences-v1/canary-zero_and_two_normalization.json` | `1fc3717ec967f62a2b5e18842f056e9fd8e492113c874548a46a06fe1c149094` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-header-fences-v1/public-binary_mean_minimizer.json` | `7be4701c0b532001fa0ba9f5bbdd80cef24c7294df76e29ef1c5ad4c67e4706e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-header-fences-v1/public-binaryStream_cons_last.json` | `2f7ba7ba982ecbb8383f64558013c9f6b8d8da2679081648538e5689f68caaed` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-header-fences-v1/public-binaryStream_cons_prefix.json` | `76a87605c8a5f4991cae60acc074e059dfb873dbc5da098c62c5259328d17ef0` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-header-fences-v1/public-binaryValues_cons_prefix.json` | `5defbc45d0de6bdf4c1b218357cb835756fdddfa651811b4d3b8937a9782f7d5` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-header-fences-v1/public-binaryValues_sq.json` | `af1380f4b62406c7f6eb61d5ece50d03efa245055d434f292c2f098e77306141` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-header-fences-v1/public-binaryValues_sum.json` | `04e352056cbe3196b291f507a5514b974a2cb1aed02390a028d91fd6f099ef15` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-header-fences-v1/public-branch_mass.json` | `0fc960fb23895a0e1f4a5df4238b7b955584b497b89a4adb591689b3885c03b8` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-header-fences-v1/public-causalPredict_cons_last.json` | `9a530eb34b692b57dc315641c5c99561b28664ffe8b4acc899ada70a46159bc7` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-header-fences-v1/public-causalPredict_history.json` | `ae48dab6f010feb3ce4ea04c3e08ec678bcc510f80cf0431729af47febd908a4` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-header-fences-v1/public-causalPredict_prefix.json` | `a668c0d93ecda21f0ba07f6ed2e0ed869d2737581051862b140581c4d83211de` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-header-fences-v1/public-conditional_square_lower.json` | `8d7fc639588c905eb30c31a5bf7586909d7589f38868334712b5e55147cecb65` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-header-fences-v1/public-expected_heads.json` | `6e986e5e344d440978a757ac910c8415977e065d431523f8f622c97852ed16cf` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-header-fences-v1/public-expected_heads_sq.json` | `9f7c760029113246d65199d19d35496f443be4950f34cdeace78408f33360f75` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-header-fences-v1/public-expected_next_variance.json` | `e16774e4b4372b7c71f977f9095465a56d304d31f5b3723423b29e427e8a930c` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-header-fences-v1/public-expected_pathBestLoss.json` | `2b271ad6e09a5d2eafad8a363fbe03e3dfa2a7a19f6d9f3ffffa5ff684289d4f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-header-fences-v1/public-expected_pathLearnerLoss_lower.json` | `fefba652cfd806d5fb9cab32aee489f1e355e1c5498df0a5c1bebac822325d82` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-header-fences-v1/public-expected_pathLearnerLoss_step.json` | `9f989c750f4f19bae6eff515b1d674b424ab01b958e0554cef22f5ab3fa9e909` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-header-fences-v1/public-expected_pathLearnerLoss_succ.json` | `9f26d92153000e372476d018e5e2ff41a9da393cca428a2e841a9398690f31cd` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-header-fences-v1/public-expected_pathRegret_lower.json` | `1dd0e54f05b4940a54efff4554392e5dca1de659b4d52113de676b973c3a1af6` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-header-fences-v1/public-heads_sq_succ.json` | `879f81447ba8ee5a9750329310ee7fa0bb29a365de6129afb6640e9cb1013ba7` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-header-fences-v1/public-heads_succ.json` | `d1aae01e383cba0025e7e2710c98e21446417c108fbf3d6f40aec8d4cb66ad0f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-header-fences-v1/public-pathBestLoss_count.json` | `2475dde4d92d339d1f11aebd061916974c2b43651e7ac194157feb36f738ca11` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-header-fences-v1/public-pathExpectation_add.json` | `f577281e555f8b05234fbec2a8dbde5d55bf3d676cc6237c15d1c44e9158c64c` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-header-fences-v1/public-pathExpectation_congr.json` | `73c885a9ded4757ad04b780a6b6a124e262f29316a960ed2a3c81286606563d6` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-header-fences-v1/public-pathExpectation_const.json` | `3340581b5b736e5856c12902b1a9fb979d8516d861cb5dd8eac52faf06176c57` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-header-fences-v1/public-pathExpectation_const_mul.json` | `96cde615dcc84e317126df3a954cd0935bdce9d3fbf2445e9316622accb680da` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-header-fences-v1/public-pathExpectation_div.json` | `62b35b6f7c4c781ea1ce4c7d73cc2760b0f316e44a8c5c0cff5e729b547ef71f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-header-fences-v1/public-pathExpectation_integral.json` | `50abc0d8a9ae38cb5c27d2dbcc38406aa930e195bd4a4ae1c99a6ac4bdf72f42` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-header-fences-v1/public-pathExpectation_mono.json` | `8913a5b80c4d1ebfb8efae9175231b4606a14b94edf1a6c3fb641b5d6052a9b9` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-header-fences-v1/public-pathExpectation_sub.json` | `65e4a2adeb15e26e7dabaa5173f1d0117ee4e18404a2e1fb4cadc90190c98fbc` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-header-fences-v1/public-pathExpectation_succ.json` | `34f817f0bcb20926be84971033bdb7fc50f3979a3d0549c0b938e2aefd4010df` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-header-fences-v1/public-pathLearnerLoss_cons.json` | `40bfd04d99f6fa8aba254c8381d43b11c994098930344d1184a89a12a3c8f363` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-header-fences-v1/public-pathRegret_abs_le.json` | `ad0aaa1eda2952c1ad81ad38554d1bd92666db36bce7727228b16abbb433355c` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-header-fences-v1/public-pathRegret_eq_losses.json` | `60145a1970ed1a4a8c5e5a6e77de99b5f4d30e890f4df1f46fa5f04694c8faa5` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-header-fences-v1/public-pathRegret_integrable.json` | `e9bd6ce5d6560465f40555027638cee0ab82b1e17aa342684fb458fbc2bed019` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-header-fences-v1/public-pathRegret_measurable.json` | `661aef7e26dfb09e72c321b979eda8a1094aca099da14195b861d1eefc6fd9dc` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-header-fences-v1/public-pathWeight_nonneg.json` | `8eb25ee2e174d81a0fd649c4a1125695ed34c4bb387d98696c744684ab50380c` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-header-fences-v1/public-pathWeight_pos.json` | `593accc425345ca8dc160da93e5165f98123df8925bf8819add76b58ed7bb003` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-header-fences-v1/public-prefix_distribution.json` | `1c3dc60440e044be0c5cf998a6e93aec53e76c1fc99a51a06fcf40234c8369f5` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-header-fences-v1/public-prefix_mass_one.json` | `0edfaa93175c72f80aab0ce4064267afde8862567a0d89d4578310ee983b7dbf` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-header-fences-v1/public-prefixMeasure_probability.json` | `78c1bba6364077a300c03cd9692d8361d034ac7eb32e07a9b964255432d81cae` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-header-fences-v1/public-probability_mem.json` | `a05905f2ee0733b9118deb80dee7f9c90792f16a2e1c2d323d6839e03daccbf7` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-header-fences-v1/public-randomized_harmonic_lower.json` | `ef87aef6f25f31fa6ef7922c80bfe14717dd1933aea4919843b808282a7ca7a4` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-header-fences-v1/public-randomized_log_lower.json` | `22f031693461e6e1605a2cb5d15519befd6bfb697b5b2609c2ac2ba9e39e6931` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-header-fences-v1/public-square_loss_mem.json` | `e22555d6d31217cb9ec7d2983cdfc6f71f61fb0d09da54b54bdd2918f20b25b2` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-header-fences-v1/public-square_loss_sum_mem.json` | `38419bebb830f17cce439502c372f501baaa9b5bfba4eb77be7e534017453c90` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-header-fences-v1/public-sum_vectors_succ.json` | `61ab253f88274cba4474222b75da09a3c2f0d9af6308c6a59a8563c9061e9d42` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-header-fences-v1/public-variance_sum.json` | `9425c2aebf30238453d20e93f05f874c3232ec3d2c1b563b6f394ff9e11f918b` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-neutral-input-v2.json` | `03f7bbd2142cc065385d05c5d3982818f3d362431302493c6c2efb95c714d52a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-neutral-map-v1.json` | `8b5f115a40abe54d7a5a07ce682161cf7057b46b8770ae4c44b8021b5ac0d5f2` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-neutral-map-v2.json` | `c78e8ef3783362df5366e3f99c0b2ff5302b3b3c7a63a407d35131ee982b89ae` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-neutral-packet-v1.lean` | `3b05872b4dc0f833509498a3b33c132ee2cace69c7e772e31b26c0ae4b2d86e4` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-neutral-packet-v2.lean` | `a3ae86dfd2e5982381eb9c8dd6d57a1594fb34d0c1d5dea098417205f37af679` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-neutral-repair-v2.json` | `4d4eada4309fb8e79e27ae21e027904b80e2a289801410964580c6e2bd290399` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-neutral-types-v1-exit.json` | `c1f66e395326e6dad114921feb86c8e7369a40f2f6a394a20df430013f6b2278` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-neutral-types-v1.log` | `18ce587fc7e7606e16becdf6c0659b7f397876b0afbe7e6c0afbb00ef6ac5fd6` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-neutral-types-v2-exit.json` | `0a6c746d1ef86be56ae035294378b5f4c5fdb9b6f70040e86930dc10a3ece0a7` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-neutral-types-v2.log` | `8287b31dc0cb13e783e755b60549b4cf5592bb179f65816b5fe84f77936126ef` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-proof-frontier-v1.json` | `a7f2f15d3b57c7df5de376ad10a8d062552cd98f181f6f3748098ede411bb00a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-canary-actual_last_prediction-v1-exit.json` | `00dc3c574ae60eae6f676c8ed1db72ac4ae742ebc42cae53f183854f3295c035` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-canary-actual_last_prediction-v1.log` | `412f0537317bb88ec035d8466bcb36b607aba9a1cb9bd60e66f0a386e4e3fea3` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-canary-actual_optimal_loss-v1-exit.json` | `98b31851e7dae44cbbc863e17f504c002d1cf926591982974a7f2adcff2a3e4b` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-canary-actual_optimal_loss-v1.log` | `7bcefb24ccdc8bcd345898d977f220085f7a8937e3547559e66dc03f545926ab` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-canary-averaged_variance-v1-exit.json` | `91aebaaa529b8e4c5e0363332844429ca460b9cfece3cab31c10e9c2a783678e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-canary-averaged_variance-v1.log` | `f436dc8719e7ac3dbb9161c92a5ea66e70a46e247bd8af667f3d8adf54e7e991` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-canary-coin_distribution-v1-exit.json` | `1ed4c6b4174a528ee64e7348b5d1d865420f1d753dcc1668d47ff95dbd77bd2f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-canary-coin_distribution-v1.log` | `1261d908b57a138dea48d71d78479d17332b89bcb11c046d4712e07dc307e94a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-canary-correlated_moments-v1-exit.json` | `fef95480279a266a0ad76d320c09d256820547b7c6f25d990c1b8d2308560179` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-canary-correlated_moments-v1.log` | `c255a2f47fe5f4d5871177f771fb6564d757c21abc878ce95a95be6e1681285f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-canary-correlated_two_step_masses-v1-exit.json` | `9bb347f85535a82a87128aec49db4d26dc61183d8fe2e0d2d49b09ec05a82ea0` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-canary-correlated_two_step_masses-v1.log` | `e8ad09e39cf317d4347a879205fa8a59a33814a8f604a9198e6373db2ce9e6b9` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-canary-deterministic_fixed_sequence_endpoint-v1-exit.json` | `0747d4c8c77e414cbe9f56d25eb6d95964d6e784c0982059061089d4fb87ce05` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-canary-deterministic_fixed_sequence_endpoint-v1.log` | `cd3776170db7b88b794a7630f7d9cc4789d0292dbbf9c3470ba194a70e4e1c29` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-canary-genuine_coin_policy-v1-exit.json` | `4c9a0983ed7c54695dbc47743fc0ec7c89147fc02ab175a54197ce1167b62ec3` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-canary-genuine_coin_policy-v1.log` | `967e69c39ec3ef89764ba3ef0041b4eec395fb47595b4786575b0011b4ba9edd` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-canary-nondegenerate_actual_regret-v1-exit.json` | `7d55c016486ac1c2496380583548eff869d811891214186e101b64e427ca8879` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-canary-nondegenerate_actual_regret-v1.log` | `a8ee4d4d2e06715e46b8735f2e350fa1f0f0c772af857e4d70c7fa1e77273fa9` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-canary-one_step_harmonic_endpoint-v1-exit.json` | `8068b9aa3f66949e3734685895ac69aaca98bb64691f9ac01888b384baf1e4c5` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-canary-one_step_harmonic_endpoint-v1.log` | `4faf662027772b3089738717a020922aa13ba38c7eff17bb3cc7a2d9b25622fd` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-canary-same_past_different_current-v1-exit.json` | `fbfab07774d5bfca2e888141707619d949857420b8e0a4f73ba888e2d14c484d` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-canary-same_past_different_current-v1.log` | `589356d95fafac9e97780a1a9214359dc73849e80369842be166d32f3c676ed3` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-canary-seeded_fixed_sequence_endpoint-v1-exit.json` | `a8ac7258df6598d5fcc64ddfa162013f4370aaa769f9ab89af63fb2337067085` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-canary-seeded_fixed_sequence_endpoint-v1.log` | `a1270c16eb1297583e6d444b68cee4da4eed995ac03d0ec0b83e9a82648c25ec` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-canary-seeded_log_endpoint-v1-exit.json` | `401d63f60162c1e1a535420a52e68d7e38cdb3dcf427204af065526140cbd3ca` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-canary-seeded_log_endpoint-v1.log` | `acc3cbbe2cd9f7b814ab5831e9e672cbbae83437ac5dd65d6b1e790daa6a1874` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-canary-seeded_policy_bounds-v1-exit.json` | `bb5eb479d09b607b0eb7ae5474f0279aacb961093dd3179f081bc7d05c2baa61` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-canary-seeded_policy_bounds-v1.log` | `7ddab008641003c4a1454a34b69585dbba4bf5c6c7307bda8c976b7eb6a7d8a7` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-canary-unbalanced_probability-v1-exit.json` | `3a8b8b445fbf9bacd957a6e663792971bff5cdef4f6abff5bad08fbe6efce1bd` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-canary-unbalanced_probability-v1.log` | `68855ae0d8442bfd94b27f0c863087da7fcf528a109f64e9b9b910ea834d748e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-canary-zero_and_two_normalization-v1-exit.json` | `29a59a983c86feb2a73308365e2b8373ed1be3f881a678a17a82aefbbecd856d` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-canary-zero_and_two_normalization-v1.log` | `27ac8a48577fc001750ff545ed893becaa0a4a145ae6e132480d69179fd7ffa7` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-binary_mean_minimizer-v1-exit.json` | `30e2cf49622e2f0706fb6cc9fcf06faec8868c7f0ea3e9387ba603a2d6198777` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-binary_mean_minimizer-v1.log` | `3f94b972afddcfd007b46bb00fc5e82ae12735c50a6aacc0b856aeec6dfc9f1b` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-binaryStream_cons_last-v1-exit.json` | `c9527b35445f16b82921f4c515a363b2f8c4e1382baf52eb6d26916904211f86` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-binaryStream_cons_last-v1.log` | `cebe0ac48592c5e2ca863c9f254e605dfd6eed30fc7d4e32d6b9f4b77fc938f4` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-binaryStream_cons_prefix-v1-exit.json` | `8a913b9cfd470a46cd6391fcbc6ec229c3c40e316fc25b901f4c002164ffacdf` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-binaryStream_cons_prefix-v1.log` | `b64f0b53b6624639d8b9f827fe6cc0e51cb598bfd8479e2361109f1a6ffcb52f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-binaryValues_cons_prefix-v1-exit.json` | `6fa2645d6c9d75e7a0a751ff8af548227b6c8d702ed3d5b3d682cc20badf26f6` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-binaryValues_cons_prefix-v1.log` | `ccf5e7a944d6700eec30fac34ec491e88c9cbd6036a72fdedcaa336cb71eb5e6` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-binaryValues_sq-v1-exit.json` | `cb69dd31d6e4ccec779456dae4a5a529e37fd577d648ae907b098d265941263d` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-binaryValues_sq-v1.log` | `14c2925be71cb7b5a81208875c803d3f910bbd5a04329eb7cdd7434a9fc09fb1` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-binaryValues_sum-v1-exit.json` | `2086dd2af6351ddf52b66a0f152dafc562da48a833de740b816354cd80c545a2` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-binaryValues_sum-v1.log` | `6fe101a50f86fff9efa94666b5eb466f7cc46337d6620549b1517d1b05a3de9b` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-branch_mass-v1-exit.json` | `6f816d20ac63e84753717400f0f81277a51b091a5ecd9d775142ba86d6ed3025` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-branch_mass-v1.log` | `27d4c5e73418849e033ac672266cc6b7b1ba940425553d84ef9026c755837ebf` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-causalPredict_cons_last-v1-exit.json` | `69874e23d352f96383dddc19a3274f231fe0b9e5e41d8bc9caf10df7c645b4e6` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-causalPredict_cons_last-v1.log` | `11b54d30e3b5261756a5c7ad7679f6e8b3e6dd3a8075e6fd528879e533b45677` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-causalPredict_history-v1-exit.json` | `de7a44ab480d6f2076d2339ef6b70b7fdb81180743c2301a6d056b48436b9980` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-causalPredict_history-v1.log` | `f2692bf6edc849725090bc4dc3fbae6025751c82aa67392abb9d1c3547eed407` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-causalPredict_prefix-v1-exit.json` | `6f6c4725b916be52dc5932ff93119e53b95ecea363cf6645870725a8e422e0c4` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-causalPredict_prefix-v1.log` | `7b7924ee5094aafd007d9900eb28ed48be9cc0eb755cea33b07eb9e6553c1af0` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-conditional_square_lower-v1-exit.json` | `669df753c06291540f85fb7090f9907853ce72bb500d3c75ca68afa03f24e8d4` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-conditional_square_lower-v1.log` | `30a76d1c5778295b157027434aebaae94c2e9e6d7cec8f0e3bc708da71ffadaa` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-expected_heads-v1-exit.json` | `5bb2e873a1fd5157c38c03539a86c2b1bc2dfbfc23daec29619970b4796e9fe6` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-expected_heads-v1.log` | `3a80b74d1fc952af6d8a9ece6ad67bb801965a2f51f937b99f398a607e411173` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-expected_heads_sq-v1-exit.json` | `b2e51a22bc45077983d2930375d7f52ddd1fcd69e4b0153675a70e6e252ff1f4` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-expected_heads_sq-v1.log` | `50ca869be12e237ff0f3dcd751cd19da8b344216581909b250224461b6a0583b` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-expected_next_variance-v1-exit.json` | `ba09fb9acd2d52aac22fd8c2d03b73385de7b2111553aec88703bba43228477c` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-expected_next_variance-v1.log` | `7f240e634e985e1cacb84600f548c448c6c421ecac3a82bb6232ce9e9e3a6065` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-expected_pathBestLoss-v1-exit.json` | `da7b5fc61e23438e5d50a7321bf00e7f651c37c8b73b2e60ef69f98a5b044471` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-expected_pathBestLoss-v1.log` | `efef49b79c0d99b000befca94c55961c3fdaac880b4a3622213a2a0ded8349c0` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-expected_pathLearnerLoss_lower-v1-exit.json` | `8f639c3a198305e876b26b43e9410cbc98e4a24cea9dc3d326baaac1a19502ce` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-expected_pathLearnerLoss_lower-v1.log` | `dc05379bbeddadfc3528384c18a271177dacc7168015d0edb6826d77ec24b411` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-expected_pathLearnerLoss_step-v1-exit.json` | `ad766f99a4c9373432c7e17ba85aeacf0d9b5f55ddd7195880cc722316af4da0` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-expected_pathLearnerLoss_step-v1.log` | `1aa885020e34bb5bbcd81b1285643b3921456e4f98f27f7b7672325eeba7edd2` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-expected_pathLearnerLoss_succ-v1-exit.json` | `1e48cf8ff7f598ab4735a8814f8d75fecbe57666e1a31f173e1bb07411fcdd24` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-expected_pathLearnerLoss_succ-v1.log` | `2bc8a5ee77059542288439cf0f46a9d1fefaa48686e4dca9d8c3a7be41b129a8` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-expected_pathRegret_lower-v1-exit.json` | `bd4bb9e4f1a6b33080f6eacce53b2ebd7a002421debecfa54b3be260f00e8c20` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-expected_pathRegret_lower-v1.log` | `73d020f7949b8e8ec57b78599068861fe651880b972cfcb3f0fb84c131a84a8a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-heads_sq_succ-v1-exit.json` | `e01b3937431965f5dc5130bb8deca08eeb39e78709a8d7f4a029ffd3179be475` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-heads_sq_succ-v1.log` | `b592e3fb66059783779f86ef45d7bea2afe4032dd426fcfa385cccedabfd5037` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-heads_succ-v1-exit.json` | `b10d176aba7273c1054ef5a074790a0fba27d8d6768eb008620c7a460b4892d4` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-heads_succ-v1.log` | `37e0ba8deb413f29c7fda55c6d43602c7db411bedb5399eccc895701a635830e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-pathBestLoss_count-v1-exit.json` | `49cff60d87c721c9ef2172346d8dfd3475cbfabd5fbb6f0a70d6b96c7c306f7a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-pathBestLoss_count-v1.log` | `96c5784e3863eb2337569572284f954a57a1c3a79f2db150717b11be1d015537` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-pathExpectation_add-v1-exit.json` | `0a3ad7c98e5690e254058db56daa36048e0daa64684947a6263b4e275c667cb1` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-pathExpectation_add-v1.log` | `33c307f12179076a966e7a8dbacf50306d7d18fe03742c9548da50c66513e92c` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-pathExpectation_congr-v1-exit.json` | `5e88f25ef39efbbf3651f2e2543283e717e2fd7799bdab7d7d48bbde3040c911` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-pathExpectation_congr-v1.log` | `937d99dc3f47fdf803d69f2599f76eec15176ee9c58b2c1c13a56f0d19faa387` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-pathExpectation_const-v1-exit.json` | `679a909a30044c88a9bab091ce31716daa5c354ecb4932696cc909246703be9a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-pathExpectation_const-v1.log` | `fa35e3d32a5a48cc0922cd7205615ea04ec94e93a7e0264b00ebc5857334719e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-pathExpectation_const_mul-v1-exit.json` | `a6866bc6f8df7a51668ab7e8ace4fc38f90b199965952b335c96d4d1c201ca5f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-pathExpectation_const_mul-v1.log` | `596eccd46868c4a192356bcb0dde907ce2fb30fa01ee3b0b63f9c56abc5204e0` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-pathExpectation_div-v1-exit.json` | `fade979006beddafe18faeb9d4d4e24dc0d47f5279544c19d6997f20fa477cad` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-pathExpectation_div-v1.log` | `51d136758bf6479282b8f3cef939d8272350dbf2f0fc5802c888a20498f284a5` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-pathExpectation_integral-v1-exit.json` | `42586287bd358d2826e4645924c4cb82f1617cfa879413963c3386a55ce4dfac` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-pathExpectation_integral-v1.log` | `ff08c0e74f453d226f848643f7c24df21f87d13609db6ee587036b905b02da15` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-pathExpectation_mono-v1-exit.json` | `e381101371ac50a07bed7de0e6104887607f849fb0f467b9e99fa96537c5c46f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-pathExpectation_mono-v1.log` | `eb37e5dc0b5ce70348e9c2fca72f1430aeab8ca530c67ecda879ca029fc175cf` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-pathExpectation_sub-v1-exit.json` | `124222ebbbfcf54950bced64bad1fcc46f1c5be8d53c8bcb1993ab8101c23092` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-pathExpectation_sub-v1.log` | `3eb8c464c26697c8d2e3c870d67cc7d66b2083ec64852fd19fcff445cd98ebea` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-pathExpectation_succ-v1-exit.json` | `4b44dbf6b0e83dd7f0696093cb52ce649d118adac9ccbabd2e988d8ad9496ca1` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-pathExpectation_succ-v1.log` | `99df48363a97c77230606c4fbb9e71d0089df3cf088dc34d6c41395e0ea64286` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-pathLearnerLoss_cons-v1-exit.json` | `0d0d2fd0d3f9c949de42b0e9ab5b917965d19a88576893f5d9827c2377e608b2` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-pathLearnerLoss_cons-v1.log` | `8d74260e4a2e6e202f377b9b62fec5fc80423961064e9dc5e78d9b7e8e52e873` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-pathRegret_abs_le-v1-exit.json` | `050daaff3a23e47069a5e03be78ed7540d8a836b455abcf06699b51d80b8c240` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-pathRegret_abs_le-v1.log` | `d55d9da28c46f40a46c225edcc21efc7be9314e19ac9811563ac995ca2a96818` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-pathRegret_eq_losses-v1-exit.json` | `a1257184c7f1105531738f1916164508385642dcbb15653c717452dc0ddd17fb` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-pathRegret_eq_losses-v1.log` | `3dad32edd1280112dc54388e4be3d3124ab40e0604771bb018a30df21e6d983a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-pathRegret_integrable-v1-exit.json` | `8b1bccb72c601cd1b47cf39715359faefc298fb6e5a113aa1f2ea3a9e9703eb7` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-pathRegret_integrable-v1.log` | `5d8eecbc89533176dc467a867345ca443178fe2e029f000db06aae0858dde23a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-pathRegret_measurable-v1-exit.json` | `648768eaa0b6c06900002d146a2f400eee29c5de6cad56e7cd63e1c7aee17606` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-pathRegret_measurable-v1.log` | `2588b38adbe71c8cc0aec54b874927da05b2a51c75e40743c7da885421000153` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-pathWeight_nonneg-v1-exit.json` | `8dc6e82d79579cb1f70e62129226f5a0fea90861575f2a8611da5eda97467d93` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-pathWeight_nonneg-v1.log` | `4c9209ca2f7da8a593e526c5a41c58a5372167172d71741c4aa1943fc0e602b5` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-pathWeight_pos-v1-exit.json` | `f4ac310ed77bcbc613b36298ff6ac778bd9c00e958613fbbd1894cf74d21f9a1` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-pathWeight_pos-v1.log` | `4e5ff23c6024e25c43de069f324d876015dc64479cee907f047ae14799aa2f2d` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-prefix_distribution-v1-exit.json` | `9aca83e1e8e34a40a71a638d6f01f9bb1d86158490d6630516ad09410ab2695e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-prefix_distribution-v1.log` | `65538a4779fe12a6398c476284d6333747e2f898c1d09e63046f2c29ec26bd7f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-prefix_mass_one-v1-exit.json` | `9d1a100bb96b7d4b29d2bc9109e6eb570e001db3751b20d54fe2ff36069f6ba9` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-prefix_mass_one-v1.log` | `3ec23f2d1ea740e6144a40ba515bf8578efd6a3d24fcd7309ae375e5afc34925` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-prefixMeasure_probability-v1-exit.json` | `7fbead5555b2eef0c363a7958b7040ffebc248757665b4a898e75884ba942500` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-prefixMeasure_probability-v1.log` | `9f3bf1ed20ce225d9d584a3264cfc79ed85303fc69277348003f586517b5e971` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-probability_mem-v1-exit.json` | `718e4abe0903127025d9e1c297351c6507684b7b525f59cdacdad5ca4136332a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-probability_mem-v1.log` | `0e468bc9c47c7dc24000c261f48ac56658cb0dd2d066030fd639651c4c73f3b4` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-randomized_harmonic_lower-v1-exit.json` | `a8e6a4dcdce2bd901b74735e094b573595b56a5736f5a7d87cd4b396926562bf` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-randomized_harmonic_lower-v1.log` | `8a4c0e39c5073afe80fad296aeef3b6bb1d6bbaa54d8ec0f126f366f194f3f06` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-randomized_log_lower-v1-exit.json` | `c03513b7a7cc840b0288453edb942cc9b206bd54e2a0bd21141cfbca908be7ed` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-randomized_log_lower-v1.log` | `45713f1ebe1b651274a1492303f5084b3c5a8dac792fd4f7de602c1429e7dc97` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-square_loss_mem-v1-exit.json` | `25f1b12cc32d547f48dc2f810621388c9dc77ac7d2d6f790e5e2f27812799719` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-square_loss_mem-v1.log` | `2a8d6e2a741a18c61c4a78cf25373f1770a5e831448057692fea0e2c60e585d1` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-square_loss_sum_mem-v1-exit.json` | `63d56cea9acd35b75fe9c98b48a65097d8eec864f3188a88761e1ac41bae4451` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-square_loss_sum_mem-v1.log` | `f01bd34ef0a9b3439b879a104d7e2aa311d2a443e361c5f4b7719a58ae963a4a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-sum_vectors_succ-v1-exit.json` | `72886d5573dabfe8dedac442a6067c499e4fc778ea783b24d64b1588ef6ce767` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-sum_vectors_succ-v1.log` | `589519257fbb29250f3efee37996342a1d403e8555bde25947cfe2a6235c3e16` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-variance_sum-v1-exit.json` | `98c2d2078570d07a24134f184d7dd211ee8bae17edac325549939b388cccdc16` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/full-safe-public-variance_sum-v1.log` | `13e3038fd89672b567603c60f3cb483fd7766bbea94e24cc9a195b4b6c39799d` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/law-addition-v1.lean.txt` | `ffa7c37add13d767bc16cd7619a330611a07859d78e742a5872784b1d0f07a29` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/law-addition-v2.lean.txt` | `5db19f541c2bae1376d3f7a7a25fa0d5e25d9b9da54955bb90cdec0dfe948443` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/law-attempt-v1-exit.json` | `8644ae33e053214e9e0d7f6a86285378b275c34a3d6587e81416a4e6e2e962db` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/law-attempt-v1.log` | `cdb9625b565e9db329bab55969d93e6d254d2fb81ab824b606689fee7a164f4d` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/law-attempt-v2-exit.json` | `4eeac6020e87370410ecf43d6e3b71ba6b284e56f7decd7edba5f322106d3187` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/law-attempt-v2.log` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/law-progress-v2.json` | `39e6ea09d3efaf802d953e2cefc0d4c8c1f55a50cbc3a064378fd189de395c7b` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/law-promotion-repair-v2.json` | `9b6c4ccc7576d563341587212b1a94b8acb52b6c3e2a39cfe8eacc49ac28d2ca` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/law-repair-v2.json` | `e61d68791b3ac0ca84378a1801fa5fd98eee5efa48eeaf9bdb9202353a8155d5` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/leaf-fences-v1/probability_mem.json` | `a10b5f79469febfd9f66a3a3f9e8d48d1e59723ab5add0c72a43bf8a5067262d` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/leaves/all-axioms-v1.lean` | `e336153c43143067e5d2e3f0dfdeff499746a4d13b5c87a5c7a4c0f1e82bc997` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/leaves/all-exact-types-v1.lean` | `6107466660953411421ff7708cb09fc0e141b8cf812a57897f0f09deab253ae4` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/leaves/all-exact-types-v2.lean` | `16e95dbdeb1400d4d7779aa7c8fe1c71c884bb56ad2857730c70005fa0c74279` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/leaves/all-exact-types-v3.lean` | `32e678e6041ec669415a14ae5e9c319c898f25cba7914bd07b5bda625845bc2f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/leaves/causal-v1.lean` | `837b09d72f1f7fdaea9a7fc265b7e7fb409bfef6690a6954cde8e20deca0fc66` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/leaves/causal-v2.lean` | `c9380fd430f7af7f7c0f120f84357fcc39c626ee1259cbb161191f79d3394b2f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/leaves/deterministic-v1.lean` | `57e96b0702332ce55a62dae6ab56316e750eb6e097e6430209809807dfa5b2b2` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/leaves/deterministic-v2.lean` | `3c4a3cac41340499188e06c21febfd07f505eb8c1d74f8dee0df18d310332b02` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/leaves/export-actual-dependencies-v1.lean` | `449c9573da72ec1e6b5bfc0a3832e9c3ce736a87d771d055ec96f17914faf799` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/leaves/law-v1.lean` | `c13f608b5f481c9ea65ba30af975566ceb96934c0a8914bdde4af65a672dee0a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/leaves/law-v2.lean` | `2e9eff26102f09c80778e2b5a871d38e038422a51b07f2c43c2a6710bc2ad10c` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/leaves/loss-bridge-v1.lean` | `7d3430ee2d43594833d3cfa879d02633b4f8e81a55eb1d2bf7376c6f65c0b2b3` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/leaves/loss-bridge-v2.lean` | `0c3ced5ca5070767ad355ea4a59abcdd19b15f5b68585029c83ec1abecd00de4` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/leaves/moments-v1.lean` | `3a78fdf93d0353b7c54564226f597049ef004536b88beaa8a91e7a28fc925c31` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/leaves/moments-v2.lean` | `5a44645a17688feb7cc4fa93b84f988ab27e3ae3b154646ba3f8b36db47605d6` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/leaves/probability-canaries-v1.lean` | `fc095e4d31623c4e7ac0a5ee5c23bf9074d5901b6f12bb070ba21e0fddebf5e3` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/leaves/seeded-v1.lean` | `d8352872b491bbb51e89dddcc93552a8e2beaa67c278d9b80a0b7017c87dbcd1` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/leaves/seeded-v2.lean` | `b467801b4fe10e50bfd9744912cc2384a95871e30ec50304209b4928731fb61a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/leaves/seeded-v3.lean` | `9048536f028026dbb7c98c41ad95c739aeb0fa8e0b549d2621957f3f551c3014` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/loss-bridge-addition-v1.lean.txt` | `d6fb4d5e9d6fc1f171b03b17d4eb53f8ecb8bdbcca5685c9e106507c6d36b8e1` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/loss-bridge-attempt-v1-exit.json` | `b6daf47d6f7eaa1c94674dd5f0d22e3558ab890fff21396ef9eedee815e66442` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/loss-bridge-attempt-v1.log` | `00cab053af9ef4a2cb3f80456ef55738144ee743b84e12b4ccfe9d90879c2beb` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/loss-bridge-attempt-v2-exit.json` | `44e9b2259a8d650446ef92f6fe323c329c8f9759298337b1257d5bcd0fd728ec` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/loss-bridge-attempt-v2.log` | `1b9392d18ba4d6515037c5dfe64de2db8adbf736cbbc2a5fc6bc2862a4009742` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/loss-bridge-progress-v1.json` | `65ed97c86637516335a575ba288b4784c8bf0a946b7c4c57c0efb8e998eaf4dc` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/loss-bridge-repair-v2.json` | `b1dcc2ad4f5e3ee42b2d933836b8b617221afa5efff3c63df82e65ea475a4d84` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/memory_digest-candidate-v1.md` | `a337a9edb8ea057ecd8992c91e6e35602395a7b4817fa12dabb546ed025bb819` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/moments-addition-v1.lean.txt` | `b7684b5149a29626a4bfd4dff83ff3f918db9e529cde0d663d606cae5917a5a3` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/moments-addition-v2.lean.txt` | `68a42aad4ee26b77c0f00675ddbde425dd29b5bd287a0e0a9183fdb08083ba46` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/moments-attempt-v1-exit.json` | `e50f4fd91ec62fb12bddd8e7b245e3912fef25f656ea0c966d34979dd53acf6b` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/moments-attempt-v1.log` | `bdeb73382a6e341fd728b7fdacabee5c6cfbcc11d266cab526937995b1f94b56` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/moments-attempt-v2-exit.json` | `12f417f6e967e2d127458ed109b7de241a0bfcc3f0378c1ef1096a9026e70a2a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/moments-attempt-v2.log` | `bc337b11d5006b08ace2b373d1cce40654498af764a7c6c7e22fc825fbd0565a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/moments-progress-v1.json` | `85c14b424721f8660bac9bc355238ec2664e903d17f941fd9b70c817b5b64421` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/moments-repair-v2.json` | `bb4bfeee867a179951f960f301a5b465979203ac6c7481c386eb12108de695b3` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/planned-canary-fingerprints-v1.json` | `8329a63b98dcbdf638efe5f12b3921891b8b2dfa634ec49b5c62aa63dd5b523a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/planned-canary-headers-v1.json` | `a3ebc2f7e9dd04b8096ae0900f50f74bd03df1f68dbd535b5a1d904479bb20b2` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/prepare-body-review-v1.py` | `743ca5db316fc374f71ce904a90ff87fb46ed21f85e2a6bb360b5570432e63aa` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/prepare-canaries-v1.py` | `957fd74a6a162767a51c4a67cba7d0e1ca9450494b81ce9d1cb44b6bc60e40e4` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/prepare-full-neutral-v1.py` | `cf384220e422bd0f4327e288a44d7bc5d0925def987e670a7328099dfb6ae6a8` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/prepare-full-neutral-v2.py` | `1d65974e86fbd82e3d3c7bc0544a56a806d975b8d16b132d5616d4e5c5ccbedf` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/probability-canaries-v1-exit.json` | `dec75f537120edf8c9705cc9e18fe0137a78afc8f39f3ce8a4f6a1353c62d66a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/probability-canaries-v1.log` | `b2542f7c72936d848d5d4f541c56137638f69686ce3f365cd2d9670f0ccc9425` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/probability-fence-v1-exit.json` | `31246d6c4b70a558485925390aad78f6eece83a87601497fd633d87539548a71` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/probability-fence-v1.log` | `a10b5f79469febfd9f66a3a3f9e8d48d1e59723ab5add0c72a43bf8a5067262d` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/probability-leaf-bindings-v1.json` | `43a53f52358671f9ff8f7928df7fd4a5bd709cb6fe874d05ee18c38b582a290d` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/probability-safe-v1-exit.json` | `5528b2913596a7fbb6fd021bb38ec67b95bfb8871156972a08ee8043c0ee06ef` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/probability-safe-v1.log` | `0e468bc9c47c7dc24000c261f48ac56658cb0dd2d066030fd639651c4c73f3b4` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/probability-worker-trial-v1-exit.json` | `0620df0c9b482b71212fa72a43d97c135c373db845b85a064dfdbb022d066f30` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/probability-worker-trial-v1.log` | `e51223889a61607ddfc1bdef2de6273849f9e5fdb0b1fa0683697ff68c4f7e2d` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/promote-causal-v1.py` | `55e33f1ee968fe939b9d054f1d46255d4a3fade6963beefe26bc2bb1fb27d52e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/promote-deterministic-v1.py` | `1278e054b77eb3ba9469d441f140d82173a367f4b5f3638a3db38366b72acb8f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/promote-full-body-v1.py` | `835948b8eb7a57ae85fca716fdf1d867d6244a43fe52b6b0d3d38ebd5f63422a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/promote-law-v1.py` | `b94faedbb930a16f32b302f489097dfaf8657cc9713ffeaff6926ec63c55092c` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/promote-loss-bridge-v1.py` | `8a9e9c3e96c11604cc49e4db71c34a700fb6ed39ded7fbd94315f159f30627bf` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/promote-moments-v1.py` | `a5951f4489d3bea909c5d121d9c9bc2e835ff66d099912567ab4c8eeba9649b3` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/proof-obligations-candidate-v1.json` | `297a60238bff512257faa1f98467ade12a6c94fdfd7482b0441ab55f2f2ece10` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/proving-event-v1-exit.json` | `24b7806625b0d10bb73861a7f219c1a105d660683f7e3eb9ee2e4d402c00f688` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/proving-event-v1.log` | `93587f7278a288330e2cd98be83596d9a6fbdba955538f6c1931dfa65e939ea8` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/public-canary-build-v1-exit.json` | `6ca435469b05eb7d28a008b876520867f929f979ca071c9812a147f9838431b3` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/public-canary-build-v1.log` | `9a6e3c0fbab9265ec054de8cb986a1ecff12f5170d77e17d9967ba8e4d58d2ae` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/public-canary-build-v2-exit.json` | `6cd023a9dbb8e39ab21ae70d32fb7d993eea68d288416ba15b3ffae4a2ae9d8a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/public-canary-build-v2.log` | `ff71602d8e2f24a06e6af7cbe4f4b12122e4d925f0a082c54ea81607aa9375a7` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/public-canary-build-v3-exit.json` | `1f3371c2a3bf2dc3396a0b1b94f7e6bd40c00522e4bdb3467027b63a2c8ff7b0` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/public-canary-build-v3.log` | `0e65260644694810cdb965c55f6dd72eb342b890b17abe0c2a4e9f597cd20b2c` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/public-causal-build-v1-exit.json` | `8c44a0c37816c94fe047b658e028b00bbe43df7d6540ecbb3ee01857d42b37ef` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/public-causal-build-v1.log` | `59da385c22338e1a3a68e0ea785e7ed6e3907c21ce96daaf290ab9ce5c8a5d86` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/public-deterministic-build-v1-exit.json` | `242c92853f999935c39bb5585e4cac8503e87dcaa6a365c78822b0d4a6437dc1` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/public-deterministic-build-v1.log` | `937dee9dd04d0d1af98ca3f6feae22e309137b74f5b80a82a4fc8bb611f60523` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/public-full-body-build-v1-exit.json` | `fd0cf537f692b3169e6c9f23f902121889fdadb6aff28a189df97ccfc96a7343` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/public-full-body-build-v1.log` | `54d4b365b0d0a08d4f004e323f744a201a1bd2be4802c5baab5e8f8ad5b5fd1c` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/public-law-build-v1-exit.json` | `1be70f259c5e7dce569a33283a6921769a056230db4b8ebce694489575c2d35e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/public-law-build-v1.log` | `345c7e083fdd3e9722d42f7c8826fca5b83d71b960f1834a92de663df02de2b2` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/public-law-build-v2-exit.json` | `81553f036cb2a5138913a85d3c3100783c6574401f3e771e09d3c09a27ff5fc0` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/public-law-build-v2.log` | `ab1447cbdb342869b02cf20ae4cd7a403b575c2b02342c079deae2a94111fd92` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/public-loss-bridge-build-v1-exit.json` | `4cf24849f8d06eb76a5f6fdcb987a13a095d23972d1a156ecdc8ba68850806d3` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/public-loss-bridge-build-v1.log` | `25f32839ee60d0392a6e27d399f72e70c4d3682c05ecebdf374a3fb346e3cded` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/public-moments-build-v1-exit.json` | `a539fd682e2a592f47e34ae30147ff40413d643138293afd573efc768d8df50c` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/public-moments-build-v1.log` | `065928cdcdedb9602162ee60b7e19313ae950bcaa2594bd18e166b76f5c1ee75` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/repair-canaries-v2.py` | `05669564d9725d898d76f4084eb977b2a5eba4f96549bf05d5d4dc9bbe2a20c6` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/repair-canaries-v3.py` | `3821dd5d10a95acbccf934cbc80b906c51236f5df8a71e72f7ba9894604cbf2a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/repair-exact-bindings-v2.py` | `4ba35f0fe3482c0da1290dc1dd00cdc3d169e20f3d984fed1484e97fa4af18ee` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/repair-exact-bindings-v3.py` | `0608fdd73b6f3babeb511f67bae9e01971910cb08d2c2f59a57e1e81471ed1b9` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/repair-law-promotion-v2.py` | `ced126d664c32d663f7ddd40104decdbea24f31573b5a322cdf2897911cf6418` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/repair-stabilization-fingerprint-v2.py` | `0ef845d0b8cac633eb824a2ebc1602d458efb172a74cc9c03644f534a802f531` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/required-value-pairs-v1.json` | `045853eee17319a2114da9871aef521e79a28d8603b413ef4580bfd491ebd919` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/resume-full-audit-v2.py` | `73e15ac24bb13c65ced05aed6cc098eae712fcb2e90fe1376edaf43a1fb954f5` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/seeded-addition-v1.lean.txt` | `d3954ccd79c63e1152a04930851aaa2acd9dd2e4d72e8435b7211393f5d1ab18` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/seeded-attempt-v1-exit.json` | `434b1ba75fa76a80ca5ae8dca8ab3f0938343eb3423d6df53021ed559ba7ed0f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/seeded-attempt-v1.log` | `0e710fa0b16e21a6d8199b752ce400dda6f57f565429677c1c729574f6d9412a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/seeded-attempt-v2-exit.json` | `51cebbd381c0b5fd22285f3d2c09c820db62150e0763e3bb1a638d045dc31d90` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/seeded-attempt-v2.log` | `c1e8443d835196e41e637c497f9b1d876771d5842170923893d67c952bba1aa3` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/seeded-attempt-v3-exit.json` | `b7587aee79d787c6343ff41d367118e0f7851d08857407146270f1b9ee1f12db` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/seeded-attempt-v3.log` | `8aca5472cef3026587acf74bbd24a82892a083163b9a54a4f1672ef11a8c61c2` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/seeded-repair-v2.json` | `40cf7163f5b4a8093a8a3715b658ebe8ed2115f6f64952f65163b8c6b8f55d3b` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/seeded-repair-v3.json` | `451d8baedd4f6b2fb1b2e077275b20b5679af295a67e304c58f92e829752135e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/BODY-review-conversion-windows--ONLINE-GUESSING-LOG-LOWER-20261008.md.raw` | `b72cf6aae477568f8fd19e7ecc084ed10bf1c25ab4627cc83c64deb353ff4d3f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/BODY-review-proof-blueprints--ONLINE-GUESSING-LOG-LOWER-20261008.md.raw` | `d565347255f6f11add7885f8b14b072e400f870a74019712c5b29cb0311a8eb4` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/BODY-review-proof-obligations--ONLINE-GUESSING-LOG-LOWER-20261008.md.raw` | `f54a2c6fa195b059c28f6a42911ac280252553ad0c86bd52396c4cbec04e25dd` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/BODY-review-research-wiki--retrieval-index--ONLINE-GUESSING-LOG-LOWER-20261008.md.raw` | `d565347255f6f11add7885f8b14b072e400f870a74019712c5b29cb0311a8eb4` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/BODY-review-tasks--ONLINE-GUESSING-LOG-LOWER-20261008.md.raw` | `5af0aeda3713ffcec98e3dcad388991ebd02af20df25c120e9bfe3cfb421ef03` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/canaries-body-v2.lean.raw` | `6a676a88985c71fbeb8d88ffd282f454e08e354e531bede1a5187f97dcac3c9a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/canaries-body-v3.lean.raw` | `7fc1fef5234b0329343d2d8e593ad4aee88ef0aa57b85523dc842a34187f0c58` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/canaries-first-body-v1.lean.raw` | `931decf905ce24d8ef9c3adeba789671625902a30923fa2484dbae8f3f1ca0e3` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/public-causal-v1.lean.raw` | `c9380fd430f7af7f7c0f120f84357fcc39c626ee1259cbb161191f79d3394b2f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/public-deterministic-v1.lean.raw` | `3c4a3cac41340499188e06c21febfd07f505eb8c1d74f8dee0df18d310332b02` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/public-first-leaf-v1.lean.raw` | `c2fd9f3c07fca9f537747b68d77f1aa90244855c4d8c3b7ba35d597b50fb8650` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/public-full-body-v1.lean.raw` | `5f4b6bd8e3300d8b94862aa95f1d46e68ccea11e3b6261bebbf9d60aa6c9a5b1` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/public-law-v1.lean.raw` | `2fb3a28f46fbaf781bd1db8a202a3d05b3e124565cd1d3c7a6acf9d8d3d34b41` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/public-law-v2.lean.raw` | `2e9eff26102f09c80778e2b5a871d38e038422a51b07f2c43c2a6710bc2ad10c` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/public-loss-bridge-v1.lean.raw` | `0c3ced5ca5070767ad355ea4a59abcdd19b15f5b68585029c83ec1abecd00de4` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/snapshots/public-moments-v1.lean.raw` | `5a44645a17688feb7cc4fa93b84f988ab27e3ae3b154646ba3f8b36db47605d6` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/source-contract-inputs-v2.json` | `dacfb20a1fb7d501b310e053efad728abdf2d9225a5da4bf122f24518c4561eb` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/source-contract-receipt-v1.json` | `e89c703f34f87adc95c4ca333a2bdf45e0ce4d487617dd6436774bfa29767fe9` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/source-contract-review-v1.md` | `eeab02d8cb328af1a7955999a405c097c4399812e4849fbca37f9c635d84488a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/stabilization-fingerprint-repair-v2.json` | `b61de22ae52f0912973a8aa80b3762c349a24afed3d47b0a91d3d5ac54654965` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/stabilize-and-first-leaf-v1.py` | `c4265c2c6f7a0b74fef3ea5fcf7e0234359c1e01f742cdcf51c3b0836e1301ba` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/stabilize-and-first-leaf-v2.py` | `aeb8bc1c64abf8e3971b784b3c1e7e145379bbc20f230f7c35d2c614aeeef332` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/stabilized-contract-v1.json` | `db56b49747fa2cd258de4238d08452275fcb0c50e9954d26cc34073636330b73` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/stabilized-event-v1-exit.json` | `5a5aa78fca5ac6e20518221a018755e110729e4ce740eaad055a28fdd05cbbac` |
| `E:/ABRL/worktrees/research-online-book/runs/online-log-lower-20261008/stabilized-event-v1.log` | `7afdaa9de997c44ec09e3ac6f01d7ec47cdf14d7474d39d0d7d9d0e8f5ea1d5c` |
| `BanditRLProof/OnlineGuessingLogLower.lean` | `5f4b6bd8e3300d8b94862aa95f1d46e68ccea11e3b6261bebbf9d60aa6c9a5b1` |
| `Tests/OnlineGuessingLogLowerCanary.lean` | `7fc1fef5234b0329343d2d8e593ad4aee88ef0aa57b85523dc842a34187f0c58` |
| `runs\online-log-lower-20261008\body-review-inputs-v1.json` | `5bdc4fbb707835f7cb599159f95f14a04acc026ef54ba975eae7d23df94c531b` |
