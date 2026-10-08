# Neutral reconstruction, v2

Actor: `/root/osd_blind`. Requested settings: GPT-6 Astra, medium; actual runtime model and effort are not independently attested. This actor has earlier staged neutral-decoder history, including this package's v1, and inherited background may remain. This is not an absolute-blindness, human-review or external-independence claim. The present reconstruction uses only the designated v2 packet, neutral context and manifest. Earlier files were not read or changed. The declarations `def Q... : Prop := ...` define closed proposition types; this report supplies neither their proofs nor a source-fidelity, compilation, chapter or acceptance verdict.

## Notation and complete scope conventions

Let \(I=[0,1]\), \(I_t=\{i\in\mathbb N:i<t\}\), and \(\mathbb E_\mu f=\int f\,d\mu\). Every sum below is over the finite range \(0\le t<T\); natural indices and horizons start at zero. Define notation
\[
m=\mathbb E_\mu Y_0,\qquad v=\operatorname{Var}_\mu(Y_0),\qquad
J_T(u)=\mathbb E_\mu\sum_{t<T}(u-Y_t)^2,\qquad
A_T(P)=\mathbb E_\mu\sum_{t<T}(P_t-Y_t)^2.
\]
The common assumption bundle \(S(\Omega,\mu,Y)\) means: \(\Omega\) is an arbitrary type in an arbitrary universe, equipped with a measurable space; \(\mu\) is a probability measure; \(Y:\mathbb N\to\Omega\to\mathbb R\); for every natural \(t\), \(Y_t\) is measurable, has the same distribution under \(\mu\) as \(Y_0\), and belongs to \(I\) \(\mu\)-almost everywhere. These are assumptions for every time, not only for the chosen horizon. Same distribution does not assert independence. The bounds are a.s., not pointwise on every sample. Write \(D(Y)\) for the separate assumption `iIndepFun Y μ`, independence of the whole indexed family.

Write \(H(\pi)\) for the following precise policy assumptions:
\[
\pi_t:\mathbb R^{I_t}\to\mathbb R,\quad
\forall t,\ \pi_t\text{ measurable},\quad
\forall t\ \forall z\in\mathbb R^{I_t},\quad
\bigl[\forall i\in I_t,\ z_i\in I\bigr]\Longrightarrow\pi_t(z)\in I.
\]
The finite-product domain is the function type on the subtype of `Finset.range t`. Measurability is on the full real product. Output feasibility is required only for feasible input tuples. Nothing in \(H\) bounds outputs on tuples with a coordinate outside \(I\). Define the actual prediction
\[
P^\pi_t(\omega)=\pi_t\bigl((Y_i(\omega))_{i\in I_t}\bigr),\qquad
P^*_t(\omega)=C3\bigl(i\mapsto Y_i(\omega),t\bigr).
\]
Thus \(P^\pi_t\) uses exactly finite strict-past coordinates; no current \(Y_t\), future outcome or explicit random seed is an input. The universally quantified policy is not required to be chosen without knowledge of the distribution. At \(t=0\), its empty input imposes feasibility vacuously, so its fixed output lies in \(I\), but need not equal \(1/2\).

These abbreviations expand exactly as above in every quantifier and formula below. Bare definitions use Lean's totalized real integral, real infimum and division; their existence as expressions does not assert integrability or attainment.

## C0

In words, take the expected cumulative squared loss of each fixed feasible real comparator and then take the infimum of those real expected values.
\[
\forall\Omega\ [\text{measurable space}],\ \mu:\operatorname{Measure}(\Omega),\ Y:\mathbb N\to\Omega\to\mathbb R,\ T\in\mathbb N,\quad
C0(\mu,Y,T)=\inf\{J_T(u):u\in I\}.
\]

1. **Objects:** arbitrary measurable space, measure, outcome functions, horizon, real feasible comparator.
2. **Quantifiers:** \(\Omega\), its measurable structure, \(\mu,Y,T\) are definition arguments; the image-set variable \(u\in I\) is inside the definition.
3. **Assumptions:** none beyond those argument types; probability, measurability of outcomes and independence are absent.
4. **Conclusion/operation:** real `sInf` of the image \(J_T''I\), with the infimum outside the integral.
5. **Constants/normalization:** interval endpoints 0 and 1, squared loss, unnormalized sum over \(t<T\).
6. **Information/probability:** one fixed \(u\) is used across all times and samples. It is not a sample-dependent hindsight optimizer, and the definition is not \(\mathbb E\inf_u\sum_t(u-Y_t)^2\).
7. **Boundary:** no minimizer is asserted by this definition; the feasible set is a continuum, not a finite candidate set. At \(T=0\) the image is \(\{0\}\), so the value is zero. Integrals remain totalized outside integrability hypotheses.

## C1

In words, the supplied prediction sequence's expected cumulative squared loss minus the fixed-comparator benchmark C0 is a signed real excess.
\[
\forall\Omega\ [\text{measurable space}],\ \mu,Y,P,T,\qquad
C1(\mu,Y,P,T)=A_T(P)-C0(\mu,Y,T),
\quad Y,P:\mathbb N\to\Omega\to\mathbb R,\ T\in\mathbb N.
\]

1. **Objects:** a measure and two arbitrary real-function sequences, with natural horizon.
2. **Quantifiers:** arguments occur in order \(\Omega\), measurable structure, \(\mu,Y,P,T\); no policy is implicitly quantified.
3. **Assumptions:** no probability, integrability, feasibility, causality or independence premise.
4. **Conclusion/operation:** expected cumulative prediction loss minus C0, in that order.
5. **Constants/normalization:** squared loss, range \(0,\ldots,T-1\); no division by \(T\).
6. **Information/probability:** prediction is supplied, not generated by this definition. It can depend on current or future outcomes unless another proposition restricts it.
7. **Boundary:** zero at \(T=0\); nonnegativity is not part of the definition. The signed subtraction is not an absolute value or positive part.

## C2

In words, C2 is the arithmetic mean of the first \(T\) entries of a deterministic real sequence, with totalized division.
\[
\forall y:\mathbb N\to\mathbb R\ \forall T\in\mathbb N,\qquad
C2(y,T)=\frac{\sum_{t<T}y_t}{T}.
\]

1. **Objects:** a real sequence and natural prefix length.
2. **Quantifiers:** definition arguments are \(y\), then \(T\); all values are permitted.
3. **Assumptions:** no feasibility, probability or positive-horizon premise.
4. **Conclusion/operation:** prefix sum divided by the real coercion of \(T\).
5. **Constants/normalization:** denominator exactly \(T\), not \(T+1\); includes index zero and excludes index \(T\).
6. **Information/probability:** depends only on indices strictly below \(T\); no measure is involved.
7. **Boundary:** at \(T=0\), empty sum and total division give C2 = 0. Arbitrary real inputs do not imply a feasible mean.

## C3

In words, C3 predicts one half initially, and thereafter the empirical mean of the strict past.
\[
\forall y:\mathbb N\to\mathbb R\ \forall t\in\mathbb N,\qquad
C3(y,t)=\begin{cases}1/2&t=0,\\ t^{-1}\sum_{i<t}y_i&t>0.\end{cases}
\]

1. **Objects:** real sequence and prediction index.
2. **Quantifiers:** arguments \(y,t\) are unrestricted; the branch condition is exactly \(t=0\).
3. **Assumptions:** no stochastic or boundedness premise.
4. **Conclusion/operation:** explicit predictor defined by a branch and C2, rather than a supplied arbitrary prediction trace.
5. **Constants/normalization:** fixed initial \(1/2\); later denominator is the current index \(t\).
6. **Information/probability:** even though the whole sequence is an argument, the value at \(t\) reads only \(i<t\). The distribution mean is not an input.
7. **Boundary:** C3 at zero differs from C2 at zero; no output bound is imposed for unbounded input histories. At \(t=1\), output equals \(y_0\).

## Q001

For every common-law bounded measurable outcome sequence on any probability space, every horizon and every real fixed comparator, expected cumulative squared loss decomposes into variance and squared distance from the mean:
\[
\forall\Omega,\mu,Y\quad S(\Omega,\mu,Y)\Longrightarrow
\forall T\in\mathbb N\ \forall u\in\mathbb R,\quad
J_T(u)=T v+T(u-m)^2.
\]

1. **Objects:** arbitrary-universe probability space, outcome sequence, fixed comparator and horizon.
2. **Quantifiers:** space/measure/probability instance, \(Y\), measurability, same-law and a.s.-bound proofs, then \(T,u\), matching the displayed universal closure.
3. **Assumptions:** exactly S; no independence or restriction \(u\in I\).
4. **Conclusion:** the displayed equality of expected loss and the two real terms.
5. **Constants/normalization:** variance of \(Y_0\), mean of \(Y_0\), real factor \(T\), unnormalized finite sum.
6. **Information/probability:** fixed \(u\) across samples and times; this identity requires no online policy.
7. **Boundary:** all natural \(T\), including zero; arbitrary real comparator. No optimization or uniqueness conclusion is asserted here.

## Q002

The common distribution mean is feasible, and \(Tv\) is an attained least value in the set of fixed feasible comparators' expected losses:
\[
\forall\Omega,\mu,Y\quad S(\Omega,\mu,Y)\Longrightarrow\forall T\in\mathbb N,
\quad m\in I\ \land\ \operatorname{IsLeast}(\{J_T(u):u\in I\},Tv).
\]
Equivalently the second conjunct says \(\exists u\in I:J_T(u)=Tv\) and \(\forall u\in I:Tv\le J_T(u)\).

1. **Objects:** probability space, common-law outcome family, mean and expected-loss image set.
2. **Quantifiers:** space/measure/probability instance, \(Y\), all S assumptions, then every \(T\); image-set comparator quantifiers are within the conclusion.
3. **Assumptions:** S only; no independence.
4. **Conclusion:** mean feasibility and IsLeast, including both membership/attainment and lower-bound components. The explicit IsLeast witness is a value, not an asserted unique comparator.
5. **Constants/normalization:** least value exactly \(T\operatorname{Var}(Y_0)\), feasible interval \([0,1]\).
6. **Information/probability:** minimization is outside expectation over deterministic constant comparators; no pathwise hindsight minimum.
7. **Boundary:** \(T=0\) has all feasible comparators tied at zero. The proposition does not assert uniqueness, even when additional reasoning could establish it at positive horizons.

## Q003

For every common-law bounded measurable outcome sequence, C0 equals horizon times the common variance:
\[
\forall\Omega,\mu,Y\quad S(\Omega,\mu,Y)\Longrightarrow\forall T\in\mathbb N,
\qquad C0(\mu,Y,T)=Tv.
\]

1. **Objects:** probability space, sequence and the C0 real infimum.
2. **Quantifiers:** space, measure/probability instance, sequence, S assumptions, then all natural horizons.
3. **Assumptions:** precisely S; independence is absent.
4. **Conclusion:** equality of the outside-integral fixed-comparator infimum and \(Tv\).
5. **Constants/normalization:** no normalization; variance and mean-related comparator are tied to \(Y_0\), not a horizon-dependent reference law.
6. **Information/probability:** expectation is taken before optimizing a fixed comparator; no learner or revealed information is specified.
7. **Boundary:** zero horizon gives zero. This value equality alone is not a uniqueness claim or a pathwise identity.

## Q004

For any supplied prediction sequence that is square-integrable at every time and independent of its contemporaneous outcome, subtracting \(Tv\) from its expected cumulative loss leaves the sum of its expected squared distances from \(m\):
\[
\forall\Omega,\mu,Y\quad S(\Omega,\mu,Y)\Longrightarrow
\forall P:\mathbb N\to\Omega\to\mathbb R,
\bigl[(\forall t,\ P_t\in L^2(\mu))\land(\forall t,\ P_t\perp_\mu Y_t)\bigr]
\Longrightarrow\forall T\in\mathbb N,
\quad A_T(P)-Tv=\sum_{t<T}\mathbb E_\mu(P_t-m)^2.
\]

1. **Objects:** arbitrary supplied random real predictions and common-law outcomes on the same probability space.
2. **Quantifiers:** S binders first, then \(P\), then every-time `MemLp ... 2 μ` and every-time `IndepFun` premises, then \(T\).
3. **Assumptions:** S, square-integrability (Lean MemLp includes a.e. strong measurability) and separate independence for each pair \((P_t,Y_t)\). Pointwise measurability of P is not an additional explicit premise.
4. **Conclusion:** exact bias-square-sum identity displayed above; it uses \(Tv\) directly on the left.
5. **Constants/normalization:** exponent 2, range \(t<T\), reference mean \(m\), no division.
6. **Information/probability:** this consumes supplied contemporaneous independence; it does not construct a causal algorithm. Outcomes need not themselves form an independent family, nor must predictions be mutually independent.
7. **Boundary:** \(T=0\) yields zero. Predictions need not lie in \(I\). No explicit random-seed independence or history representation is supplied.

## Q005

For every independent common-law bounded outcome family and every measurable policy feasible on feasible strict histories, the actual policy path has excess equal to a sum of mean squared deviations and hence nonnegative excess:
\[
\forall\Omega,\mu,Y\quad S(\Omega,\mu,Y)\Longrightarrow D(Y)\Longrightarrow
\forall\pi\quad H(\pi)\Longrightarrow\forall T\in\mathbb N,
\quad C1(\mu,Y,P^\pi,T)=\sum_{t<T}\mathbb E_\mu(P^\pi_t-m)^2
\ \land\ 0\le C1(\mu,Y,P^\pi,T).
\]

1. **Objects:** independent family of outcome functions, time-indexed finite-product policy, its actual strict-past prediction path and C1.
2. **Quantifiers:** S binders, whole-family independence, then policy, measurability for every time, conditional feasibility for every time and tuple, then arbitrary horizon.
3. **Assumptions:** exactly S, D and H. In H the antecedent \(\forall i\in I_t,z_i\in I\) is essential; arbitrary real tuples outside the feasible cube carry no output-feasibility requirement.
4. **Conclusion:** both the equality and nonnegativity for the same actual path \(P^\pi\), not a substitute sequence.
5. **Constants/normalization:** finite range \(t<T\), squared deviations from population mean, no averaging by \(T\).
6. **Information/probability:** each call receives only \((Y_i)_{i<t}\); its actual feasibility is a.s. because outcome support is a.s. Input-tuple conditional feasibility is pointwise. There is no separately assumed MemLp or independent-prediction premise here, and no direct seed/current-outcome input.
7. **Boundary:** \(T=0\) gives zero excess and an empty sum. Empty-history output lies in I but is not fixed at one half. Measurability still applies to the entire real input space; a positive-time off-cube output can be arbitrary without violating H.

## Q006

For independent common-law bounded outcomes, the explicit predictor with first output one half and subsequent strict-past empirical means obeys the same squared-deviation equality and nonnegativity:
\[
\forall\Omega,\mu,Y\quad S(\Omega,\mu,Y)\Longrightarrow D(Y)\Longrightarrow
\forall T\in\mathbb N,\quad
C1(\mu,Y,P^*,T)=\sum_{t<T}\mathbb E_\mu(P^*_t-m)^2
\ \land\ 0\le C1(\mu,Y,P^*,T),
\quad P^*_0=1/2,\quad P^*_t=t^{-1}\sum_{i<t}Y_i\ (t>0).
\]

1. **Objects:** independent outcome family and the actual C3-generated prediction sequence.
2. **Quantifiers:** S binders, independence, then arbitrary \(T\); no arbitrary policy or supplied P is quantified.
3. **Assumptions:** S and D only; no separate policy feasibility, integrability or prediction-independence assumption.
4. **Conclusion:** conjunction of exact equality and nonnegative C1 for this specified predictor.
5. **Constants/normalization:** initial one half, denominator \(t\) for positive prediction times, sum over \(t<T\), reference \(m\).
6. **Information/probability:** actual outputs read only the strict past. The empirical mean uses realized outcomes; it is not the distribution mean. Boundedness applies almost surely on the actual path, not to C3 on every arbitrary real sequence.
7. **Boundary:** \(T=0\) has no played predictions; \(T=1\) uses only initial one half. No convergence rate or upper regret bound is asserted.

## Q007

The constant oracle predictor equal to the distribution mean is feasible and has zero excess against C0 at every horizon:
\[
\forall\Omega,\mu,Y\quad S(\Omega,\mu,Y)\Longrightarrow\forall T\in\mathbb N,
\qquad m\in I\ \land\ C1(\mu,Y,(t,\omega)\mapsto m,T)=0.
\]

1. **Objects:** common-law outcomes, their population mean and the constant prediction trace.
2. **Quantifiers:** S binders then every natural \(T\); predictor is explicitly fixed by the preceding \(\mu,Y\), not existentially chosen after observing samples.
3. **Assumptions:** S only; no whole-family independence premise.
4. **Conclusion:** conjunction of mean feasibility and exactly zero signed excess.
5. **Constants/normalization:** predictor is \(\int Y_0\,d\mu\) at every time and sample; excess is unnormalized.
6. **Information/probability:** this is a distribution-dependent oracle identity. It does not claim a learner can know m from finite data under an unknown law.
7. **Boundary:** covers \(T=0\) and degenerate distributions; no uniqueness, estimation rate or implementation assertion.

## Q008

For a measurable conditionally feasible strict-history policy under independent common-law bounded outcomes, at every positive horizon the average expected squared loss minus variance equals average C1:
\[
\forall\Omega,\mu,Y\quad S(\Omega,\mu,Y)\Longrightarrow D(Y)\Longrightarrow
\forall\pi\quad H(\pi)\Longrightarrow
\forall T\in\mathbb N,\quad 0<T\Longrightarrow
\frac{A_T(P^\pi)}{T}-v=\frac{C1(\mu,Y,P^\pi,T)}{T}.
\]

1. **Objects:** same actual finite strict-history policy path, its expected loss, benchmark excess and variance.
2. **Quantifiers:** S binders, independence, policy, all-time measurability and conditional feasibility, then T and its strict positivity premise.
3. **Assumptions:** S, D, H and \(T>0\). The policy bound is only \([\forall i<t,z_i\in I]\Rightarrow\pi_t(z)\in I\); no global output bound on infeasible tuples.
4. **Conclusion:** the exact normalization identity; variance is subtracted after dividing the cumulative loss by T.
5. **Constants/normalization:** denominator is real \(T\) on both sides, no \(T+1\), and the variance term has coefficient one.
6. **Information/probability:** same path on both sides, with strict-past input order as in Q005. A.s. outcome support and pointwise conditional policy feasibility are distinct premises. This is an expectation identity, not a realized-path assertion.
7. **Boundary:** T0 is excluded: under totalized division the right side would be zero and the left would be \(-v\), which need not be zero. No asymptotic limit, sublinearity, uniqueness or unknown-law oracle access is claimed.

## Ambiguities and scope

No blocking ambiguity was found in these neutral expressions. The four definitions and eight closed proposition types have distinct roles; supplying a proposition as a Lean definition is not supplying its proof. In particular, the conditional history-cube feasibility in Q005/Q008 must not be strengthened into an all-real-tuples output bound. C0's image is generally an infinite feasible continuum and its infimum is outside integration; Q002 separately asserts an attained least value. Same-law, family independence and supplied contemporaneous independence remain separate hypotheses. This report makes no source, proof or acceptance assessment.
