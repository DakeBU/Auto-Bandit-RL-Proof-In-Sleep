# Neutral reconstruction

Actor `/root/osd_blind`; requested GPT-6 Astra / medium, without independent runtime model or effort attestation. This reused automated actor has prior staged project and neutral-decoder history. No absolute blindness, human review or external independence is claimed. Only the designated current packet, manifest and neutral context were read. These are complete definitions and closed proposition types, not supplied proofs of the targets. This reconstruction makes no source-fidelity or proof-acceptance assessment.

## Notation and exact common premises

Let \(I=[0,1]\), \(I_t=\{i\in\mathbb N:i<t\}\), \(m=\int Y_0\,d\mu\), \(v=\operatorname{Var}_\mu(Y_0)\), and
\[
A_T(P)=\int\sum_{t<T}(P_t(\omega)-Y_t(\omega))^2\,d\mu(\omega),\quad
D_T(P)=\sum_{t<T}\int(P_t(\omega)-m)^2\,d\mu(\omega).
\]
The abbreviation \(B(\Omega,\mu,Y)\) means: an arbitrary-universe type Ω equipped with a measurable space, a probability measure μ, real outcome maps \(Y:\mathbb N\to\Omega\to\mathbb R\), and for every natural t, measurability of Yt, identical distribution of Yt and Y0 under μ, and \(Y_t\in I\) μ-almost surely. These assumptions cover all times, not only a chosen prefix. B does not include independence. Write \(D(Y)\) for the separate whole-family premise `iIndepFun Y μ`.

For real sequences, \(f=o(T)\) means little-o at `atTop` of the real-coerced natural sequence T: for every ε>0, eventually \(|f(T)|\le\varepsilon|T|\). It is a two-sided magnitude condition, not just an eventual upper bound. Limits below are ordinary real limits along natural horizons to infinity; the target is the neighborhood filter of 0. All displayed universal closures expand the common premises as stated here and the binder order listed in each item.

## C0

In words, C0 takes the expected cumulative squared loss of each fixed feasible real comparator, then takes the real infimum of those expected values:
\[
\forall\Omega\ [\text{measurable space}],\mu:\operatorname{Measure}(\Omega),Y:\mathbb N\to\Omega\to\mathbb R,T\in\mathbb N,
\quad C0(\mu,Y,T)=\inf\left\{\int\sum_{t<T}(u-Y_t)^2\,d\mu:u\in[0,1]\right\}.
\]

1. **Objects:** arbitrary measurable space, measure, real outcome sequence, natural horizon, fixed feasible real comparator.
2. **Quantifiers:** definition arguments are Ω/structure, μ, Y, T; u is scoped inside the image of I used by `sInf`.
3. **Assumptions:** no probability, measurability of Y, integrability, support or independence premise in the definition.
4. **Operation:** infimum of the actual real image of I under expected finite loss. The integral occurs inside the comparator optimization.
5. **Constants/normalization:** [0,1], exponent 2, indices 0 through T-1; no division by T.
6. **Information/probability:** one u is fixed across samples and time. This is not expectation of a pathwise hindsight minimum and does not exchange infimum with integration.
7. **Boundary:** at T0 the empty loss sum gives C0=0. The feasible continuum is not a finite candidate set, and the definition asserts no attainment or unique minimizer. Real integration and `sInf` are totalized operations, not integrability certificates.

## C1

In words, C1 is the supplied prediction sequence's expected finite cumulative loss minus C0:
\[
\forall\Omega\ [\text{measurable space}],\mu,Y,P,T,\quad
C1(\mu,Y,P,T)=A_T(P)-C0(\mu,Y,T),
\qquad Y,P:\mathbb N\to\Omega\to\mathbb R,\ T\in\mathbb N.
\]

1. **Objects:** measure, outcome and prediction maps, horizon and signed real excess.
2. **Quantifiers:** Ω/structure, μ, Y, prediction P, then T are its arguments.
3. **Assumptions:** no causality, measurability, integrability, independence or feasibility requirement in the definition itself.
4. **Operation:** expected prediction loss minus the fixed-comparator infimum, with this subtraction order.
5. **Constants/normalization:** squared loss, t<T, no averaging or absolute value or positive part.
6. **Information/probability:** P is merely supplied here; C1 does not produce an algorithm or restrict access to the current outcome.
7. **Boundary:** C1 at T0 is zero. Nonnegativity is not automatic for arbitrary P and is asserted later only under suitable premises.

## C2

In words, C2 predicts one half initially and thereafter predicts the empirical average of all strictly earlier entries:
\[
\forall y:\mathbb N\to\mathbb R\ \forall t\in\mathbb N,\quad
C2(y,t)=\begin{cases}1/2,&t=0,\\ \displaystyle\frac{\sum_{i<t}y_i}{t},&t>0.\end{cases}
\]

1. **Objects:** real sequence y and natural prediction time t.
2. **Quantifiers:** arbitrary y then arbitrary t; branch test is exactly t=0.
3. **Assumptions:** no outcome range, probability or independence restriction in this definition.
4. **Operation:** an explicit prediction rule, not an arbitrary trace: constant initial output, then strict-prefix arithmetic mean.
5. **Constants/normalization:** initial 1/2; later denominator is real t, not t+1; indices i<t include zero and exclude current time.
6. **Information/probability:** despite its whole-sequence argument, the value at t uses only the strict past. It does not need the population mean or a random seed.
7. **Boundary:** the branch avoids using an empty average as the first prediction; C2(y,0)=1/2. No feasibility guarantee for arbitrary unbounded real histories is part of the definition.

## Q001

For every arbitrary real sequence `total` and every fixed real constant c, the residual total(T)-Tc is little-o of T exactly when normalized total(T) minus c tends to zero:
\[
\forall a:\mathbb N\to\mathbb R\ \forall c\in\mathbb R,\qquad
\bigl(T\mapsto a_T-Tc\bigr)=o(T)
\quad\Longleftrightarrow\quad
\lim_{T\to\infty}\left(\frac{a_T}{T}-c\right)=0.
\]

1. **Objects:** arbitrary real total sequence, fixed real c, natural horizon and real asymptotic filters.
2. **Quantifiers:** a then c, followed by a biconditional; both asymptotic statements quantify only over the varying natural T.
3. **Assumptions:** none beyond types; no nonnegativity, monotonicity, probabilistic structure or a0=0 premise.
4. **Conclusion:** equivalence of two convergence conditions. It does not independently assert either condition holds.
5. **Constants/normalization:** exact residual aT-Tc, denominator real T, limit zero, no tuning or T-dependent c.
6. **Information/probability:** a deterministic sequence identity with no learner or distribution. Little-o controls absolute magnitude, not one-sided upper behavior.
7. **Boundary:** Lean real division at zero is totalized: a0/0-c=-c. The residual at zero is a0. These finite initial values do not affect atTop statements; the claim is not a pointwise residual/quotient identity at T0.

## Q002

For every measurable seed-history policy with feasible outputs on all seeds and feasible histories, under independent common-law bounded outcomes and a seed independent of the entire outcome vector, excess is nonnegative at every horizon. Moreover, sublinear excess, average expected loss tending to the common variance, and average squared deviation from the population mean tending to zero satisfy the two stated equivalences. The contract does not assert any of those limiting properties for every such policy.

Formally, universally quantify B, then \(D(Y)\), an arbitrary measurable seed type Seed, and a measurable \(S:\Omega\to\mathrm{Seed}\) satisfying
\(S\perp_\mu(\omega\mapsto(Y_t(\omega))_{t\in\mathbb N})\), and a policy
\[
\pi_t:\mathrm{Seed}\times\mathbb R^{I_t}\to\mathbb R,\quad
\forall t,\ \pi_t\text{ measurable},\quad
\forall t,s,z,\quad [\forall i\in I_t,z_i\in I]\Longrightarrow\pi_t(s,z)\in I.
\]
With the single actual path \(P_t(\omega)=\pi_t(S(\omega),(Y_i(\omega))_{i<t})\) and \(R_T=C1(\mu,Y,P,T)\), the conclusion is exactly
\[
\left(\forall T\in\mathbb N,\ 0\le R_T\right)
\ \land\ \left(R=o(T)\ \Longleftrightarrow\ \lim_{T\to\infty}(A_T(P)/T-v)=0\right)
\ \land\ \left(\lim_{T\to\infty}(A_T(P)/T-v)=0\ \Longleftrightarrow\ \lim_{T\to\infty}D_T(P)/T=0\right).
\]

1. **Objects:** arbitrary-universe Ω and Seed with measurable structures; probability μ; independent outcome family; seed; time-indexed policy on seed times finite real-history product; its actual path, C1 and two normalized real sequences.
2. **Quantifiers:** exact binder order is Ω, Seed and structures, μ/probability, Y, all-time measurability, same-law and a.s. support, family independence, S/measurability/whole-vector independence, policy/measurability/conditional feasibility. Prediction is then a let-defined composition. The all-T lower bound and limits occur inside the resulting conclusion, not as additional premises.
3. **Assumptions:** B and whole-family independence; seed independent of the entire target vector, not just pairwise independent of each target; policy measurable on the full input domain. Its bound applies to every seed and every history all of whose coordinates are in I. Infeasible histories have no output bound. Outcome support is a.s., not pointwise.
4. **Conclusion:** conjunction of one universal finite-horizon nonnegativity statement and two biconditionals. These are not a conjunction of convergence assertions, and do not produce convergence for an arbitrary policy.
5. **Constants/normalization:** m and v refer to Y0's law; squared loss, strict range t<T, denominator real T in both normalized sequences, little-o relative to real T. No numerical rate constant occurs.
6. **Information/probability:** policy receives seed and exactly finite strict-past outcomes; no current target or other side-information input appears. The whole seed is allowed from the beginning. All integrals average the randomness already in μ. The comparator in C0 remains fixed outside integration; no hindsight optimization interchange is made.
7. **Boundary:** at T0, R0=A0=D0=0. Totalized A0/0-v=-v whereas D0/0=0, so these sequences need not agree at zero, despite the stated equivalence of their limits. At t0 the empty-history condition is vacuous and the policy must be feasible for every seed, but may vary with seed; no initial 1/2 requirement. No kernel representation or unknown-law learning rate is claimed.

## Q003

For every common-law measurable outcome family supported in I almost surely, the explicit initial-half, empirical-past-mean predictor has excess at every positive horizon bounded above by 4+4 log T. Independence is not an assumption of this proposition:
\[
\forall\Omega,\mu,Y,\quad B(\Omega,\mu,Y)\Longrightarrow
\forall T\in\mathbb N,\quad 0<T\Longrightarrow
C1(\mu,Y,P^*,T)\le 4+4\log T,
\qquad P^*_t(\omega)=C2(i\mapsto Y_i(\omega),t).
\]

1. **Objects:** arbitrary-universe measurable probability space, common-law outcome sequence and the explicitly defined C2 prediction path.
2. **Quantifiers:** Ω/structure, μ/probability, Y, all-time measurability, same-law and a.s. bounds, then T and the proof T>0.
3. **Assumptions:** exactly B and positive T. There is no `iIndepFun`, no seed and no arbitrary-policy premise; dependent common-law outcomes are within this stated scope.
4. **Conclusion:** a one-sided finite upper bound on the signed C1 of the actual P*. This is not a lower bound, absolute bound or by itself a two-sided convergence assertion.
5. **Constants/normalization:** exactly 4+4 times the natural real logarithm of real-coerced T; unnormalized cumulative excess, no log(T+1). Predictor has first output 1/2 and subsequent denominator t.
6. **Information/probability:** P* reads only strict-past observations, without the population mean. C1 uses expected losses and a fixed-comparator benchmark outside integration; no seed averaging or policy optimization is present.
7. **Boundary:** T0 is excluded even though the involved Lean operations are total. At T1 the displayed bound is 4. Zero excess at T0 from the definitions is separate from the positive-horizon contract. Without the additional independence premise, this statement alone does not give nonnegative excess.

## Q004

For independent common-law a.s. bounded outcomes, the same explicit predictor has normalized excess tending to zero and its unnormalized excess is little-o of the horizon:
\[
\forall\Omega,\mu,Y,\quad B(\Omega,\mu,Y)\Longrightarrow D(Y)\Longrightarrow
\left[\lim_{T\to\infty}\frac{C1(\mu,Y,P^*,T)}{T}=0\right]
\ \land\ \left[(T\mapsto C1(\mu,Y,P^*,T))=o(T)\right],
\quad P^*_t(\omega)=C2(i\mapsto Y_i(\omega),t).
\]

1. **Objects:** arbitrary-universe probability space, independent common-law outcome family, explicit C2 predictor and its expected signed excess sequence.
2. **Quantifiers:** Ω/structure, μ/probability, Y, all-time measurability, same-law, a.s. support, family independence; varying T is bound within each asymptotic function. There is no external fixed T argument or T>0 assumption.
3. **Assumptions:** B plus `iIndepFun Y μ`; unlike Q003 independence is explicitly present. No arbitrary policy, seed or oracle mean access is assumed.
4. **Conclusion:** conjunction of actual zero-limit and actual little-o assertions for the specified predictor, not merely an equivalence. This describes the target proposition; the supplied `def ... : Prop` is still not its proof.
5. **Constants/normalization:** real T denominator and little-o comparison sequence, ordinary limit to zero. No additional explicit rate constant appears in this proposition.
6. **Information/probability:** same actual initial-half empirical-mean path in both conjuncts. Convergence concerns expected excess, a deterministic sequence of real integrals, not samplewise regret or almost-sure convergence of predictions.
7. **Boundary:** normalized value at T0 is 0/0=0 under totalized division and does not affect the limit. Initial prediction remains 1/2. No independent claim about convergence for all randomized policies, samplewise rates, or uniqueness of a comparator is included.

## Ambiguity and scope record

No blocking ambiguity was found in the specified neutral expressions. Q001 and the asymptotic parts of Q002 assert equivalences; Q004's target is a conjunction of convergence properties for a specific predictor. Q003 is only an upper bound and has no independence assumption, while Q004 does. All target claims remain contract proposition definitions rather than supplied proofs. No source, proof or acceptance verdict is made.
