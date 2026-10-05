# Restricted current-packet reconstruction: N01–N12

This pass read only `blind-packet-v1.md` in this run directory as mathematical file input. No source, numbered original-name map, import body, proof, prior verdict, or other file was read. This is a restricted current-packet reconstruction, not fresh-history blinding: previous unrelated actor history is not erased. The distinct automated decoder is `/root/normal_blind`, requested GPT-6 Astra / medium, without runtime-model attestation or human/external-model review. No compilation, source acceptance, proof validation, chapter certification, or Goal certification is claimed.

Independent exact raw-byte packet SHA-256:
`8dd65e42c2e140fe37ae6fcda1671d3a7cfce50ab8168f8630e9a87ff768c8c4`.

N01–N09 are presented as retained statement headers. N10–N12 are planned exact type expressions: this report treats them only as proposed propositions, not as existing proved bodies, compiled public declarations, or accepted results. The neutral theorem syntax does not change that distinction.

## Supplied notation, not independently inspected definitions

The packet supplies the interpretation of Domain, project, RegularLoss, gradient, step, iterate, regret, empiricalMean and meanPredict. Their original bodies were not inspected. The following reconstruction uses exactly that supplied interpretation.

All algorithmic points here are real numbers. The domain is I=[0,1], a nonempty closed convex subset of the real Hilbert space. P_I is the actual nearest-point choice, not an arbitrary externally supplied clamp function. For scalar η and label y, define S_η^y(x)=P_I(x−η∇[(·−y)²](x)). A fixed-step run for label sequence y and initialization a is

\[
x_0=a,\qquad x_{t+1}=S_\eta^{y_t}(x_t),\qquad
R_T(\eta,y,a;u)=\sum_{t=0}^{T-1}[(x_t-y_t)^2-(u-y_t)^2].
\]

RegularLoss(I,f) requires an open U containing I on which f is convex and differentiable. The gradient is the actual ambient real-Hilbert Fréchet gradient. It is not a supplied arbitrary oracle. Mean prediction is

\[
m_t(y)=\begin{cases}1/2,&t=0,\\ t^{-1}\sum_{i=0}^{t-1}y_i,&t>0.\end{cases}
\]

The supplied empiricalMean formula at t=0 uses total real division, but meanPredict chooses its separate 1/2 branch there. All real division in this packet is total, with zero inverse zero.

Both procedures predict at t before using current label y_t. The projected update uses y_t only to produce x_{t+1}; m_t uses a strict prefix. No stochastic law, expectation, filtration, randomness, independence, or loss-adaptive adversary is assumed. A horizon-tuned scalar step may depend on T before the run; this is not an anytime schedule independent of the horizon.

For the recurring lower example let y_t=0 for every t, T_n=(2n)² as a natural number, η_n=1/(2√(T_n)), and R_n=R_{T_n}(η_n,0,1;0). The original initialization is exactly 1 and the comparator exactly 0. Write B_n=Σ_{t<T_n}m_t(0)². Since the comparator's squared loss is zero, R_n is also the actual cumulative squared loss of that particular projected-gradient run. This identity of objectives does not imply that the two predictors share an initialization: the mean predictor starts at 1/2.

## N01 — projection formula (retained header)

1. **Objects/spaces:** Real input z and actual nearest-point projection onto I=[0,1].
2. **Quantifiers:** Every z∈ℝ.
3. **Assumptions:** None on z beyond being real.
4. **Conclusion/metric:** P_I(z)=min(max(z,0),1).
5. **Constants/indexing:** Closed endpoints 0 and 1, max before min; exact equality.
6. **Information/probability:** Deterministic geometric identification of the chosen projection.
7. **Boundary:** Includes z<0, z=0, 0<z<1, z=1, and z>1. This identifies the genuine projection with clipping rather than assuming a freely specified clipping routine.

## N02 — square-loss regularity (retained header)

1. **Objects/spaces:** Real parameter y and function f_y(x)=(x−y)² on ℝ, domain I.
2. **Quantifiers:** Every y∈ℝ.
3. **Assumptions:** No y∈I condition.
4. **Conclusion/metric:** RegularLoss(I,f_y): some open U⊇I has ConvexOn ℝ U f_y and DifferentiableOn ℝ f_y U.
5. **Constants/indexing:** Square without a 1/2 normalization.
6. **Information/probability:** Deterministic function regularity, not a probability or trajectory claim.
7. **Boundary:** Labels outside I are included. No bounded-gradient conclusion follows from this header alone; regularity is the supplied neighborhood notion, not merely differentiability within the closed interval.

## N03 — exact gradient (retained header)

1. **Objects/spaces:** Real y,x and ambient gradient of f_y.
2. **Quantifiers:** Every real y and every real x.
3. **Assumptions:** None on interval membership or sign.
4. **Conclusion/metric:** ∇f_y(x)=2(x−y).
5. **Constants/indexing:** Factor exactly 2 because the loss is (x−y)², not half the square.
6. **Information/probability:** Deterministic derivative identity.
7. **Boundary:** Includes x=y, where gradient is zero, and inputs outside I. No abstract support selection replaces the derivative.

## N04 — feasible gradient bound (retained header)

1. **Objects/spaces:** Label y and action x in I, with the real norm of ∇f_y(x).
2. **Quantifiers:** Every pair x,y satisfying the membership assumptions.
3. **Assumptions:** 0≤y≤1 and 0≤x≤1.
4. **Conclusion/metric:** ‖∇f_y(x)‖≤2, equivalently |2(x−y)|≤2.
5. **Constants/indexing:** Bound exactly 2, non-strict.
6. **Information/probability:** Deterministic pointwise bound on feasible pairs.
7. **Boundary:** Endpoints included and equality permitted. Both membership assumptions matter; no such uniform bound for unrestricted x or y is stated.

## N05 — one projected step (retained header)

1. **Objects/spaces:** Arbitrary real step η,label y,current point x and projected update on I.
2. **Quantifiers:** Every η,y,x∈ℝ.
3. **Assumptions:** No η>0, x∈I, or y∈I premise.
4. **Conclusion/metric:**
   \[S_\eta^y(x)=\min(\max(x-2\eta(x-y),0),1).\]
5. **Constants/indexing:** Exact factor 2 multiplying η(x−y), with clipping after the unconstrained update.
6. **Information/probability:** Deterministic current-loss update. In the defined trajectory this produces the next prediction, not the already played one.
7. **Boundary:** Includes η=0 and η<0; at η=0 the result is P_I(x), which equals x only when x∈I. Labels and current points outside I remain within this identity's scope.

## N06 — uniform comparator bound at a tuned horizon (retained header)

1. **Objects/spaces:** Label sequence y:ℕ→ℝ, feasible initialization a, positive horizon T, step η*=1/(2√T), and its actual projected-square-loss run.
2. **Quantifiers:** Every y,a,T satisfying the premises; then for every comparator u∈I the bound holds on the same fixed run.
3. **Assumptions:** a∈I, T>0, and y_t∈I for every t<T. No condition on labels at t≥T.
4. **Conclusion/metric:**
   \[\forall u\in I,\quad R_T(1/(2\sqrt T),y,a;u)\le2\sqrt T.\]
5. **Constants/indexing:** Exact step denominator 2√T and bound coefficient 2. T is coerced to ℝ under square root; regret uses t=0,…,T−1.
6. **Information/probability:** Deterministic bound for all feasible comparators, not expected regret. The step is horizon dependent; no requirement on a stochastic label process or independence.
7. **Boundary:** T=0 excluded. Arbitrary feasible initialization allowed here. No claim that one unchanged run with horizon-independent steps meets this formula at every T; no assertion of a minimizing comparator or a lower bound.

## N07 — explicit zero-label trajectory (retained header)

1. **Objects/spaces:** Positive natural n, constant step 1/(4n), all-zero labels, initialization 1, and iterate at arbitrary natural t.
2. **Quantifiers:** Every n>0 and every t∈ℕ.
3. **Assumptions:** n positive; no finite-horizon restriction on t.
4. **Conclusion/metric:**
   \[x_t=\left(1-\frac1{2n}\right)^t.\]
5. **Constants/indexing:** Denominator 4n in the step and 2n in the contraction; natural exponent t, and n is cast to ℝ in arithmetic.
6. **Information/probability:** Deterministic exact trajectory of the defined projected procedure, not an approximation or independent test sequence. Labels are fixed zero from the start.
7. **Boundary:** t=0 is included, giving x₀=1. n=0 excluded. This does not describe every initialization or all algorithms; the formula is for initialization exactly 1.

## N08 — tuning identity including zero (retained header)

1. **Objects/spaces:** Natural n and two real scalar step expressions.
2. **Quantifiers:** Every n∈ℕ, without a positivity hypothesis.
3. **Assumptions:** None beyond n being natural and the supplied total real division convention.
4. **Conclusion/metric:**
   \[\frac1{2\sqrt{((2n)^2: \mathbb N)}}=\frac1{4(n:\mathbb R)},\]
   with the natural square coerced to real before square root.
5. **Constants/indexing:** Exact factor 2 outside square root and 4 on the right; no asymptotic equivalence.
6. **Information/probability:** Deterministic algebraic identity, not a statement about a generated trajectory or its loss.
7. **Boundary:** n=0 is expressly included; both expressions evaluate to zero under total division. This does not make a zero-horizon positive-step guarantee valid or extend N07/N09 beyond their positive-n premises.

## N09 — a specific regret lower bound (retained header)

1. **Objects/spaces:** T_n=(2n)², η_n=1/(2√T_n), zero-label run starting at 1, comparator 0, and R_n.
2. **Quantifiers:** Every natural n>0.
3. **Assumptions:** n>0; all run parameters are fixed as displayed.
4. **Conclusion/metric:** (n:ℝ)/4≤R_n.
5. **Constants/indexing:** Horizon exactly (2n)²; step uses that horizon; lower coefficient exactly 1/4. Comparator loss is zero on every round.
6. **Information/probability:** Deterministic realized lower bound for this run on the single fixed all-zero sequence. No adversarial adaptation or probabilistic averaging.
7. **Boundary:** Not a lower bound for every initialization, every horizon shape, or every prediction algorithm. It gives no exact regret formula. n=0 excluded. In particular initialization 0 would be a different run not covered by this statement.

## N10 — cumulative loss of the mean predictor (planned type expression)

1. **Objects/spaces:** Positive natural horizon T, all-zero label sequence, and the supplied causal mean predictor m_t with initial prediction 1/2.
2. **Quantifiers:** Every T>0 in the proposed proposition.
3. **Assumptions:** T positive. No model or measure assumptions; definitions are the supplied notation.
4. **Conclusion/metric:** Proposed exact equality
   \[\sum_{t=0}^{T-1}m_t(0)^2=\frac14.\]
5. **Constants/indexing:** The first prediction is 1/2, contributing 1/4; subsequent strict-prefix means of zero labels are zero under the supplied definition. The statement is a cumulative squared-loss sum, not an average divided by T.
6. **Information/probability:** Deterministic causal predictor: current label is not used. No actual implementation, proof body, or compilation of this proposed expression is supplied.
7. **Boundary:** T=0 excluded, as its empty sum would be zero rather than 1/4. This does not replace the separate time-zero branch by empiricalMean(0,0). No general-label claim is made.

## N11 — quantitative gap against that mean predictor (planned type expression)

1. **Objects/spaces:** R_n for the zero-label projected-gradient run starting at 1 and B_n for the zero-label mean predictor starting at 1/2, both through T_n rounds.
2. **Quantifiers:** Every n∈ℕ with n>0 in the proposed proposition.
3. **Assumptions:** n>0; all labels, steps, initializations, comparator and horizon are exactly fixed as in the supplied expression.
4. **Conclusion/metric:** Proposed inequality
   \[\frac n4-\frac14\le R_n-B_n.\]
   R_n is the comparator-0 regret, which here equals that run's cumulative loss, while B_n is the other predictor's cumulative loss.
5. **Constants/indexing:** Retains the subtraction 1/4 and the horizon (2n)²; no dropped constant or changed initialization.
6. **Information/probability:** Deterministic performance comparison of two specified causal predictors on the same zero labels, not an expected or randomized gap. The statement is planned and has no supplied new proof body.
7. **Boundary:** At n=1 the displayed lower bound is zero; strictly positive gap is not claimed by this bound for every positive n. Initializations differ and no equal-initialization comparison should be inferred. Not a universal lower bound for all algorithms or all sequences.

## N12 — unbounded gap at arbitrarily large indices (planned type expression)

1. **Objects/spaces:** Arbitrary real threshold C, natural lower index bound N, and the family of gaps R_n−B_n indexed by n.
2. **Quantifiers:**
   \[\forall C\in\mathbb R\ \forall N\in\mathbb N\ \exists n\in\mathbb N:\quad N<n\ \land\ C<R_n-B_n.\]
   The selected n may depend on both C and N and is shared between both strict inequalities.
3. **Assumptions:** No positivity condition on C; N is any natural. There is no separate n>0 premise because the existential conclusion N<n entails positivity for natural N.
4. **Conclusion/metric:** The proposed comparator-0 regret minus mean-predictor cumulative loss exceeds every prescribed real threshold at some index above every prescribed natural cutoff.
5. **Constants/indexing:** Both comparisons are strict. N bounds n, not directly the horizon; the horizon remains T_n=(2n)² and the tuned step changes with n. The threshold is compared to the exact gap, with no normalization by time.
6. **Information/probability:** Deterministic unbounded-tail-existence statement for this family of separately horizon-tuned runs and fixed causal mean predictions. It does not posit a stochastic event, current-label access, or a single horizon-independent run.
7. **Boundary:** Negative or zero C allowed; N=0 allowed. The literal conclusion is “for every cutoff, some later n,” not “for all sufficiently large n,” although other statements might support stronger consequences. No uniform statement about all initializations, every algorithm, arbitrary labels, or every natural horizon is asserted. This remains a planned type expression, not a proved/compiled-public result.

## Reconstruction limits

N01–N09 are reconstructed as retained headers with no proof inspection. N10–N12 are reconstructed only as planned propositions. The supplied notation was not independently checked against original definitions. Causality is interpreted from the packet's strict-prefix prediction and next-step update definitions, with fixed initialization and step; it does not attest how external callers choose those parameters. No source attribution or acceptance conclusion is drawn from the neutral packet.
