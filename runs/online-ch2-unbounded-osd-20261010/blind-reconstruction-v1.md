# Eleven neutral unbounded-domain statements

Actor /root/osd_blind; requested GPT-6 Astra / medium, without independent runtime model or effort attestation. This is a reused automated decoder with related staged history, not absolutely blind, fresh source-naive, human or externally independent. Only the neutral packet and targeted authorized shared API lookup were used. The lookup displayed incidental adjacent declarations/proof lines, which were not used to certify proofs. No source identity or other role verdict was consulted.

## Four exact local definitions

For α∈R and t∈N,
\[
\eta_\alpha(t)=(t+1)^{-\alpha},\qquad
c(\alpha)=\frac1{2-\alpha}
+\frac{(1/2)^{1-\alpha}-1}{1-\alpha}.
\]
Powers here are real powers of positive real bases (the natural t+1 is cast to R). Both are total Lean real expressions: c is defined even at α=1 or 2 using totalized division, but the range theorem excludes those points and the limit below is one-sided/punctured.

For T,t∈N let m=⌊(T+1)/2⌋=⌈T/2⌉ and n=⌊T/2⌋. The sign is σ_T(t)=−1 if t<m, otherwise +1. For a real inner-product space and v,z∈E define q_(T,v,t)(z)=σ_T(t)⟨v,z⟩. The negative block has m rounds and the positive block n rounds within horizon T. At and after t=m the sign is +1, including times beyond the tested horizon. These definitions contain no loss randomness.

## Actual shared API and feedback order

The authorized API gives currentSubgradient(f,x) as Classical.choose of a global supporting-vector witness if SourceSubdifferential f x is nonempty, otherwise zero. Global support compares f(x)+ι⟨g,y−x⟩≤f(y) for every ambient y. This is a specified actual selector, not a quantifier over all policies.

step(V,η,f,x)=project V (x−η currentSubgradient(f,x)).
The actual iterate has X0=x0 and X_(t+1)=step(V,η_t,loss_t,X_t). Regret is
\[
R_T(u)=\sum_{t<T}\bigl[(\mathrm{loss}_t(X_t)).\mathrm{toReal}
-(\mathrm{loss}_t(u)).\mathrm{toReal}\bigr].
\]
The scored point is X_t, BEFORE processing current loss_t. Current feedback determines the next X_(t+1); the update is not itself the scored current prediction. fullSpace is the Domain whose carrier is univ with its nonempty/closed/convex structure. No feasibility restriction or projection constraint beyond the entire E is imposed. All tested losses are finite real affine functions embedded in EReal, so toReal recovers their values. This differs from the earlier retained post-update-scored packets; their interpretation is not imported here.

Define R_(α,T,v) as this actual full-space regret with step schedule ηα, loss_t=ι∘q_(T,v,t), initial point 0 and fixed comparator 0, at horizon T. Dependence of the constructed loss sequence on T is explicit.

## claim1: actual selector on affine losses

For every real inner-product E (NormedAddCommGroup and InnerProductSpace R), a,x∈E and b∈R, the actual selected subgradient of z↦ι(⟨a,z⟩+b) at x is a.
\[
\operatorname{currentSubgradient}(z\mapsto\iota(\langle a,z\rangle+b),x)=a.
\]

1. **Objects:** Actual selector and a finite extended-real affine function.
2. **Quantifiers:** E/structures, then all a,x,b; no completeness or finite dimension.
3. **Assumptions:** None beyond types; no a≠0 or supplied support witness.
4. **Conclusion:** Exact chosen-vector equality, not just membership of a in the support set.
5. **Constants/boundaries:** Arbitrary intercept b and zero vector allowed; zero-dimensional space allowed.
6. **Information:** Selector sees the current function and current point. No temporal or random premise.
7. **Scope:** Auxiliary selector fact; no regret or existence of adverse sequence asserted. It is a header without a proof.

## claim2: actual full-space step

In finite-dimensional real inner-product E, for all η∈R,a,x∈E,b∈R,
\[
\operatorname{step}(\mathrm{fullSpace},\eta,z\mapsto\iota(\langle a,z\rangle+b),x)=x-\eta a.
\]

1. **Objects:** Normed additive real inner-product E with FiniteDimensional R E; actual step.
2. **Quantifiers:** E/structures,η,a,x,b, all universal.
3. **Assumptions:** Finite dimension; no positive-step or nonzero-vector condition.
4. **Conclusion:** Exact unprojected-looking value of the actual full-space step.
5. **Constants/boundaries:** η=0 or negative and a=0 included; no half factor.
6. **Information:** Current affine coefficient affects next state.
7. **Scope:** Auxiliary identity for fullSpace only, not an arbitrary constrained domain or a proof of implementation.

## claim3: closed form for actual affine run

In the same finite-dimensional context, for arbitrary streams η,a,b, initial x0 and natural t,
\[
X_t=x0-\sum_{s<t}\eta_s a_s,\qquad
\mathrm{loss}_s(z)=\iota(\langle a_s,z\rangle+b_s).
\]

1. **Objects:** Actual full-space recursion and entire affine streams.
2. **Quantifiers:** η:N→R,a:N→E,b:N→R,x0,t, after E/structures.
3. **Assumptions:** No sign, norm bound, boundedness or monotonicity.
4. **Conclusion:** Equality to a finite strict-prefix weighted vector sum.
5. **Constants/indices:** range t is 0,…,t−1; t=0 gives X0=x0. Intercepts do not appear on the RHS.
6. **Information:** X_t depends on coefficients/steps before t, not the current a_t. Equality describes this actual selector run.
7. **Scope:** Auxiliary exact identity, not a convergence or regret statement.

## claim4: schedule_pos

For all real α and all natural t, ηα(t)>0.
\[
\forall\alpha\in\mathbb R,\ \forall t\in\mathbb N,\quad(t+1)^{-\alpha}>0.
\]

1. **Objects:** Scalar real-power schedule.
2. **Quantifiers:** α,t arbitrary.
3. **Assumptions:** No 0<α<1 restriction.
4. **Conclusion:** Strict positivity, not merely nonnegativity.
5. **Boundaries:** t=0 gives positive base 1; no zero-base power.
6. **Information:** Deterministic index-only schedule.
7. **Scope:** No monotonicity or summability assertion.

## claim5: payoff regularity

For finite-dimensional real inner-product E, every T,t and unit v satisfy
\[
\operatorname{ConvexOn}_{\mathbb R}(E,q_{T,v,t})
\land \operatorname{LipschitzWith}(1,q_{T,v,t}).
\]

1. **Objects:** Scalar payoff on the full ambient E and unit direction v.
2. **Quantifiers:** T,v,hv:||v||=1,t; all times t, not only t<T.
3. **Assumptions:** Finite dimension and unit norm. No explicit Nontrivial binder, but hv excludes a zero-dimensional realized instance.
4. **Conclusion:** Ambient convexity and global Lipschitz constant at most 1.
5. **Boundaries:** T=0 allowed, giving the positive-sign function for every t. t=m uses +1.
6. **Information:** Losses depend on fixed T,v and time, not learner feedback.
7. **Scope:** Does not assert losses are bounded in value or nonnegative on unbounded E.

## claim6: exact scalar regret

For every α∈R,T∈N, using v=1 on R,
\[
R_{\alpha,T,1}
=-(m-n)\sum_{i<m}\eta_\alpha(i)
+\sum_{i<T}(i+1)^{1-\alpha}
-T\sum_{i=m}^{T-1}\eta_\alpha(i).
\]

1. **Objects:** Actual scalar full-space run, zero initial point/comparator, horizon-dependent sign losses.
2. **Quantifiers:** α,T only; no exponent range assumption.
3. **Assumptions:** None beyond their types.
4. **Conclusion:** Exact signed unnormalized regret identity with all three terms.
5. **Constants/indices:** m=natural (T+1)/2 and n=natural T/2, separately cast to reals before subtraction. m−n is 0 for even T, 1 for odd T. The final range is Ico m T. T=0 makes all sums zero; no division by T.
6. **Information:** Scores X_i before current update. The sequence can vary with the evaluated horizon T.
7. **Scope:** Exact arithmetic/trajectory identity, not yet a positive lower bound.

## claim7: coefficient_range

For 0<α<1,
\[
0<c(\alpha)<1-\log2.
\]

1. **Objects:** The exact coefficient function above and real natural logarithm.
2. **Quantifiers:** α then proofs of α>0 and α<1.
3. **Assumptions:** Strict open interval only.
4. **Conclusion:** Two strict inequalities conjoined.
5. **Boundaries:** α=0 and α=1 excluded; denominators 2−α and 1−α are positive under the premises.
6. **Information:** Scalar auxiliary fact, no run.
7. **Scope:** Does not claim equality to the limiting constant or include endpoints.

## claim8: coefficient_limit

\[
\lim_{\alpha\to1^-}c(\alpha)=1-\log2
\quad\land\quad 3/10\le1-\log2.
\]

1. **Objects:** Real function c and the left-neighborhood filter at 1.
2. **Quantifiers:** Closed conjunction; no free α.
3. **Assumptions:** None.
4. **Conclusion:** One-sided limit from below plus a non-strict numerical lower comparison.
5. **Boundaries:** The approach excludes α=1. The totalized c(1) evaluates to 1, so the statement is not continuity or equality at 1. The numeric bound is 0.3, not an exact value.
6. **Information:** Real-parameter asymptotic, not horizon asymptotic.
7. **Scope:** No two-sided limit, no c(α)≥0.3 for all α, and no uniform rate of approach.

## claim9: scalar lower bound

For 0<α<1 and natural horizon satisfying
\[
\frac{2}{(1-\alpha)c(\alpha)}\le T,
\qquad
\frac12c(\alpha)T^{2-\alpha}\le R_{\alpha,T,1}.
\]

1. **Objects:** Scalar actual run with sign losses, schedule and zero comparator.
2. **Quantifiers:** α,hα0,hα1,T,hT.
3. **Assumptions:** Open exponent range and the displayed real-valued threshold (natural T cast to real).
4. **Conclusion:** Positive coefficient times real-power horizon is a lower bound on signed cumulative regret.
5. **Boundaries:** Under claim7's asserted positive coefficient the threshold is positive; T=0 does not satisfy it. No hidden ceiling is written in hT: it is a real comparison to natural T. Equivalent integer threshold rounding is not substituted into the type.
6. **Information:** Deterministic constructed loss sequence depends on this T; initial and comparator both zero.
7. **Scope:** Not an all-T result, not a lower bound for every loss stream or every learner.

## claim10: unit-direction lower bound

For finite-dimensional real inner-product E, the same exponent/horizon hypotheses and any v with ||v||=1 yield
\[
\frac12c(\alpha)T^{2-\alpha}\le R_{\alpha,T,v}.
\]

1. **Objects:** Actual full-space vector run along supplied unit v.
2. **Quantifiers:** E/structures,α and range proofs,T and threshold proof,v,hv.
3. **Assumptions:** Finite dimension and unit norm in addition to claim9's conditions.
4. **Conclusion:** Same scalar lower bound on the exact vector-run regret.
5. **Boundaries:** Zero-dimensional E has no unit v, so cannot instantiate the premises; dimension is not otherwise specified. All norms use the given real inner-product norm.
6. **Information:** Canonical current selector, same schedule, loss coefficient σ_T(t)v, and initial/comparator zero.
7. **Scope:** No arbitrary starting point, arbitrary comparator or arbitrary legal selector is quantified.

## claim11: existential adverse sequence

For finite-dimensional nontrivial real inner-product E and the same α,T hypotheses, there exists a real-valued loss stream with convex 1-Lipschitz played losses and the lower bound on the actual embedded-loss run:
\[
\exists\ell:\mathbb N\to E\to\mathbb R,\quad
[\forall t<T,\ \operatorname{ConvexOn}_{\mathbb R}(E,\ell_t)
\land\operatorname{LipschitzWith}(1,\ell_t)]
\land
\frac12c(\alpha)T^{2-\alpha}
\le R_T(\mathrm{fullSpace},\eta_\alpha,\iota\circ\ell,0,0).
\]

1. **Objects:** E with NormedAddCommGroup, InnerProductSpace R, FiniteDimensional R and Nontrivial; existential real loss stream.
2. **Quantifiers:** Structures and Nontrivial, α with 0<α<1, T with threshold, then existence of one loss stream. The witness may depend on α,T and E.
3. **Assumptions:** Nontriviality excludes the zero space; no selected unit vector is required from the caller.
4. **Conclusion:** Existence plus both regularity properties for each t<T and the actual-regret lower bound. This is the existence-level endpoint among these types.
5. **Boundaries:** Only played losses are required convex/Lipschitz; later losses remain unspecified by the conclusion. The horizon threshold and factor 1/2 are unchanged.
6. **Information:** Single stream chosen for the actual canonical OSD learner and zero comparator. No random seed, expectation or universal quantification over competing learners.
7. **Scope:** Not one fixed sequence guaranteed for all horizons at once, not a minimax result for all algorithms, and not a claim that losses are bounded in value. No proof of witness existence is supplied in the packet.

## Completeness and limits

All four definitions and eleven statements are reconstructed. The distinction between auxiliary selector/run identities, coefficient facts, conditional explicit lower bounds and final existential lower bound is retained. No unresolved semantic context remains after the permitted API lookup. Strong scope details include schedule positivity for all α, claim6 for all α,T, claim5 regularity at all times, and globally supported affine selector identity; narrower details include the final witness depending on T and only played-time regularity there. No statement was repaired or replaced.

The authorized API search displayed incidental adjacent proof lines; no proof was executed or accepted from them. Actual shared API hashes are recorded only as context snapshots. Source fidelity, compilation, theorem truth and Goal acceptance are not assessed.
