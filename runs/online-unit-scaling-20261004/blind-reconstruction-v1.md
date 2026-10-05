# Fresh restricted-input reconstruction: N01–N22

This pass uses only `blind-packet-v1.md` in this run directory as mathematical input. No source, provenance, name map, proof, type log, review, or other file was read for this pass. Previous unrelated actor history is not claimed erased; previous artifacts are unchanged. This is a distinct automated decoding pass, not human or external-model review. No compilation, proof validation, or source acceptance is claimed.

Independent raw-byte packet SHA-256:
`2d173e0575477e7e4c0be6f58f65b99dbe2f00ce8ad4ab0e876bee727957072e`.

## Shared objects and precise notation

Except for the explicitly abstract dimension identities N01–N02, the supplied context is a finite-dimensional real inner-product space E with its normed additive commutative group structure. No positive dimension is required. A structure C holds a nonempty closed convex carrier; K is specifically the whole-space carrier E. J selects a nearest point to its argument in K by classical choice. All trajectory targets pass K. Although H,Z,G,L,R accept a parameter k:C E, their supplied definitions use J for the fixed K; this packet does not describe projection onto arbitrary k.carrier.

Properness Q(f) means f:E→EReal never takes −∞ anywhere and has at least one finite real value at some point. Define

\[
S_f(x)=\{g\in E:\forall y\in E,\ f(x)+\iota(\langle g,y-x\rangle)\le f(y)\}.
\]

The support inequality queries all of E. B(f) means Q(f) and S_f(x) nonempty for every x∈K, hence every x∈E. It is not an explicit global convexity hypothesis. Properness together with a supporting vector at x supplies finite f(x); B therefore supplies finite values throughout E. No uniform bound on those values or vectors is imposed.

An exogenous fixed deterministic policy p_t takes t whole past loss functions, a tuple of t+1 outputs including the current output, and the current whole loss function, and returns a vector. It is not required by type to return a support vector. It has no future-loss argument. For schedule η, losses f, initialization x₁ (despite zero-based time), and p, abbreviate the actual original run by

\[
H_0=(x_1),\quad z_t=H_t(t),\quad
 g_t=p_t((f_s)_{s<t},H_t,f_t),\quad
 H_{t+1}=H_t\mathbin{\|}(J(z_t-\eta_t g_t)).
\]

Thus z₀=x₁. H is a generated output history, not an arbitrary stored vector sequence. Actual legality L_T means ∀t<T, g_t∈S_{f_t}(z_t). No universal law on all possible histories is defined or assumed in these targets. The real-valued regret expression is

\[
R_T(u)=\sum_{t=0}^{T-1}\big(\operatorname{toReal}f_t(z_t)-\operatorname{toReal}f_t(u)\big).
\]

The packet does not expand EReal.toReal. Equalities between converted expressions are algebraic even without finite values; interpreting them as ordinary finite losses requires the corresponding properness/support premises. Actual legality with Q gives finite played losses, but by itself does not guarantee finite values at an arbitrary comparator. B gives both.

Define F_c f(y)=f(cy), transformed schedule e_c(η)_t=η_t/c², and transformed policy

\[
p^{(c)}_t(b,h,f)=c\,p_t((F_{1/c}b_i)_{i<t},(c h_i)_{i\le t},F_{1/c}f).
\]

This policy reconstructs original-coordinate functions and outputs before applying p, then scales the returned vector by c. It uses exactly the finite past and current function that its own interface receives, not a separate access to a full future sequence. It is not generally correct to keep p unchanged.

For c>0, write the matched transformed run with hats:

\[
\widehat\eta_t=\eta_t/c^2,\quad \widehat f_t=F_c f_t,
\quad\widehat x_1=x_1/c,\quad\widehat p=p^{(c)},
\]

and use \(\widehat H_t,\widehat z_t,\widehat g_t,\widehat R_T\) for the actual run generated from these data. This notation always includes all four transformations. N18 explicitly uses a different, unadjusted schedule in transformed coordinates and is written separately below. The scalar expression is U(A,B,η)=A/(2η)+ηB/2; scalar B as an argument of U is distinct from the predicate B(f).

All claims are deterministic, with no probabilities, expectations, random oracles, or independence requirements. Finite-past typing describes the information interfaces; these headers do not contain a separate paired-run causality theorem or certify how external callers chose p, η, or initialization. Time T means T rounds 0,…,T−1 and terminal output z_T.

## N01

1. **Objects/spaces:** Abstract additive commutative group D, elements X,L,H representing additive unit exponents; these are not vectors in the algorithmic space E.
2. **Quantifier order:** Every D with that structure and every X,L,H satisfying the premise.
3. **Assumptions:** H+(L−X)=X.
4. **Conclusion/metric:** H=X+X−L; this solves the supplied dimension-balance identity, not an optimization or regret problem.
5. **Constants:** X occurs twice; additive exponent notation corresponds to multiplying units, and subtraction to division.
6. **Information/probability:** Deterministic group identity, no observation order.
7. **Boundaries:** No real-number, positivity, dimensional independence, or numerical step-size premise is imposed; D can have arbitrary additive-group structure.

## N02

1. **Objects/spaces:** Additive commutative group D and X,L∈D.
2. **Quantifier order:** Every such D,X,L.
3. **Assumptions:** Only the group structure.
4. **Conclusion/metric:** Both identities hold: X+X−(X+X−L)=L and (X+X−L)+(L−X)+(L−X)=L.
5. **Constants:** Two X terms in the candidate exponent and two copies of L−X in the second equality.
6. **Information/probability:** Deterministic algebra; no probability or temporal input.
7. **Boundaries:** These are abstract unit-consistency equalities. They establish neither numerical parameter values nor a regret guarantee.

## N03

1. **Objects/spaces:** Extended-real function f on E and the coordinate pullback F_c.
2. **Quantifier order:** Every c>0 and every f:E→EReal.
3. **Assumptions:** c strictly positive; no properness or differentiability.
4. **Conclusion/metric:** F_{1/c}(F_c f)=f as equality of whole functions.
5. **Constants:** Reciprocal scaling, no loss-value multiplier or additive term.
6. **Information/probability:** Deterministic invertibility of the coordinate change.
7. **Boundaries:** Functions with infinite values are included. c=0 and c<0 are not within this header, even if a broader algebraic statement might be possible.

## N04

1. **Objects/spaces:** f:E→EReal, Q, and F_c f.
2. **Quantifier order:** Every positive c and every proper f.
3. **Assumptions:** c>0 and Q(f).
4. **Conclusion/metric:** Q(F_c f): transformed function has no −∞ values and has some finite witness.
5. **Constants:** Coordinate factor c only; finite loss values are not multiplied.
6. **Information/probability:** Deterministic preservation of properness.
7. **Boundaries:** Properness permits +∞ away from the finite witness; it does not mean finite everywhere or uniformly bounded.

## N05

1. **Objects/spaces:** f:E→EReal, y,g∈E, original point cy and transformed point y.
2. **Quantifier order:** Every c,f,y,g satisfying the hypotheses.
3. **Assumptions:** c>0, Q(f), and g∈S_f(cy).
4. **Conclusion/metric:** cg∈S_{F_c f}(y), meaning for every z∈E, F_c f(y)+ι(⟨cg,z−y⟩)≤F_c f(z).
5. **Constants:** Support vector scales by c, not 1/c or c².
6. **Information/probability:** Deterministic all-query support transport at the specified point; no policy law is involved.
7. **Boundaries:** Only this membership direction is stated; no set equality or universal selector law. Q and membership ensure finite loss at cy but not necessarily every point.

## N06

1. **Objects/spaces:** f and F_c f on the fixed whole-space K, predicate B.
2. **Quantifier order:** Every c>0 and every f satisfying B(f).
3. **Assumptions:** Properness and nonempty support sets at every original point, plus c>0.
4. **Conclusion/metric:** B(F_c f), namely transformed properness and a support vector at every transformed point.
5. **Constants:** Positive coordinate scale c with K=E unchanged as a set.
6. **Information/probability:** Deterministic statement about existence of support vectors, not how p chooses them.
7. **Boundaries:** Not a claim for arbitrary constrained domains. B is stronger than actual feedback legality on a finite run.

## N07

1. **Objects/spaces:** Real-valued f:E→ℝ, y,g∈E, real c, gradient-at relation.
2. **Quantifier order:** Every real c,f,y,g meeting the derivative premise.
3. **Assumptions:** f has gradient g at cy; no positivity or nonzero assumption on c.
4. **Conclusion/metric:** y↦f(cy) has gradient cg at y, formally HasGradientAt(F_c f,cg,y) for the real-valued composition.
5. **Constants:** Gradient multiplier c with its sign preserved.
6. **Information/probability:** Deterministic differential chain rule, no feedback assumptions.
7. **Boundaries:** Includes c=0 and negative c. This broader calculus statement must not be restricted to the positive scaling assumptions of other targets or confused with an EReal support condition.

## N08

1. **Objects/spaces:** Real f, real c, point y, and the gradient operator.
2. **Quantifier order:** Every c,f,y with differentiability at cy.
3. **Assumptions:** DifferentiableAt ℝ f (cy), with no sign condition on c.
4. **Conclusion/metric:** ∇(z↦f(cz))(y)=c∇f(cy).
5. **Constants:** Exactly c times the original gradient.
6. **Information/probability:** Deterministic calculus identity, independent of the policy construction.
7. **Boundaries:** Zero and negative c included; differentiability is required even where a weaker special-case hypothesis might suffice. No convexity or properness premise.

## N09

1. **Objects/spaces:** x,g∈E and real η,c.
2. **Quantifier order:** Every c>0, arbitrary η∈ℝ, and arbitrary x,g.
3. **Assumptions:** Only c>0 in addition to ambient structure.
4. **Conclusion/metric:** (x−ηg)/c=x/c−(η/c²)(cg).
5. **Constants:** Step rescales by 1/c² and vector by c.
6. **Information/probability:** Deterministic one-update algebra; no generated history or legality premise.
7. **Boundaries:** Zero/negative η included. g is arbitrary, not necessarily a gradient or support vector; no projection on another domain is asserted.

## N10

1. **Objects/spaces:** x,g∈E and real η,c.
2. **Quantifier order:** Every positive c, every real η,x,g.
3. **Assumptions:** c>0 only.
4. **Conclusion/metric:** c(x/c−η(cg))=x−(c²η)g.
5. **Constants:** An unadjusted transformed step η becomes c²η in original coordinates.
6. **Information/probability:** Deterministic algebraic identity, not a regret bound.
7. **Boundaries:** No positivity of η or legality of g required. This identity is distinct from compensating the step by 1/c² in N09.

## N11

1. **Objects/spaces:** Schedule η:ℕ→ℝ, scale c, and one index t.
2. **Quantifier order:** Every positive c, schedule, and t with η_t>0.
3. **Assumptions:** c>0, η_t>0.
4. **Conclusion/metric:** e_c(η)_t=η_t/c²>0.
5. **Constants:** Denominator c².
6. **Information/probability:** Deterministic admissibility at that time; no information constraint on how η was chosen.
7. **Boundaries:** No positivity at other times is required or concluded. Zero/negative c and nonpositive η_t lie outside this header.

## N12

1. **Objects/spaces:** Original generated output history H_t and matched transformed generated history \(\widehat H_t\), using K.
2. **Quantifier order:** Every positive c, schedule, full loss sequence, initialization, policy, and time t.
3. **Assumptions:** c>0 only; no regularity, legality, or step positivity.
4. **Conclusion/metric:** \(\widehat H_t(i)=H_t(i)/c\) for every 0≤i≤t, as equality of full functions on Fin(t+1).
5. **Constants:** Loss arguments scale by c, outputs/initialization by 1/c, steps by 1/c², selected-policy definition by c.
6. **Information/probability:** Deterministic identity of actual recursively generated histories with transformed policy p^{(c)}. The policy receives finite past functions and all outputs through the current play, then current f_t.
7. **Boundaries:** Includes t=0, arbitrary η and infinite loss values. No analogous constrained-domain statement or identity with an unchanged arbitrary p is made.

## N13

1. **Objects/spaces:** Original output z_t and matched transformed output \(\widehat z_t\).
2. **Quantifier order:** Every positive c and all original run data, every t.
3. **Assumptions:** c>0 only.
4. **Conclusion/metric:** \(\widehat z_t=z_t/c\).
5. **Constants:** Factor 1/c at the same index t; no time shift.
6. **Information/probability:** Deterministic same-run correspondence with all schedule/loss/initialization/policy transformations applied.
7. **Boundaries:** No support or finiteness assumptions; includes initial output. Does not assert equality between arbitrary unrelated trajectories.

## N14

1. **Objects/spaces:** Actual selected original g_t and matched transformed \(\widehat g_t\).
2. **Quantifier order:** Every c>0, original data tuple, and t.
3. **Assumptions:** c>0 only, no actual legality assumption.
4. **Conclusion/metric:** \(\widehat g_t=cg_t\).
5. **Constants:** Feedback factor c, in contrast to output factor 1/c.
6. **Information/probability:** Deterministic equality of selections from the transformed actual history, not just an arbitrary vector substitution. Current whole loss is an allowed input to both coupled selectors.
7. **Boundaries:** The selections can be illegal; this equality does not certify membership in support sets. No universal oracle law is inferred.

## N15

1. **Objects/spaces:** Actual original and matched transformed runs, horizon T, properness Q and legality L_T.
2. **Quantifier order:** Every c>0 and run; assume Q(f_t) and original legality for every t<T, then conclude transformed legality for all those times.
3. **Assumptions:** Positive c, horizon properness, and L_T of the original run. No B(f_t), positive steps, or universal policy law is required.
4. **Conclusion/metric:** \(\widehat g_t\in S_{F_cf_t}(\widehat z_t)\) for all t<T, i.e. transformed L_T.
5. **Constants:** Uses exact c and 1/c transport from the matched runs; no error term.
6. **Information/probability:** Deterministic actual-trajectory support preservation. Off-trajectory selector behavior remains unconstrained.
7. **Boundaries:** T=0 allowed. Properness plus actual legality ensures finite played losses, but does not by itself ensure a finite arbitrary comparator loss. No claim after T or for arbitrary domains.

## N16

1. **Objects/spaces:** Original and matched transformed loss evaluated at their actual time-t plays.
2. **Quantifier order:** Every c>0 and run data, every t.
3. **Assumptions:** c>0 only.
4. **Conclusion/metric:** \((F_cf_t)(\widehat z_t)=f_t(z_t)\) in EReal.
5. **Constants:** Exact equality of loss values; no multiplicative loss-unit factor.
6. **Information/probability:** Deterministic same-play correspondence after coordinate conversion.
7. **Boundaries:** Either side may be infinite. The equality alone is not a finiteness certificate, and no support or properness premise is present.

## N17

1. **Objects/spaces:** Original R_T(u) and matched transformed converted-regret expression at u/c.
2. **Quantifier order:** Every c>0, original run, comparator u∈E, natural horizon T.
3. **Assumptions:** c>0 only; no finiteness or legality conditions.
4. **Conclusion/metric:** \(\widehat R_T(u/c)=R_T(u)\).
5. **Constants:** Equality, with comparator scaled by exactly 1/c and no scale factor on regret.
6. **Information/probability:** Deterministic identity of the sums defined using toReal on this coupled pair of runs.
7. **Boundaries:** T=0 allowed. This is pure converted-expression algebra for arbitrary EReal losses; it is not by itself equality of finite ordinary loss regrets. Proper/legality or stronger regularity hypotheses would be needed for that interpretation.

## N18

1. **Objects/spaces:** A transformed-coordinate run using losses F_cf, initialization x₁/c, policy p^{(c)}, but unadjusted schedule η; compare with original-coordinate run using c²η.
2. **Quantifier order:** Every c>0, schedule η, losses, initialization, policy, and time t.
3. **Assumptions:** c>0 only; no step positivity or support hypotheses.
4. **Conclusion/metric:**
   \[
   c\,Z(K,\eta,F_cf,x_1/c,p^{(c)},t)
   =Z(K,(s\mapsto c^2\eta_s),f,x_1,p,t).
   \]
5. **Constants:** Exactly c² amplification of original-coordinate step sizes.
6. **Information/probability:** Deterministic identity of two genuinely generated runs. The original-coordinate feedback on the right is generated using its changed schedule, not assumed equal to feedback from an original η-run.
7. **Boundaries:** This is not matched-run invariance under unchanged steps. Arbitrary real schedule entries and t=0 included; no regret comparison or legal-selector conclusion.

## N19

1. **Objects/spaces:** Arbitrary x,u∈E and c>0.
2. **Quantifier order:** Every such c,x,u.
3. **Assumptions:** Positive c only.
4. **Conclusion/metric:** ‖x/c−u/c‖²=‖x−u‖²/c².
5. **Constants:** Squared distance scales by 1/c².
6. **Information/probability:** Deterministic geometric identity; no histories or losses.
7. **Boundaries:** Includes x=u and zero vectors. It supplies neither a bounded-domain assumption nor a special comparator condition; c≤0 is outside the header.

## N20

1. **Objects/spaces:** Actual feedback energy sums of original and matched transformed runs through T−1.
2. **Quantifier order:** Every positive c, original run data, and natural T.
3. **Assumptions:** c>0 only.
4. **Conclusion/metric:** \(\sum_{t<T}\|\widehat g_t\|^2=c^2\sum_{t<T}\|g_t\|^2\).
5. **Constants:** Exact factor c² and unit coefficients in both sums.
6. **Information/probability:** Deterministic identity for the coupled actual selections, not a stochastic second-moment bound.
7. **Boundaries:** T=0 gives empty sums. No norm bound, legal feedback, or finite-loss condition is needed; “energy” refers only to this finite sum of squared norms.

## N21

1. **Objects/spaces:** Scalar U with real A,B,η,c; these scalar coefficients are not themselves a supplied trajectory.
2. **Quantifier order:** Every c>0, every A,B∈ℝ, and every η>0.
3. **Assumptions:** c>0 and η>0. Notably neither A≥0 nor B≥0 is required.
4. **Conclusion/metric:** U(A/c²,c²B,η/c²)=U(A,B,η).
5. **Constants:** A divided by c², B multiplied by c², and η divided by c²; both terms in U retain their factors 1/2.
6. **Information/probability:** Deterministic scalar identity, not a proof that either side is an actual regret bound in all cases.
7. **Boundaries:** Negative and zero A or B included. Nonpositive η and c are excluded by the declared assumptions. No optimization or uniqueness statement is present.

## N22

1. **Objects/spaces:** Original constant-step run with η, its matched transformed run with constant η/c², horizon T, and arbitrary u∈E.
2. **Quantifier order:** Every c>0, η>0, full loss sequence, initialization, policy and T satisfying the horizon premises, then every comparator u.
3. **Assumptions:** B(f_t) for every t<T and actual original legality L_T for the constant-η run. No universal selector law or gradient-norm bound. K is the whole space, so all initializations/comparators are allowed.
4. **Conclusion/metric:**
   \[
   \widehat R_T(u/c)\le
   \frac{\|x_1-u\|^2}{2\eta}
   +\frac\eta2\sum_{t=0}^{T-1}\|g_t\|^2
   -\frac{\|z_T-u\|^2}{2\eta},
   \]
   where every quantity on the right is from the original constant-η run, and the left from the fully matched transformed run.
5. **Constants:** Exact initial term, coefficient η/2 on feedback energy, and negative terminal residual with denominator 2η. No factor c remains on the right, and terminal output is z_T after T updates.
6. **Information/probability:** Deterministic finite-loss regret bound. B supplies properness and support everywhere, hence finite original comparator/played values; the positive coordinate transformation preserves this interpretation. p still needs legality only on the actual original trajectory. The transformed policy receives only its finite past and current whole loss.
7. **Boundaries:** T=0 allowed, with empty sum and cancelling initial/terminal distances. Nonpositive η or c excluded. No diameter, rate O(√T), tuned horizon, arbitrary-domain result, or theorem asserting feedback legality for every possible policy history is included.

## Limits and ambiguities

The packet fixes sufficient definitions for this reconstruction, including the otherwise potentially misleading unused domain-interface parameter. EReal.toReal and library projection/gradient facts are not expanded; no proof or elaboration verification is inferred. The positive-scaling hypotheses have been preserved exactly even where an algebraic identity could plausibly extend further. Conversely N07–N08 retain their unrestricted real c. N01–N02 are abstract additive dimension equations, not numeric update theorems. No source identity, provenance, or broader scientific acceptance follows from this decoding.
