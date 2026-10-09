# Two neutral divergence canary reconstructions

Actor /root/osd_blind; requested GPT-6 Astra / medium, without independently attested runtime model or effort. This automated decoder has reused staged history, including the related neutral divergence definition and headers. No fresh-history independence, absolute blindness, human review, or external independence is claimed. Only the current neutral canary file was newly read; no production proof, draft body, source contract, or source material was consulted.

## Imported meaning and notation

The previously supplied neutral definition is retained as related contextual knowledge:
\[
D_\psi(a,b)=\psi(a)-\psi(b)-(\operatorname{fderiv}_{\mathbb R}\psi(b))(a-b).
\]
The derivative base is the second argument. fderiv is a continuous real-linear map and is total, with zero default outside differentiability; this convention is not itself a differentiability hypothesis. Here both generators are explicit real polynomials. No new inspection or verification of the imported production implementation was performed.

IsMinOn F V p means every z∈V satisfies F(p)≤F(z); it does not include p∈V. Both concrete proposed minimizers below are 0, which belongs to their displayed domains. StrictConvexOn R univ ψ is strict convexity on the entire real line: for distinct a,b and positive real weights α,β with α+β=1,
\[
\psi(\alpha a+\beta b)<\alpha\psi(a)+\beta\psi(b).
\]
This strictness pertains to the generator, not to the non-strict comparator inequalities in the targets. All objects are scalar and deterministic. These are proposed conjunctions, not supplied proofs or compiler evidence.

## 1. nonquadratic_nonsmooth

Let ψ(z)=z⁴/4+z²/2. The target asserts seven properties: ψ is globally strictly convex; zero minimizes |z|+Dψ(z,1/2) over all reals; absolute value is not differentiable at zero; Dψ(1/2,0)=9/64; the reversed divergence Dψ(0,1/2)=11/64; every real comparator satisfies the stated three-divergence inequality; and the separate numerical inequality −1/2≤−5/16 holds.

\[
\begin{aligned}
&\operatorname{StrictConvexOn}_{\mathbb R}(\mathbb R,\psi)\\
&\land\operatorname{IsMinOn} (z\mapsto |z|+D_\psi(z,\tfrac12),\mathbb R,0)\\
&\land\neg\operatorname{DifferentiableAt}_{\mathbb R}(|\cdot|,0)\\
&\land D_\psi(\tfrac12,0)=\tfrac9{64}
\land D_\psi(0,\tfrac12)=\tfrac{11}{64}\\
&\land\left[\forall u\in\mathbb R,\ 
-|u|\le D_\psi(u,\tfrac12)-D_\psi(u,0)-D_\psi(0,\tfrac12)\right]\\
&\land(-\tfrac12\le-\tfrac5{16}),
\qquad \psi(z)=\tfrac{z^4}{4}+\tfrac{z^2}{2}.
\end{aligned}
\]

1. **Objects:** A specified quartic-plus-quadratic generator ψ, loss f(z)=|z|, center x=1/2, candidate minimizer p=0, and all-real feasible comparators. The imported divergence is used with its ordered arguments.
2. **Quantifiers and order:** Seven closed conjuncts. The sixth universally quantifies u over R. Strict convexity and IsMinOn have their own internal all-point quantifiers. There is no external assumption that any conjunct already holds.
3. **Assumptions and regularity:** No external hypotheses. Global strict convexity of ψ and nondifferentiability of f at p are conclusions. The minimum assertion is also a conclusion, not a supplied minimizer premise in this canary. No derivative claim for ψ is explicitly conjoined, although the formula is a polynomial.
4. **Conclusion and signs:** Retain all seven assertions. The comparator bound has leading D(u,1/2) followed by two subtracted terms D(u,0) and D(0,1/2); the loss difference is f(0)−f(u)=−|u|. The explicit ordered values 9/64 and 11/64 are unequal and display asymmetry, not two estimates of the same ordered divergence.
5. **Constants and boundary cases:** Coefficients 1/4 and 1/2 are part of ψ; there is no additional implicit half factor in D. The minimum objective has coefficient 1 on D, corresponding to step parameter 1 if compared to the earlier neutral proximal form. At u=0 the comparator inequality is 0≤0. The numeric conjunct corresponds to u=1/2 in the displayed comparison; it is written separately. Its inequality is non-strict even though these particular numerical sides differ. No denominator is zero.
6. **Information and interpretation:** Deterministic minimization over the full real line, with the same fixed center and generator throughout. There is no algorithm, recursion, chronology, expectation, or changing comparator. The target allows a nonsmooth loss at the supplied minimizing point.
7. **Excluded scope and proof status:** Strict convexity is not a statement that every bound is strict or that divergence is symmetric. IsMinOn does not assert membership or uniqueness by definition; no explicit uniqueness conjunct is supplied. The statements and numerical specialization do not certify an actual application of a public helper or proof-term dependency. No proof or source judgment is made.

The minimization conjunct specifically expands to
\[
\forall z\in\mathbb R,\quad
|0|+D_\psi(0,\tfrac12)\le |z|+D_\psi(z,\tfrac12).
\]
It concerns a global minimum on the displayed domain, not only a local extremum.

## 2. boundary_outside_initial

Let q(z)=z²/2. The target asserts six properties: q is globally strictly convex; the center −1 lies outside [0,1]; zero minimizes |z|+Dq(z,−1) on [0,1]; Dq(0,−1)=1/2; every comparator in [0,1] satisfies the stated three-divergence inequality; and the separate numerical inequality −1/2≤1/2 holds.

\[
\begin{aligned}
&\operatorname{StrictConvexOn}_{\mathbb R}(\mathbb R,q)
\land(-1\notin[0,1])\\
&\land\operatorname{IsMinOn}(z\mapsto |z|+D_q(z,-1),[0,1],0)\\
&\land D_q(0,-1)=\tfrac12\\
&\land\left[\forall u\in[0,1],\
-|u|\le D_q(u,-1)-D_q(u,0)-D_q(0,-1)\right]\\
&\land(-\tfrac12\le\tfrac12),
\qquad q(z)=\tfrac{z^2}{2}.
\end{aligned}
\]

1. **Objects:** Quadratic generator q, loss abs, closed interval V=[0,1], center x=−1 and proposed constrained minimizer p=0, with feasible real comparator u.
2. **Quantifiers and order:** Six closed conjuncts. The fifth universally quantifies u and then imposes u∈[0,1]. There is no universal claim over arbitrary centers, domains, or generators.
3. **Assumptions and regularity:** No outer premises. The strict convexity, nonmembership and constrained minimization are asserted conclusions. There is no explicit nonsmoothness conjunct here, unlike the first canary. No center-membership condition is silently inserted.
4. **Conclusion and signs:** All six properties are retained. The comparator bound is −|u|≤D(u,−1)−D(u,0)−D(0,−1), with the center −1 and minimizer 0 playing different roles. The minimum is over [0,1], not over all reals.
5. **Constants and boundary cases:** Center −1 is outside V; p=0 is a feasible endpoint. Divergence is evaluated at the outside base point and has the specified value 1/2 at p. u=0 yields equality 0≤0. u=1/2 corresponds to the separate nonzero comparison −1/2≤1/2. The half in q is explicit; the objective multiplies D by 1. Both endpoints of V are included.
6. **Information and interpretation:** A static constrained minimizer with an outside regularization center, not an iteration with a proven initial-feasibility invariant. Global strict convexity of q extends beyond V, while the comparator/minimum statements remain restricted to V. No temporal or probabilistic structure occurs.
7. **Excluded scope and proof status:** The header does not demand x∈V or an interior minimizer. IsMinOn alone does not include membership, though 0∈[0,1] is fixed by the concrete values. It does not assert an unconstrained minimum, uniqueness, a general outside-center theorem, or that the numeric result's proof uses the imported helper. No proof or source acceptance is supplied.

The minimization clause expands to
\[
\forall z\in[0,1],\quad
|0|+D_q(0,-1)\le |z|+D_q(z,-1).
\]

## Completeness and remaining scope

Both full conjunctions have natural-language, LaTeX and seven-slot reconstructions: seven clauses in the first and six in the second. No unresolved semantic-context ambiguity was identified, using the disclosed retained neutral definition. The input alone does not demonstrate theorem truth, typechecking, production-definition identity, or actual helper dependence. None of those, or source fidelity, is assessed here.
