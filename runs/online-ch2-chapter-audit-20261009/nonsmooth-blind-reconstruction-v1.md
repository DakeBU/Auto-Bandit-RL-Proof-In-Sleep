# Statement-only reconstruction: three nonsmooth terminals

Actor: /root/osd_blind. Requested settings: GPT-6 Astra / medium; runtime model and reasoning effort are not independently attested. This automated decoder has reused staged role history, including earlier unrelated packets. This is not absolute blindness, human review, or external independence. The present reconstruction uses only the current neutral packet and its input JSON. No source identity, earlier verdict, proof body, or other repository file was consulted.

These are proposed closed theorem types. The text below describes their assertions and boundary scope; it supplies neither proofs nor evidence of compilation or source fidelity.

## Shared notation

For Terminals 2 and 3, E is an arbitrary finite-dimensional real inner-product space with the stated normed additive group structure. Its dimension may be zero. There is no positive-dimension, nonzero-vector, unit-norm, bounded-domain, or discrete-label hypothesis. Write Df(x) to mean ordinary ambient real Fréchet differentiability at x. Global differentiability means that this property holds at every x in E. Convexity is on the entire ambient space, not on a feasible subset. Inner products are real.

## Terminal1

For every real center c, the translated absolute-value function is convex on all of the real line. At each real x it is differentiable exactly when x differs from c.

\[
\forall c\in\mathbb R,\quad
\operatorname{Convex}_{\mathbb R}\bigl(x\mapsto |x-c|\bigr)
\ \land\
\bigl[\forall x\in\mathbb R,\ 
D(w\mapsto |w-c|)(x)\ \Longleftrightarrow\ x\ne c\bigr].
\]

1. **Objects:** A real parameter c and the real-valued function f_c(w)=|w-c| on the real line.
2. **Quantifiers and order:** c is arbitrary; for that same function the convexity assertion is conjoined with a universally quantified pointwise equivalence for all x. x is not chosen in advance of c.
3. **Assumptions:** Only c and x being real. No condition c≠0 or x≠c is a premise of the whole proposition; x≠c is the right side of the equivalence.
4. **Conclusion:** Ambient global convexity, together with exact pointwise differentiability away from the center and its failure at the center.
5. **Constants, indices, and degeneracies:** The center can equal zero. The point x=c is always available and is exactly the exceptional point. There are no horizon, index, probability, or normalization parameters.
6. **Information and differentiability scope:** Deterministic ambient pointwise Fréchet differentiability. The theorem explicitly asserts convexity globally but expresses differentiability pointwise for every x. It does not assert global differentiability; its pointwise criterion includes an exceptional point for every c.
7. **Excluded scope:** No restricted-domain, one-sided, subgradient, directional-derivative, Lipschitz-constant, or explicit derivative formula is stated.

## Terminal2

For every admissible space E and every vector a, the function whose value is the larger of 1−⟨a,x⟩ and zero is convex on E. At every point x, it is differentiable exactly when the margin ⟨a,x⟩ is not 1.

\[
\forall E\ \text{as above},\ \forall a\in E,\quad
\operatorname{Convex}_{E}\bigl(x\mapsto\max\{1-\langle a,x\rangle,0\}\bigr)
\ \land\
\left[\forall x\in E,\ 
D\bigl(w\mapsto\max\{1-\langle a,w\rangle,0\}\bigr)(x)
\Longleftrightarrow \langle a,x\rangle\ne1\right].
\]

1. **Objects:** An arbitrary finite-dimensional real inner-product space E, vector a∈E, and real-valued ambient function h_a(w)=max{1−⟨a,w⟩,0}.
2. **Quantifiers and order:** Universally quantify E and its structures, then a. For each fixed E,a, conjoin convexity with an equivalence universally quantified over x∈E. Both sides refer to the same a and point x.
3. **Assumptions:** The three displayed structural assumptions on E only. There is no a≠0 premise and no dimension lower bound. The margin condition is a conclusion-side characterization, not an assumed domain restriction.
4. **Conclusion:** Ambient convexity and the exact pointwise differentiability criterion. At a point of margin 1 the asserted criterion says differentiability fails; at any other margin it says differentiability holds.
5. **Constants, indices, and degeneracies:** Threshold 1 and truncation value 0 are fixed real constants. If a=0 then every margin is 0, h_a is constant 1, and no margin-1 point exists. A zero-dimensional E forces a=0 and therefore falls in this constant case. For nonzero a, margin-1 points can occur (indeed the corresponding level set is nonempty); none is ruled out by the hypotheses.
6. **Information and differentiability scope:** Deterministic and ambient; no randomness, feedback, or observation order. Differentiability is stated pointwise with universal x. The header does not include a separate global Differentiable equivalence, although the pointwise characterization distinguishes constant and nonconstant cases.
7. **Excluded scope:** No false unconditional assertion that every a has a kink point, and no nonzero assumption inserted to manufacture one. No gradient formula, feasible-set smoothness, optimization algorithm, or probability claim is supplied.

## Terminal3

For every admissible E, every real scalar y, and every vector z, the function max{1−y⟨z,x⟩,0} is convex on E. At each x it is differentiable exactly when its margin y⟨z,x⟩ differs from 1. In addition, the entire function is differentiable at every ambient point exactly when the effective vector y•z is zero.

\[
\begin{aligned}
&\forall E\ \text{as above},\ \forall y\in\mathbb R,\ \forall z\in E,\\
&\operatorname{Convex}_{E}\bigl(x\mapsto\max\{1-y\langle z,x\rangle,0\}\bigr)\\
&\quad{}\land
\left[\forall x\in E,\ 
D\bigl(w\mapsto\max\{1-y\langle z,w\rangle,0\}\bigr)(x)
\Longleftrightarrow y\langle z,x\rangle\ne1\right]\\
&\quad{}\land
\left[
\bigl(\forall w\in E,\ D(w'\mapsto\max\{1-y\langle z,w'\rangle,0\})(w)\bigr)
\Longleftrightarrow y\mathbin{\bullet}z=0_E
\right].
\end{aligned}
\]

1. **Objects:** E with its stated structures, real y, vector z∈E, and h_{y,z}(w)=max{1−y⟨z,w⟩,0}. The effective normal is y•z∈E; it is not a real-valued product.
2. **Quantifiers and order:** E and structures, then y, then z, all arbitrary. Three conjuncts concern this same function. The universal x belongs to the middle conjunct; the last conjunct is a separate global differentiability equivalence. y and z are fixed while points vary.
3. **Assumptions:** Only the displayed structural assumptions and types. y need not be ±1, nonzero, nonnegative, or a normalized label. z need not be nonzero, normalized, or bounded. No positive dimension is required.
4. **Conclusion:** Global convexity, the precise pointwise criterion at margin 1, and the global criterion Differentiable iff y•z=0. Global differentiability is a universal assertion about points; it is not the claim that some individual off-margin point is differentiable.
5. **Constants, indices, and degeneracies:** Fixed threshold 1 and truncation 0. When y=0 or z=0, the effective vector is zero, all margins are 0, and the function is constant 1; the pointwise and global criteria are compatible. Over the real scalars, y•z=0 is equivalent to y=0 or z=0. In dimension zero z=0 necessarily, for every real y. When y•z≠0, margin 1 can occur, so the global failure does not imply differentiability fails at all points: the middle clause still characterizes the off-margin points. Negative y is included.
6. **Information and differentiability scope:** No probabilistic or algorithmic information structure. Both differentiability notions are ordinary real ambient Fréchet notions. The final equivalence concerns all ambient points, whereas the middle equivalence tests one arbitrary point with the same parameters.
7. **Excluded scope:** No nonzero-label convention may be added. There is no assertion of everywhere nondifferentiability when y•z≠0, no claim that the equality margin can occur when the effective vector vanishes, and no derivative/subgradient formula or source interpretation is provided.

## Completeness and boundary review

All three terminals are reconstructed with seven slots and explicit quantifier scope. The packet supplies enough semantic context for each; there is no unresolved type or semantic-context question in this reading.

Zero labels and zero features are allowed in Terminal3, and a zero effective vector is allowed in Terminal2. Zero-dimensional spaces are allowed in Terminals2–3. Their constant-function cases do not conflict with the pointwise margin criterion because the margin equals 0 everywhere, never 1. Margin 1 is present only in the nonzero effective-normal case; the proposed types characterize differentiability at such points without requiring all parameters to generate such a point. Terminal1 always includes its center as the exceptional point. These boundary descriptions clarify the meaning of the draft assertions; this report neither proves them nor certifies typechecking.

No source fidelity, proof acceptance, compilation result, chapter acceptance, or program completion is assessed.

