# Neutral divergence definition and five statement reconstructions

Actor /root/osd_blind; requested GPT-6 Astra / medium. Runtime model and reasoning effort are not independently attested. This is a reused automated staged actor, not a fresh source-naive, absolutely blind, human, or externally independent reviewer. Only the neutral input and targeted mathlib declaration searches needed for fderiv semantics were consulted; no source book, source card, contract, formalizer plan or project proof was read. A targeted search of FDeriv.Basic displayed the zero-default declaration and incidental adjacent proof lines; these were not used as proof verification. No proof, compilation, or source-acceptance verdict is given.

## Definition: divergence

In an arbitrary real normed vector space E, for an arbitrary real-valued function ψ and points x,y, define
\[
D_\psi(x,y)=\psi(x)-\psi(y)-(\operatorname{fderiv}_{\mathbb R}\psi(y))(x-y).
\]
The second argument y is the derivative base point, and x−y is the displacement.

1. **Objects:** E:Type with NormedAddCommGroup E and NormedSpace R E; ψ:E→R; x,y:E. fderiv is a continuous real-linear map E→R.
2. **Quantifiers/order:** This is a definition for every E with these structures, then ψ,x,y, without additional hypotheses.
3. **Assumptions/regularity:** No convexity, differentiability, completeness, finite dimension, or inner product is required to form the expression.
4. **Conclusion/operation:** The displayed signed real difference defines D; it does not assert positivity, symmetry, or separation of points.
5. **Constants/boundaries:** Coefficients are exactly 1,−1,−1. No 1/2, norm square, step size or normalization is inserted. For a nondifferentiable base y, Lean's total fderiv defaults to the zero continuous linear map, so this definition gives ψ(x)−ψ(y); that value does not assert a genuine derivative exists.
6. **Information:** Deterministic evaluation at two supplied points. No prediction, loss feedback, probability or recurrence.
7. **Excluded scope:** D is not assumed to be a metric or nonnegative globally, and no source-specific regularity can be inferred from its name.

## 1. divergence_self

For every ψ and point x, self-divergence is zero.
\[
\forall\psi:E\to\mathbb R,\ \forall x\in E,\quad D_\psi(x,x)=0.
\]

1. **Objects:** The same arbitrary real normed space and total divergence definition.
2. **Quantifiers/order:** Universal E/structures, ψ, then x; no premises.
3. **Assumptions:** No differentiability even at x, and no convexity.
4. **Conclusion:** Exact equality to zero.
5. **Constants/boundaries:** Coincident points give the zero displacement; nondifferentiable points are included by the total definition.
6. **Information:** Pure deterministic algebraic identity.
7. **Excluded scope:** Does not assert that D(x,y)=0 forces x=y, or that other divergences are positive. The identity is proposed without a supplied proof.

## 2. three_point_identity

For every ψ and three arbitrary points, the signed three-divergence combination equals the difference of the two continuous-linear derivative values applied to z−x.
\[
\forall\psi,x,y,z,\quad
D_\psi(z,x)+D_\psi(x,y)-D_\psi(z,y)
=(\operatorname{fderiv}\psi(y)-\operatorname{fderiv}\psi(x))(z-x).
\]

1. **Objects:** ψ:E→R and points x,y,z in an arbitrary real normed space; subtraction of continuous linear maps on the right.
2. **Quantifiers/order:** Universal E/structures, ψ,x,y,z in this order. No restrictions on equality or ordering of points.
3. **Assumptions:** No differentiability or convexity hypotheses. The fderiv terms remain total.
4. **Conclusion:** Exact equality with signs +D(z,x)+D(x,y)−D(z,y) and derivative order fderiv at y minus fderiv at x.
5. **Constants/boundaries:** No factor or denominator. All coincidences of points are permitted, as are nondifferentiable base points; the zero-default convention is retained.
6. **Information:** Algebraic comparison of supplied points; no iterates or temporal meaning.
7. **Excluded scope:** No gradient vector or inner-product identity is being assumed in this normed-space section. No inequality, positivity or proof is supplied.

## 3. divergence_nonneg

If ψ is convex on X, both points belong to X, and ψ is ambient differentiable at the base point y, then Dψ(x,y) is nonnegative.
\[
\forall X\subseteq E,\psi,\quad
\operatorname{ConvexOn}_{\mathbb R}(X,\psi)
\Rightarrow
\forall x,y\in E,\quad
x\in X\Rightarrow y\in X\Rightarrow
\operatorname{DifferentiableAt}_{\mathbb R}(\psi,y)
\Rightarrow 0\le D_\psi(x,y).
\]

1. **Objects:** Set X, real function ψ, and points x,y in the normed core.
2. **Quantifiers/order:** X,ψ,convexity premise,x,y, membership of x, membership of y, then differentiability at y.
3. **Assumptions/regularity:** ConvexOn includes convexity of X and the function's convexity on it. Both memberships are explicit. Differentiability is ambient at y, not merely within X; none is required at x.
4. **Conclusion:** Nonnegativity for this ordered pair.
5. **Constants/boundaries:** x=y is allowed. Boundary points of X are allowed if ambient differentiability holds at y. No openness, closedness, strict convexity or positive dimension is required. Membership prevents an empty X in a realized instance.
6. **Information:** Deterministic supporting comparison, with no gradient representation necessary.
7. **Excluded scope:** Does not assert nonnegativity outside X, at nondifferentiable y, or without convexity. No strict positivity or uniqueness follows as part of this type.

## 4. proximal_one_step

Let η be positive, and let p be a supplied feasible point minimizing z↦f(z)+η⁻¹Dψ(z,x) over V. Assume f is convex on V and ψ is ambient differentiable at both x and p. Then every feasible comparator u satisfies the displayed signed divergence bound.
\[
\begin{aligned}
&\forall V\subseteq E,\ f,\psi:E\to\mathbb R,\ \eta\in\mathbb R,\quad \eta>0,\\
&\forall x,p\in E,\quad p\in V,\quad\operatorname{ConvexOn}_{\mathbb R}(V,f),\\
&\operatorname{DifferentiableAt}_{\mathbb R}(\psi,x),\quad
\operatorname{DifferentiableAt}_{\mathbb R}(\psi,p),\\
&\left[\forall z\in V,\ 
f(p)+\eta^{-1}D_\psi(p,x)
\le f(z)+\eta^{-1}D_\psi(z,x)\right]\\
&\qquad\Longrightarrow
\forall u\in V,\quad
\eta\bigl(f(p)-f(u)\bigr)
\le D_\psi(u,x)-D_\psi(u,p)-D_\psi(p,x).
\end{aligned}
\]

1. **Objects:** V, f,ψ, positive real η, ambient center x, supplied minimizer p, and arbitrary feasible u. Same ψ and η occur throughout.
2. **Quantifiers/order:** E/structures,V,f,ψ,η,hη,x,p,hp,hf,hdx,hdp,hmin, then all u with membership. p is given, not existentially produced.
3. **Assumptions/regularity:** p∈V is explicit because IsMinOn alone does not contain membership. f is convex on V. ψ has ambient derivatives at both base points x and p. There is no f differentiability premise, no ψ convexity premise, no x∈V premise, and no derivative premise at u. V need not be closed or open; E need not be complete or an inner-product space.
4. **Conclusion:** The left side is η times the loss difference f(p)−f(u). The right side has leading D(u,x) and exactly two subtracted residuals: D(u,p) and D(p,x). Their signs cannot be replaced or omitted. Without ψ convexity, the type does not guarantee either residual is nonnegative.
5. **Constants/boundaries:** The objective coefficient is η⁻¹, with η>0 excluding zero and negative values. No hidden factor 1/2. p=x is allowed if feasible; u=p is allowed and the displayed expressions then cancel. x may be outside V. Singleton V and zero-dimensional E are permitted.
6. **Information/existence:** Deterministic conditional statement about an actual supplied minimizer of the specified objective. IsMinOn asserts global comparison over V, not merely a local minimum. It does not provide existence, uniqueness, a selection procedure, an iterate sequence, or a rule determining which data were available before p was chosen.
7. **Excluded scope:** No current-loss derivative, online chronology, boundedness, strong convexity, or probabilistic law may be inferred. The type alone does not prove its inequality or establish a recurrence, and it does not license dropping signed residuals without additional premises.

## 5. divergence_eq_gradient

In a complete real inner-product space, if ψ is ambient differentiable at y, its divergence can be expressed using the inner product with the gradient at y.
\[
\forall\psi:E\to\mathbb R,\ x,y\in E,\quad
\operatorname{DifferentiableAt}_{\mathbb R}(\psi,y)
\Rightarrow
D_\psi(x,y)=\psi(x)-\psi(y)-\langle\nabla\psi(y),x-y\rangle_{\mathbb R}.
\]

1. **Objects:** E with NormedAddCommGroup, InnerProductSpace R and CompleteSpace; real-valued ψ; arbitrary x,y; gradient ψ y in E.
2. **Quantifiers/order:** Universal complete real inner-product space, ψ,x,y, then differentiability at y.
3. **Assumptions/regularity:** Complete inner-product structure is explicit here, unlike the normed core. Differentiability is required at y only; no convexity or finite dimension.
4. **Conclusion:** Exact conversion of the functional evaluation to inner product, with gradient in the first slot and displacement x−y in the second.
5. **Constants/boundaries:** No normalization factor or step size. x=y is included. This header assumes away nondifferentiability at the base, unlike the first two algebraic identities.
6. **Information:** Deterministic representation of the same divergence, not a new update or loss gradient hypothesis.
7. **Excluded scope:** Does not impose inner-product completeness on earlier statements, and does not claim this conversion under omitted typeclasses. It is not proof of positivity or an optimization guarantee.

## Completeness and evidentiary boundary

The definition and all five proposed statements are reconstructed with seven slots. No unresolved semantic-context issue remains. In particular, fderiv's total zero-default convention is distinguished from differentiability, the two explicit ψ differentiability hypotheses in the proximal statement are retained, and minimizer existence/uniqueness is not produced. No source conditions absent from the input were added. This is neither a proof nor a compilation/source-acceptance judgment.
