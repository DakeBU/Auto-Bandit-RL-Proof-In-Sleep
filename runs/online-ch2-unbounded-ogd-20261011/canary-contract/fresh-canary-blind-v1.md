# Source-unexposed canary statement decoding

## Provenance and exposure

Only the two assigned neutral files were read in this continuation. Previously this decoder read only a neutral terminal theorem header and neutral definitions, and produced a statement decoding. No original mathematical source, source book, production body, adjacent prospectus, review or verdict was consulted. The assignment and inherited workspace/team instructions were visible. No source identity is guessed, and no proof or compilation is assessed.

Verified raw input SHA-256 hashes:

- `neutral-canary-headers-v1.txt`: `bfa5398e87af36f6637f9c2bcbbad56da074611c4007e0802287dcc0737f7453`
- `neutral-imported-definitions-v1.txt`: `d9e196391b2aad8e2c4f279e14ae8eef142dd2d4c44a46ab77290416d3510d9e`

The assignment requests model Astra and reasoning effort medium. These are requested settings, not an attestation of the executing runtime model or effort.

## Shared definitions and metric

Both statements use the deterministic schedule

\[
\eta_t=(t+1)^{-1/2},\qquad t\in\mathbb N,
\]

where the natural number t+1 is cast to the reals before taking the real power. For losses f_t on a real inner-product space, the supplied recursion is

\[
x_0=0,\qquad x_{t+1}=P_E\bigl(x_t-\eta_t\nabla f_t(x_t)\bigr)
=x_t-\eta_t\nabla f_t(x_t).
\]

Here the domain is the entire space E. The supplied project definition chooses a point minimizing distance in that domain; for the full space the projection is mathematically the identity. The parameter named x1 in the imported recursion is the iterate at index zero. The regret is the signed sum

\[
R_T(0)=\sum_{t=0}^{T-1}\bigl(f_t(x_t)-f_t(0)\bigr).
\]

Thus the first zero argument is the initial point, and the second is the fixed comparator. This is cumulative regret against zero, not an average, norm, absolute value, terminal loss, or an explicit minimization over comparators. The iterates inside this score are the actual gradient recursion. The final scored point is x_(T-1); x_T is the next update and is not scored in R_T.

The common scalar is

\[
\phi(\alpha)=\frac{1}{2-\alpha}+\frac{(1/2)^{1-\alpha}-1}{1-\alpha}.
\]

The gradients are those of the current loss at the current iterate. No stochastic oracle, noisy feedback, bandit feedback, randomized algorithm, or filtration is specified.

## Statement 1: scalar_actual_two_rounds

This theorem has no free parameters or explicit hypotheses. Its loss sequence is fixed, not existential. It takes E=R with its ordinary absolute-value norm and inner product, alpha=1/2, initial point zero, comparator zero and horizon T=2. The supplied switch definition uses natural-number division:

\[
s_t=\begin{cases}-1,&t<(2+1)\mathbin{\mathrm{div}}2=1,\\1,&t\geq1,\end{cases}
\qquad f_t(z)=s_t\langle1,z\rangle=s_tz.
\]

Its entire conclusion is the following conjunction, preserving all twelve outer clauses:

1. The first step size is eta_0=1.
2. The second step size is eta_1=2^(-1/2).
3. The second step size is strictly positive.
4. The second step size is strictly smaller than the first.
5. For every real z, f_0(z)=-z and f_1(z)=z.
6. For every natural t<2, f_t is convex on all of R, globally 1-Lipschitz, and real differentiable everywhere.
7. For every real z, the gradient of f_0 at z is -1 and the gradient of f_1 at z is 1.
8. The actual initial iterate is x_0=0.
9. The actual iterate after the first update is x_1=1.
10. The actual iterate after the second update is x_2=1-2^(-1/2).
11. The actual two-round regret against zero is R_2(0)=1.
12. The horizon two is strictly below the displayed threshold: 2 < 2/((1-1/2)*phi(1/2)).

In compact mathematical form, its iteration and scoring clauses read

\[
x_0=0,\quad x_1=1,\quad x_2=1-2^{-1/2},\qquad
R_2(0)=[f_0(0)-f_0(0)]+[f_1(1)-f_1(0)]=0+1=1.
\]

Round 0 scores the initial point before the first update. Round 1 scores x_1=1 before applying the second, smaller step. The stated value of x_2 is an actual update value, but does not contribute another summand to the two-round score.

Quantifier order is a closed conjunction with two separately scoped universal quantifiers over z and a separate universal quantifier over natural t<2. The theorem does not assume the regularity or gradient formulas; it asserts them for this fixed sequence. Its final strict inequality explicitly puts T=2 outside the threshold condition appearing in the prior neutral terminal header. It does not assert application of that terminal lower-bound theorem at T=2.

## Statement 2: finiteDim_terminal_lower_bound

This is also a closed theorem with no explicit hypotheses. It fixes alpha=1/2 and T=64. Its domain is EuclideanSpace R (Fin 2), namely the two-dimensional real Euclidean inner-product space with its Euclidean norm. It is not the scalar domain used in Statement 1.

There are four outer conjuncts:

1. phi(1/2) >= 1/15.
2. The threshold 2/((1-1/2)*phi(1/2)) is at most 64.
3. The real power 64^(2-1/2) equals 512.
4. There exists a single loss sequence f:N -> R^2 -> R satisfying all the following inner conjuncts simultaneously:
   - For every natural t<64, f_t is convex on all of R^2, globally 1-Lipschitz in Euclidean distance, and real differentiable everywhere.
   - Its actual gradient-descent regret against zero is at least (1/2)*phi(1/2)*64^(2-1/2).
   - That same regret is at least 256/15.
   - That same regret is strictly greater than 17.

Equivalently, with the supplied recursion, the existential conclusion includes

\[
\exists (f_t)_{t\in\mathbb N},\quad
\bigl[\forall t<64:\ f_t\text{ is convex, 1-Lipschitz and differentiable on }\mathbb R^2\bigr],
\]
\[
x_0=(0,0),\quad x_{t+1}=x_t-(t+1)^{-1/2}\nabla f_t(x_t),\quad
R_{64}(0)=\sum_{t=0}^{63}\bigl(f_t(x_t)-f_t(0)\bigr),
\]
\[
\frac12\phi(1/2)\,64^{3/2}\leq R_{64}(0),\qquad
\frac{256}{15}\leq R_{64}(0),\qquad 17<R_{64}(0).
\]

The universally quantified round index lies inside the existential loss-sequence clause. The three lower bounds all refer to the same witness and its same actual recursion. The first three outer numeric conjuncts do not depend on the chosen sequence. Because the horizon is fixed at 64 before the existential choice, this statement gives no horizon-uniform witness and no claim for arbitrary T. No formula for this two-dimensional loss witness or its iterates is supplied; it need not be identified with the scalar switch sequence, and the neutral text does not assert that identification.

## Boundaries and missing context

The scalar losses are explicitly defined for all natural times by switchLoss, but the regularity conjunction in Statement 1 only quantifies t<2. The second loss sequence is defined for all natural times, but its asserted regularity only covers t<64. A Lipschitz constant of 1 is an admissible upper bound; the statement does not assert that the smallest Lipschitz constant is exactly 1.

Differentiable R means real Frechet differentiability at every point. It does not itself assert a continuous derivative, a Lipschitz gradient, twice differentiability, or strong convexity. Statement 2's convexity, Lipschitzness and differentiability are existential witness guarantees, not assumptions imposed on an externally supplied loss sequence. Statement 1 additionally exposes the gradients of its two scored losses everywhere.

There are no theorem proof bodies. The imported gradient and foundational projection-existence definitions are not expanded; their standard mathematical meanings suffice to decode the statements, while their internal implementations remain uninspected. The two-dimensional loss construction is opaque, as expected for an existential statement. These omissions block construction/proof verification, but do not block statement comprehension. The theorem headers alone establish no compilation, successful proof checking, or source-faithfulness verdict. No canonical edit or build was performed.
