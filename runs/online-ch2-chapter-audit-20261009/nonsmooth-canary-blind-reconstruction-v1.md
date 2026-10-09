# Five concrete nonsmooth proposition reconstructions

Actor /root/osd_blind. Requested GPT-6 Astra / medium; runtime model and effort are not independently attested. This is a reused automated decoder with prior staged role history, not an absolutely blind, human, or externally independent reviewer. Only the current packet and accompanying JSON were read for this task. The following text reconstructs proposed types; it does not prove them or claim compilation, source fidelity, or acceptance.

## Notation and exact aliases

Plane is the canonical real Euclidean space indexed by Fin 2, identified with R² with its Euclidean inner product. e0=(1,0) and e1=(0,1); these are the supplied EuclideanSpace.single values, not unspecified orthogonal vectors. On the real line, ⟨z,w⟩=zw. Write Df(x) for ordinary real ambient Fréchet differentiability at x and Df for differentiability at every point of the indicated domain. Convexity is on the entire domain. E0 denotes EuclideanSpace R (Fin 0), the zero-dimensional real space.

## TerminalC001

The function f(w)=|w−10| is convex on R, is not differentiable at 10, and is differentiable at each of 9 and 11.

\[
\operatorname{Convex}_{\mathbb R}(f)\ \land\ \neg Df(10)
\ \land\ Df(9)\ \land\ Df(11),\qquad f(w)=|w-10|.
\]

1. **Objects:** One fixed real-valued function on the real line.
2. **Quantifiers/order:** A closed conjunction of four properties; w is a bound function argument. No externally quantified parameter or premise.
3. **Assumptions:** None beyond the specified real types and function.
4. **Conclusion:** Global convexity, failure of pointwise differentiability at 10, and pointwise differentiability at 9 and 11, all for the same function.
5. **Constants/boundaries:** Center 10; test points one unit below and above it. The exceptional point is explicitly included.
6. **Information/differentiability:** Deterministic ambient scalar differentiability. Convexity is global; the three differentiability tests are pointwise. No probability, history, or algorithm.
7. **Excluded scope:** No derivative values, subgradient formula, or full universal differentiability characterization is asserted by this particular type. It does not claim differentiability everywhere.

## TerminalC002

Let f+(w)=max{1−6w,0} and f−(w)=max{1+6w,0}. Each is globally convex. f+ is not differentiable at 1/6, and f− is not differentiable at −1/6. Both are differentiable at zero, and neither is globally differentiable. These are all eight conjuncts.

\[
\begin{aligned}
&\operatorname{Convex}_{\mathbb R}(f_+)
\land \operatorname{Convex}_{\mathbb R}(f_-)\\
&\land\neg Df_+(1/6)
\land\neg Df_-(-1/6)\\
&\land Df_+(0)
\land Df_-(0)\\
&\land\neg Df_+
\land\neg Df_-,
\\
&f_+(w)=\max\{1-2\langle3,w\rangle,0\}=\max\{1-6w,0\},\\
&f_-(w)=\max\{1-(-2)\langle3,w\rangle,0\}=\max\{1+6w,0\}.
\end{aligned}
\]

1. **Objects:** Two different real-valued scalar functions with fixed feature 3 and fixed scalar factors 2 and −2.
2. **Quantifiers/order:** A closed eight-part conjunction in the displayed order: two convexity properties, two failures at their respective boundaries, two differentiability properties at zero, and two failures of global differentiability. There is no universally quantified label parameter here.
3. **Assumptions:** No hypotheses; the positive and negative factors are concrete nonzero real numbers, not Boolean labels.
4. **Conclusion:** Each function has the exact specified pointwise tests, and each fails the everywhere-differentiable property. The negative factor has its own boundary, not the positive factor's boundary.
5. **Constants/boundaries:** Margins are 6w and −6w. Their margin-1 locations are respectively 1/6 and −1/6, where the functions equal zero. At w=0 both margins are zero and both function values are 1. The denominators are nonzero fixed 6. f+ is in its positive affine branch for w<1/6; f− is in that branch for w>−1/6.
6. **Information/differentiability:** Ambient scalar pointwise differentiability and global differentiability are distinct predicates. Non-global differentiability means failure at some point; it does not negate the two explicit differentiability claims at zero.
7. **Excluded scope:** Not a theorem quantified over arbitrary positive/negative labels or all points; no rates, derivative values, probability, feasible domain, or nondifferentiability everywhere is asserted.

## TerminalC003

For every pair of real parameters y,z, setting the scalar factor to zero gives a globally differentiable constant-one function. Setting the feature to zero also gives a globally differentiable constant-one function. Both equalities to 1 hold at every real input w for that same y,z.

\[
\begin{aligned}
\forall y,z\in\mathbb R,\quad&
Dg_z\ \land\ Dh_y\
\land\bigl[\forall w\in\mathbb R,\ g_z(w)=1\land h_y(w)=1\bigr],\\
&g_z(w)=\max\{1-0\langle z,w\rangle,0\},\\
&h_y(w)=\max\{1-y\langle0,w\rangle,0\}.
\end{aligned}
\]

1. **Objects:** Two scalar functions g_z and h_y, with arbitrary real parameters y and z.
2. **Quantifiers/order:** Universally quantify y then z; conjoin global differentiability of g_z, global differentiability of h_y, and a universal w whose scope contains both value equalities.
3. **Assumptions:** None restricting y or z. Either or both may be zero, negative, or positive.
4. **Conclusion:** Both functions are globally differentiable and both are exactly 1 at every real input.
5. **Constants/boundaries:** The zero factor and zero feature annihilate the respective inner-product terms. Both margins are identically zero, so margin 1 never occurs in either function. The truncation max with 0 returns 1.
6. **Information/differentiability:** Global differentiability, not just a test at one point; deterministic, with no probabilistic or feedback structure.
7. **Excluded scope:** No claim that nonzero y and z produce a globally differentiable function; no hidden nonzero-label convention and no derivative formula. The two displayed functions must not be replaced with the general function max{1−y⟨z,w⟩,0}.

## TerminalC004

For the fixed plane function H(w)=max{1−⟨e0,w⟩,0}=max{1−w0,0}, ambient differentiability fails at e0+3e1=(1,3), whereas it holds at e1=(0,1). The scalar function obtained by restricting H to the line t↦e0+t e1 is differentiable at scalar t=0.

\[
\neg DH(e_0+3e_1)\ \land\ DH(e_1)\ \land\ Dg(0),
\qquad
H(w)=\max\{1-\langle e_0,w\rangle,0\},\quad
g(t)=H(e_0+t e_1).
\]

1. **Objects:** A single ambient function H:Plane→R and its distinct composed scalar function g:R→R on the specified line, using the exact canonical e0,e1.
2. **Quantifiers/order:** Three closed conjuncts. The first two use the same plane-domain function; the third binds a real scalar t in a composition. No arbitrary vector or direction is quantified.
3. **Assumptions:** None. Canonical basis identities come from the supplied aliases, not an extra orthogonality premise.
4. **Conclusion:** Ambient nondifferentiability at (1,3), ambient differentiability at (0,1), and scalar differentiability at t=0 of the line-restricted function.
5. **Constants/boundaries:** At (1,3) the margin is 1; at e1 it is 0. Along the entire line e0+t e1 the margin remains 1 and g is identically zero. Scalar t=0 corresponds to e0=(1,0), not to the first conjunct's point (1,3); the latter corresponds to line parameter t=3.
6. **Information/differentiability:** A derivative along this tangent line is a derivative of a scalar composition, not ambient Fréchet differentiability of H. A constant restriction can be differentiable along the margin boundary even though the plane function has a kink there. No probability or information filtration occurs.
7. **Excluded scope:** Does not assert ambient differentiability at e0 or along the boundary, nor differentiability along every direction, nor a scalar derivative value in its literal conclusion. It must not relocate the scalar test from t=0 to t=3 or identify the two point tests.

## TerminalC005

For any real y and any vector z in the zero-dimensional Euclidean space, the specified function on that space is globally differentiable and equals 1 at every point.

\[
\forall y\in\mathbb R,\ \forall z\in E_0,\quad
Dh_{y,z}\ \land\
\bigl[\forall w\in E_0,\ h_{y,z}(w)=1\bigr],
\qquad h_{y,z}(w)=\max\{1-y\langle z,w\rangle,0\}.
\]

1. **Objects:** E0=EuclideanSpace R (Fin 0), real y, vector z∈E0, and a real-valued function with domain E0.
2. **Quantifiers/order:** Universally quantify y then z; the conclusion conjoins global differentiability with a universal value equality over w∈E0.
3. **Assumptions:** No restriction on y or additional premise on z. The dimension is fixed to zero by the actual type.
4. **Conclusion:** Everywhere ambient differentiability on E0 and constant value 1 there.
5. **Constants/boundaries:** E0 contains its unique zero vector; it is not an empty domain. Thus z=w=0 and the inner product and margin are zero for all y. Margin 1 cannot occur. Constants are threshold 1 and truncation 0.
6. **Information/differentiability:** Differentiability is ambient for the zero-dimensional domain, not a restriction of a separately specified positive-dimensional function. No random quantities or feedback.
7. **Excluded scope:** No positive-dimension assumption may be inserted. This does not assert that the same formula is globally differentiable for arbitrary nonzero vectors in higher-dimensional spaces.

## Completeness and semantic status

All five terminals have complete prose, LaTeX, and seven-slot reconstructions. C002 retains all eight conjuncts and both signed boundary points. C004 distinguishes the plane points from the scalar line parameter and the corresponding differentiability predicates. C003 and C005 explicitly retain their allowed degenerate inputs.

No unresolved type or semantic-context issue was identified in the supplied packet. This is a reading of frozen proposition proposals, not a proof, compilation result, source-identification exercise, or source/proof acceptance verdict.

