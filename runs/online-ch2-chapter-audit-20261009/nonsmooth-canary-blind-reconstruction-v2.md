# Neutral canary reconstruction v2

Actor /root/osd_blind; requested GPT-6 Astra / medium. Runtime model and effort are not independently attested. This automated actor has prior staged decoder history, including earlier related statements; no absolute blindness, human review, or external independence is claimed. Only the current v2 packet and accompanying JSON were read in this task. All reconstructions below concern proposed types, not their proof, compilation, or source acceptance.

## Shared notation

Plane is EuclideanSpace R (Fin 2), the canonical real Euclidean plane. The exact supplied aliases are e0=(1,0) and e1=(0,1). On R the real inner product is ordinary multiplication. Let Df(x) mean ordinary ambient real Fréchet differentiability at x, and Df mean differentiability at every point of the domain of f. Convexity below is on the entire ambient space. E0 denotes EuclideanSpace R (Fin 0), which has one point, its zero vector.

## TerminalC001

The real function f(w)=|w−10| is globally convex, fails to be differentiable at 10, and is differentiable at 9 and 11.

\[
\operatorname{Convex}_{\mathbb R}(f)
\land\neg Df(10)\land Df(9)\land Df(11),
\qquad f(w)=|w-10|.
\]

1. **Objects:** One fixed real-valued scalar function, the absolute value centered at 10.
2. **Quantifiers/order:** Closed four-part conjunction. w is the bound argument of each function expression; no external parameters or premises.
3. **Assumptions:** None beyond the stated real domain and formula.
4. **Conclusion:** Global convexity and three pointwise differentiability tests, with failure at the center and success at both supplied off-center points.
5. **Constants/boundaries:** Center 10 and test points 9 and 11. The equality-to-center boundary is tested explicitly. No variable horizon or denominator.
6. **Information/differentiability:** Deterministic ambient scalar Fréchet differentiability, with global convexity but pointwise derivative tests; no probability or feedback.
7. **Excluded scope:** No derivative values, subgradients, or full all-point characterization is literally asserted here. Convexity does not mean differentiability at every point.

## TerminalC002

For fixed scalar factors 2 and −2 and fixed real feature 3, the two functions f+(w)=max{1−6w,0} and f−(w)=max{1+6w,0} are globally convex. They fail differentiability at 1/6 and −1/6 respectively, are both differentiable at zero, and neither is globally differentiable. All eight assertions are retained separately.

\[
\begin{aligned}
&\operatorname{Convex}_{\mathbb R}(f_+)
\land\operatorname{Convex}_{\mathbb R}(f_-)\\
&\land\neg Df_+(1/6)
\land\neg Df_-(-1/6)\\
&\land Df_+(0)
\land Df_-(0)\\
&\land\neg Df_+
\land\neg Df_-,\\
&f_+(w)=\max\{1-2\langle3,w\rangle,0\}=\max\{1-6w,0\},\\
&f_-(w)=\max\{1-(-2)\langle3,w\rangle,0\}=\max\{1+6w,0\}.
\end{aligned}
\]

1. **Objects:** Two fixed functions R→R, with identical feature 3 and distinct signed scalar factors.
2. **Quantifiers/order:** Closed eight-part conjunction: two convexities, two boundary failures, two differentiability tests at zero, then two failures of the global property. There is no universal label or feature quantifier.
3. **Assumptions:** No premises; the parameters are concrete nonzero reals. They are not restricted to a binary-label type.
4. **Conclusion:** Both convexities, each function's own boundary failure, both off-boundary pointwise successes, and both failures of differentiability everywhere.
5. **Constants/boundaries:** The margins 6w and −6w equal 1 at +1/6 and −1/6 respectively. At zero both margins are 0 and values are 1. Denominator 6 is fixed and nonzero. The affine positive branch lies below 1/6 for f+ and above −1/6 for f−.
6. **Information/differentiability:** No randomness. Pointwise differentiability at zero is compatible with lack of global differentiability. Global failure is not everywhere failure.
7. **Excluded scope:** No claim for arbitrary positive or negative parameters, no derivative formula, and no replacement of either boundary by the other. All eight conjuncts refer to their displayed functions.

## TerminalC003

For arbitrary real y,z, the function with scalar factor zero and feature z is globally differentiable, and the function with scalar factor y and feature zero is globally differentiable. At every real w both functions equal 1.

\[
\begin{aligned}
\forall y\in\mathbb R,\ \forall z\in\mathbb R,\quad&
Dg_z\land Dh_y
\land[\forall w\in\mathbb R,\ g_z(w)=1\land h_y(w)=1],\\
&g_z(w)=\max\{1-0\langle z,w\rangle,0\},\\
&h_y(w)=\max\{1-y\langle0,w\rangle,0\}.
\end{aligned}
\]

1. **Objects:** Two distinct scalar functions, one with its label-like scalar fixed at zero and the other with its feature fixed at zero.
2. **Quantifiers/order:** y then z are universally quantified. Two global differentiability claims precede a universally quantified w whose scope contains both equalities.
3. **Assumptions:** No sign or nonzero restrictions on y,z; either or both may vanish.
4. **Conclusion:** Both global differentiability properties and both constant-one identities for every input.
5. **Constants/boundaries:** Both margins are identically zero, so no margin-1 point occurs. Threshold 1 and truncation 0 remain as specified, yielding value 1.
6. **Information/differentiability:** Deterministic global differentiability on R, not only a test at zero or another selected point.
7. **Excluded scope:** This is not a statement about global differentiability of the general nondegenerate function max{1−y⟨z,w⟩,0}. No hidden nonzero-label restriction or derivative formula is added.

## TerminalC004

The plane function H(w)=max{1−⟨e0,w⟩,0}=max{1−w0,0} is not ambient differentiable at x* = e0+3e1=(1,3), but is ambient differentiable at e1=(0,1). Its scalar restriction along t↦e0+(3+t)e1 is differentiable at t=0. That scalar parameter value corresponds exactly to the same plane point x* tested for ambient nondifferentiability.

\[
\neg DH(x_*)\land DH(e_1)\land Dg(0),
\quad
x_*=e_0+3e_1,\quad
H(w)=\max\{1-\langle e_0,w\rangle,0\},
\quad
g(t)=H(e_0+(3+t)e_1).
\]

1. **Objects:** One function H:Plane→R, the fixed point x*=(1,3), the other test point e1=(0,1), and the scalar composition g:R→R.
2. **Quantifiers/order:** A closed three-part conjunction. w is a plane argument in the first two clauses; t is a real argument in the third. There is no quantifier over arbitrary directions or paths.
3. **Assumptions:** None. The exact canonical aliases supply the coordinate interpretation and orthogonality.
4. **Conclusion:** Failure of ambient Fréchet differentiability at x*, success at e1, and success of scalar differentiability of g at zero.
5. **Constants/boundaries:** The affine line is based at x*=e0+3e1, since at t=0 it equals e0+3e1. At all t its first coordinate is 1, so its margin is 1 and g(t)=0. At e1 the margin is 0. The shift 3+t is essential to the point correspondence.
6. **Information/differentiability:** The third property concerns a tangent-line restriction at the same base point where the first rejects ambient differentiability. A scalar composition can be differentiable even though the original plane function is not ambient differentiable there. No probability or information structure is involved.
7. **Excluded scope:** Tangential differentiability is not ambient differentiability and does not assert differentiability along every direction. The scalar base point must not be read as e0 or as t=3. No explicit derivative value is part of the target, despite the restriction's constant value.

## TerminalC005

For any real scalar y and any vector z in the zero-dimensional Euclidean space E0, the function w↦max{1−y⟨z,w⟩,0} is globally differentiable on E0 and equals 1 at every point there.

\[
\forall y\in\mathbb R,\ \forall z\in E_0,\quad
Dh_{y,z}\land[\forall w\in E_0,\ h_{y,z}(w)=1],
\qquad h_{y,z}(w)=\max\{1-y\langle z,w\rangle,0\}.
\]

1. **Objects:** The concrete zero-dimensional space E0, arbitrary real y, z∈E0, and h_{y,z}:E0→R.
2. **Quantifiers/order:** y then z are universally quantified; the global differentiability assertion is conjoined with an all-w value identity.
3. **Assumptions:** Only the stated types. There is no nonzero-vector or positive-dimension premise.
4. **Conclusion:** Differentiability at every ambient point of E0 and value 1 at every such point.
5. **Constants/boundaries:** E0 is a singleton rather than an empty set. z and w must be zero; hence the margin is 0 for every real y, including negative and zero y. Margin 1 cannot occur.
6. **Information/differentiability:** Global differentiability is with respect to this zero-dimensional ambient domain, not a positive-dimensional ambient function with a restricted test set. No probability, observations, or algorithm.
7. **Excluded scope:** Does not extend to arbitrary nonzero features in positive dimension. No additional assumptions or derivative values are supplied.

## Completion and limits of this reconstruction

All five current v2 types are reconstructed in full prose, LaTeX, and seven slots. No unresolved type or semantic-context question was identified. In particular, C004 explicitly matches the ambient kink point (1,3) to scalar parameter zero on its shifted tangent line. C002 preserves all eight assertions and both signed boundaries; C003 and C005 retain the constant-function cases.

These are interpretations of proposition proposals. No proof, compiler, source identity, source-fidelity review, or acceptance judgment was used or produced.

