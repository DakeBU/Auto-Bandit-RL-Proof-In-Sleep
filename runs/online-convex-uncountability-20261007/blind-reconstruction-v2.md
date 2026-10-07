# Source-blind reconstruction v2

## Scope and context repair

The substantive input for this round is exclusively `blind-packet-v2.md`. The packet reports that the earlier standalone context did not resolve `DifferentiableAt`, and adds `Mathlib.Analysis.Calculus.Deriv.Abs` to supply that existing symbol. This is a context-only repair: the displayed neutral definition Q and targets P1/P2 retain their objects, quantifiers, and logical structure. This report reconstructs the displayed v2 targets afresh. It does not independently run the type probe or certify its log.

The supplied output elaborates target propositions, not theorem proof bodies. No proof, source identity, surrounding repository, or source-review artifact was inspected in this round. Requested settings are GPT-6 Astra / medium; these are not runtime-attested. No source, package, chapter, or Goal acceptance judgment is made.

## Neutral definition

Write E for the real two-dimensional Euclidean L2 plane, identified with R^2 using coordinates x_0 and x_1. The function is

\[
Q:E\to\mathbb R,\qquad Q(x_0,x_1)=|x_0|.
\]

This is an actual everywhere-real-valued function. The elaborated expression `x.ofLp 0` accesses its first coordinate, not its second. Lean index 1 specifies the second coordinate, so `PiLp.single 2 1 1` is the vector (0,1). No extended-real projection occurs.

## P1

The particular closed segment joining (0,0) to (0,1) is uncountable:

\[
\neg\operatorname{Countable}(S),\qquad
S=[(0,0),(0,1)]
 =\{(0,t):t\in\mathbb R,\ 0\le t\le1\}.
\]

Here countable means at most countable, including finite sets.

### Seven semantic slots

1. **Ambient objects and types:** The scalar field is R and the space is E with its actual two-dimensional Euclidean L2 structure. The two endpoints are fixed vectors (0,0) and (0,1).
2. **Quantifiers and scope:** P1 is a closed proposition about one fixed set S. It does not quantify over arbitrary segments or choose a function. The parameter t above is bound only within the coordinate description of S.
3. **Domain and membership:** Membership in S means being a nonnegative real convex combination a(0,0)+b(0,1), where a+b=1. Equivalently the first coordinate is zero and the second lies in [0,1]. Both endpoints are included.
4. **Hypotheses and structural conditions:** There is no implication or list of conditional assumptions. The real field, ambient plane, fixed endpoints, and closed-segment construction are embedded in the proposition.
5. **Claim and logical structure:** The sole predicate is the negation of `Set.Countable` on S. Thus S is not finite or countably infinite; it is uncountable. No conjunct about Q appears.
6. **Analytic and operational interpretation:** P1 has no differentiability assertion, restricted derivative, stochastic quantity, algorithm, or feedback structure. The definition Q is irrelevant to the displayed P1 expression.
7. **Strength and boundaries:** Uncountability is the entire asserted cardinal property. No exact cardinality, measure, almost-everywhere, probability, or connection to a nondifferentiability set is encoded.

## P2

The specified function Q is convex on the whole real plane, and the set of points where this same Q fails ambient real Frechet differentiability is uncountable:

\[
\operatorname{ConvexOn}_{\mathbb R}(E,Q)
\quad\land\quad
\neg\operatorname{Countable}(N_Q),
\qquad
N_Q=\{x\in E:\neg\operatorname{DifferentiableAt}_{\mathbb R}(Q,x)\}.
\]

The first conjunct says that the domain E is convex and that

\[
\forall x,y\in E\;\forall a,b\in\mathbb R,\quad
(a\ge0\land b\ge0\land a+b=1)
\Longrightarrow Q(ax+by)\le aQ(x)+bQ(y).
\]

At x, ambient real Frechet differentiability means the existence of a continuous real-linear map L:E->R such that

\[
\lim_{\substack{h\to0\\h\ne0}}
\frac{|Q(x+h)-Q(x)-L(h)|}{\|h\|_2}=0.
\]

Failure of that existence condition defines membership in N_Q.

### Seven semantic slots

1. **Ambient objects and types:** E is the real Euclidean L2 plane; Q:E->R is the fixed function taking the absolute value of the first coordinate. Both convexity and differentiability are over the real scalar field.
2. **Quantifiers and scope:** The outer structure is a conjunction for this exact Q, with no outer existential quantifier selecting another function. The convexity condition quantifies over all x,y in E and nonnegative real weights summing to one. The set-builder binds its query x over E.
3. **Domain and membership:** `Set.univ` is the whole plane. N_Q also ranges over the whole plane, and membership means failure of `DifferentiableAt` at that point. Neither the domain of convexity nor the nondifferentiability query set is restricted to S.
4. **Hypotheses and structural conditions:** P2 has no external premise or implication. `ConvexOn` asserts convexity of the domain and the convex-combination inequality. The domain is already the full real vector space; Q is finite-valued everywhere.
5. **Claim and logical structure:** Both conjuncts are asserted together. The inner negation denies differentiability pointwise; the outer negation denies at-most-countability of the set of such points. Convexity is not an implication premise from which uncountability is stated to follow for arbitrary functions.
6. **Analytic and operational interpretation:** Differentiability is ambient real Frechet differentiability, testing perturbations from all directions in E. It is not a derivative within the closed segment, a derivative of the function restricted to that segment, or merely a directional derivative. There is no probability model, sampling process, algorithm, or feedback contract.
7. **Strength and boundaries:** The set N_Q is asserted to be uncountable. The target does not explicitly characterize it by a coordinate equation, identify it with S, supply its exact cardinality, or give a measure-zero or almost-everywhere conclusion. An elaborated proposition is not a proof-body compilation result.

## Cross-target boundary

P1 is solely a cardinal statement about S. P2 pairs convexity of the fixed Q with uncountability of its ambient nondifferentiability set. The targets as displayed contain no assertion that S is contained in N_Q and no proof-dependency claim linking P1 to P2. No source identity or acceptance conclusion is inferred from their mathematical form.