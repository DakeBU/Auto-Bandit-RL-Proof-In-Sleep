# Source-blind reconstruction v1

## Scope and evidentiary boundary

The only substantive input read was `blind-packet-v1.md`. This report decodes the neutral definition and the two displayed prospective propositions independently. The packet supplies elaboration output for target propositions; it supplies no compiled theorem bodies. This report does not verify proofs, infer a source, or issue source-acceptance, chapter-completion, or Goal-completion judgments.

Requested actor settings: GPT-6 Astra, medium reasoning effort. These are requested settings only and are not runtime-attested.

## Neutral definition context

Let E = EuclideanSpace over the reals indexed by Fin 2, the real two-dimensional Euclidean L2 space. Identify x in E with (x_0, x_1) in R^2. Define the everywhere-defined real-valued function

\[
Q:E\to\mathbb R,\qquad Q(x_0,x_1)=|x_0|.
\]

Lean coordinate 0 is the first coordinate; coordinate 1 is the second. The vector `PiLp.single 2 1 1` is e_1 = (0,1). The neutral elaborated body `fun x => |x.ofLp 0|` accesses the same first coordinate. There is no extended-real value, coercion from extended reals, or projection of an extended-real-valued function.

## P1: independent reconstruction

The closed line segment from the origin to (0,1) in E is not at most countable:

\[
\neg\operatorname{Countable}\bigl([0,(0,1)]\bigr).
\]

Equivalently, in ordinary coordinates,

\[
S=\{(0,t)\in\mathbb R^2:0\le t\le1\}
\quad\text{is uncountable.}
\]

### Seven semantic slots

1. **Ambient objects and types:** The ambient space is E, the actual real Euclidean L2 plane; the scalar field is R. The distinguished points are 0 = (0,0) and e_1 = (0,1).
2. **Quantification and scope:** This is a closed proposition about these fixed points and their particular segment. It has no free query point, parameterized endpoint, universal family of segments, or existentially selected function.
3. **Domain and set membership:** The set is the closed real segment. Its members have the form a(0,0) + b(0,1), with a,b >= 0 and a+b=1; equivalently (0,t) with 0<=t<=1. Both endpoints belong to the set.
4. **Hypotheses and structural conditions:** There is no implication with additional hypotheses. The real scalar field, two-dimensional Euclidean space, fixed endpoints, and closed-segment definition are built into the statement.
5. **Asserted relation and logical structure:** The single assertion is negation of `Set.Countable` for S. Countable means at most countable and includes finite sets, so this negation asserts uncountability.
6. **Analytic or operational interpretation:** This proposition has no derivative, convex-function property, random variable, process, algorithm, or feedback rule. Q is not used in P1.
7. **Strength and exclusions:** No exact cardinality is stated, and no measure, almost-everywhere, probability, or differentiability conclusion is stated. In particular, P1 alone does not identify any nondifferentiability set.

## P2: independent reconstruction

The specific function Q(x_0,x_1)=|x_0| is convex on all of E, and the set of points at which this same function is not ambient real Frechet differentiable is not at most countable:

\[
\operatorname{ConvexOn}_{\mathbb R}(E,Q)
\;\land\;
\neg\operatorname{Countable}(N_Q),
\qquad
N_Q=\{x\in E:\neg\operatorname{DifferentiableAt}_{\mathbb R}(Q,x)\}.
\]

Expanding the convexity part, the domain E is convex and, for every x,y in E and every a,b in R with a,b>=0 and a+b=1,

\[
Q(ax+by)\le aQ(x)+bQ(y).
\]

The differentiability predicate refers to existence of an ambient Frechet derivative: a continuous real-linear map L:E->R for which

\[
\lim_{\substack{h\to0\\h\ne0}}
\frac{|Q(x+h)-Q(x)-L(h)|}{\|h\|_2}=0.
\]

Thus N_Q consists of points where no such L exists.

### Seven semantic slots

1. **Ambient objects and types:** E is the real two-dimensional Euclidean L2 plane. The particular function Q:E->R is fixed by the neutral definition above. Its values are finite real numbers everywhere.
2. **Quantification and scope:** The outer logical structure is a conjunction for this one fixed Q. Convexity quantifies over every pair x,y in E and nonnegative real coefficients summing to one. The set-builder binds x over all E. There is no outer existence claim selecting a different function.
3. **Domain and set membership:** Convexity is on `Set.univ`, the entire plane. N_Q is also defined over the entire plane and contains exactly those query points satisfying the negated ambient differentiability predicate. It is not restricted to the segment of P1.
4. **Hypotheses and structural conditions:** No additional conditional hypotheses precede the conjunction. `ConvexOn` includes convexity of the domain together with the convex-combination inequality; the domain here is the full real vector space.
5. **Asserted relation and logical structure:** Both conjuncts must hold: Q is convex on E, and N_Q is not at most countable. The inner negation defines failure of differentiability pointwise; the outer negation denies countability of the resulting set. Neither conjunct is a premise implying the other.
6. **Analytic or operational interpretation:** Differentiability is real Frechet differentiability in the ambient Euclidean plane. Perturbations approach from all ambient directions. It is not differentiability within the displayed segment, differentiability of a one-dimensional restriction, or merely existence of a directional derivative. There is no sampling, probability, algorithm, or feedback semantics.
7. **Strength and exclusions:** The proposition asserts uncountably many points of failure of ambient differentiability. It does not explicitly characterize N_Q by a coordinate equation, equate it with the P1 segment, assert an exact cardinality, or give any measure-zero or almost-everywhere statement. No proof or theorem-body compilation is certified by the elaborated target.

## Relationship between the targets

P1 concerns only the cardinality of a specific closed segment. P2 concerns convexity and the cardinality of an ambient nondifferentiability set for the fixed Q. The displayed targets do not encode a containment connecting those two sets, nor a proof dependency from P1 to P2. This reconstruction makes no such dependency claim.