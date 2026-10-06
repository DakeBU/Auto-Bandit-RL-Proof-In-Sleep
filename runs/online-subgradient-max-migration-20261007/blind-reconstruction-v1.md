# Blind neutral reconstruction

Actor task: `/root/neutral_finite_family_decoder`.

The only task-content file read was `blind-packet-v1.md`. This report uses its neutral definitions, headers and supplied compiled public types. No proof bodies, source identities, repository searches, previous verdicts or histories were consulted. The actor also received execution instructions and general environment/user context; therefore this is a restricted-input reconstruction, not a claim of an empty runtime context. No source identity is inferred. GPT-6 Astra / medium is the requested configuration, not independently verified runtime model/effort evidence. This report supplies no external-human certification, source acceptance, chapter acceptance or Goal acceptance.

## Definitions, ownership, and binder scope

Write \(\overline{\mathbb R}=\mathbb R\cup\{-\infty,+\infty\}\), and write \(\langle\cdot,\cdot\rangle\) for the real inner product. Real quantities in extended-real inequalities are coerced to \(\overline{\mathbb R}\). Unless stated otherwise, theorem targets quantify over a real inner-product space \(E\) with its compatible norm and additive normed group. This does not assume finite dimension or completeness. All seventeen supplied compiled theorem types retain both these section classes, including targets whose mathematical assertion needs less structure.

Two owned definitions:

- **M:** \(M_f(x)=\max_{i\in I}f_i(x)\), for a finite, nonempty index type \(I\). The actual printed type of M quantifies over **arbitrary type E**, with no normed-group or inner-product instances. It uses an actual nonempty finite supremum, not a supremum over an empty family or an assumed bound.
- **U:** \(U_f(x)=\{g\in E:\exists i\in I,\ f_i(x)=M_f(x)\land g\in S(f_i,x)\}\). Its actual printed type requires `NormedAddCommGroup E`, `InnerProductSpace ℝ E`, `Fintype I`, and `Nonempty I`. It includes every support vector of every attaining component; it is not a chosen component, selected vector, or convex hull.

Five borrowed contexts:

- **S:** \(S(f,x)=\{g\in E:\forall y\in E,\ f(x)+\langle g,y-x\rangle\le f(y)\}\). Its intrinsic operations require subtraction and real inner product, supplied by the stated normed-group and real inner-product structure. Its test is over all ambient points, even points where f is infinite.
- **P:** \(P(f)\iff (\forall x\in E,\ f(x)\ne-\infty)\land(\exists x\in E)(\exists r\in\mathbb R)\ f(x)=r\). This predicate is intrinsically meaningful for arbitrary E; it has no intrinsic norm or linear-space requirement. It does not require global finite-valuedness.
- **D:** \(D(f)=\{x\in E:f(x)<+\infty\}\). Intrinsically arbitrary E; it excludes top but **does not itself exclude bottom**.
- **Q:** \(Q(f)=\{(x,r)\in E\times\mathbb R:f(x)\le r\}\). Intrinsically arbitrary E; epigraph heights are real, not extended real.
- **C:** \(C(f)\iff Q(f)\text{ is convex over }\mathbb R\). This uses the real linear/convex structure on \(E\times\mathbb R\), furnished here by the ambient real inner-product structure. It asserts epigraph convexity, not epigraph closedness or continuity. Unlike M/U, exact compiled public types for the five borrowed definitions were not printed separately; descriptions of their intrinsic operations are not independent kernel-binder attestations.

In formulas below \(\operatorname{co}\) denotes the ordinary real convex hull, without closure. \(\rho(z)=z.\mathrm{toReal}\) denotes the exact extended-real-to-real operation; its interpretation as the finite real value is used only when both infinities are excluded. Write \(A\Join B=\operatorname{convexJoin}_{\mathbb R}(A,B)\), the union of segments joining their points. Each seven-slot reconstruction below is a separate target, not a claim of seventeen independent source results.

## C01

**Natural language / LaTeX.** Every support vector of any component attaining the finite maximum at x supports the maximum at x:
\[U_f(x)\subseteq S(M_f,x).\]

1. **Objects/spaces:** Ambient real inner-product E; extended-real family \(f:I\to(E\to\overline{\mathbb R})\); M, U, S as defined.
2. **Quantifiers:** Every finite nonempty I, every f and x; inclusion applies to every g in U.
3. **Assumptions:** Only the ambient structure and finite nonempty indexing; membership in U supplies attainment and component support.
4. **Conclusions:** The same g satisfies the maximum's supporting inequality for every ambient y.
5. **Constants:** No numeric bounds or additional constants; maximum coefficients are not involved.
6. **Information/probability:** Deterministic universal implication; no information filtration, probability or oracle.
7. **Boundaries:** No properness, convexity, continuity, common-domain membership or finite dimension is assumed. This is one-way inclusion only; extended-real values are allowed.

## C02

**Natural language / LaTeX.** At every x, some component actually attains the finite nonempty maximum:
\[\exists i\in I,\quad M_f(x)=f_i(x).\]

1. **Objects/spaces:** Same ambient theorem structure and finite nonempty extended-real family.
2. **Quantifiers:** For all I, f and x, there exists i; i may depend on f and x.
3. **Assumptions:** Finite nonempty I only beyond ambient instances.
4. **Conclusions:** Exact equality with a component value.
5. **Constants:** None.
6. **Information/probability:** Deterministic existence, with no algorithmic, measurable or random selection guarantee.
7. **Boundaries:** No finiteness of the maximum's value; it may be either infinity. M itself needs less structure than this compiled theorem retains.

## C03

**Natural language / LaTeX.** For proper components and a point in every component domain, the maximum has a finite real value:
\[(\forall i\ P(f_i))\land(\forall i\ x\in D(f_i))\Longrightarrow\exists a\in\mathbb R,\ M_f(x)=a.\]

1. **Objects/spaces:** Ambient E, finite nonempty I, family f, point x.
2. **Quantifiers:** Every such family and x satisfying the premises; some real a.
3. **Assumptions:** Every P includes global absence of bottom and its own finite witness; all components at x lie below top.
4. **Conclusions:** M at x equals the real embedding of a.
5. **Constants:** a is existential and data-dependent; no bound on it is supplied.
6. **Information/probability:** Deterministic existence; no sampling.
7. **Boundaries:** Neither global finiteness nor convexity/continuity is asserted; the components' separate properness witnesses need not coincide with one another.

## C04

**Natural language / LaTeX.** If f never equals bottom and x is in its domain, extended-real support at x is equivalent to the real supporting inequality tested only where f is not top:
\[g\in S(f,x)\iff\forall y\in E,\ f(y)\ne+\infty\Rightarrow \rho(f(x))+\langle g,y-x\rangle\le\rho(f(y)).\]

1. **Objects/spaces:** Ambient E, one extended-real f, x and g.
2. **Quantifiers:** Every f with the global premise; every eligible x and every g; every y on the right.
3. **Assumptions:** \(\forall y, f(y)\ne-\infty\), and \(f(x)<+\infty\).
4. **Conclusions:** The stated equivalence; the real inequality needs checking only at non-top y.
5. **Constants:** None; rho is the exact toReal operation, not a free choice of representative.
6. **Information/probability:** Deterministic equivalence.
7. **Boundaries:** S still universally tests all ambient y. No convexity, continuity, finite dimension or separately supplied P is required. Global no-bottom is stronger than no-bottom merely at x.

## C05

**Natural language / LaTeX.** The supporting-vector set at a finite point is convex when f never equals bottom:
\[(\forall y, f(y)\ne-\infty)\land x\in D(f)\Longrightarrow \operatorname{Convex}_{\mathbb R}S(f,x).\]

1. **Objects/spaces:** Ambient E, f, x, set S(f,x).
2. **Quantifiers:** Every f and eligible x; convexity applies to any two vectors in S and any nonnegative real convex weights.
3. **Assumptions:** Global absence of bottom and domain membership at x.
4. **Conclusions:** All real convex combinations of members remain in S.
5. **Constants:** Convex weights are nonnegative and sum to one; no norm bound.
6. **Information/probability:** Deterministic set property.
7. **Boundaries:** f need not itself be convex or continuous; convexity of S does not assert it is nonempty or compact.

## C06

**Natural language / LaTeX.** Continuity of an extended-real f at a point below top makes that point interior to its domain:
\[x\in D(f)\land\operatorname{ContinuousAt}(f,x)\Longrightarrow x\in\operatorname{int}D(f).\]

1. **Objects/spaces:** Ambient E and its topology; f maps to EReal with its topology.
2. **Quantifiers:** Every f and x satisfying both premises.
3. **Assumptions:** f(x) is below top; ambient EReal continuity at x.
4. **Conclusions:** Some ambient open neighborhood of x is contained in D(f).
5. **Constants:** No explicit neighborhood radius or quantitative modulus is supplied.
6. **Information/probability:** Deterministic local topological assertion.
7. **Boundaries:** f(x) may equal bottom. No properness, convexity, finite dimension or relative-domain continuity assumption is substituted.

## C07

**Natural language / LaTeX.** The maximum of proper components never takes bottom:
\[\forall i\ P(f_i)\Longrightarrow\forall y\in E,\ M_f(y)\ne-\infty.\]

1. **Objects/spaces:** Ambient E, finite nonempty I, family f.
2. **Quantifiers:** All such f and every y.
3. **Assumptions:** P for every component.
4. **Conclusions:** Absence of bottom everywhere for M.
5. **Constants:** None.
6. **Information/probability:** Deterministic global assertion.
7. **Boundaries:** Does not by itself establish P(M): a common finite point is not supplied. Top remains possible, and no convexity is required.

## C08

**Natural language / LaTeX.** Under component properness and common-domain membership at x, the convex hull of active supports supports the maximum:
\[(\forall i\ P(f_i))\land(\forall i\ x\in D(f_i))\Longrightarrow\operatorname{co}U_f(x)\subseteq S(M_f,x).\]

1. **Objects/spaces:** Ambient E, finite nonempty I, family f and x.
2. **Quantifiers:** Every eligible family and x; every vector in the hull.
3. **Assumptions:** Component properness and common-domain point.
4. **Conclusions:** Inclusion of the full ordinary convex hull in S(M,x).
5. **Constants:** Hull uses real nonnegative weights summing to one; no uniform bound.
6. **Information/probability:** Deterministic inclusion, without random or algorithmic construction.
7. **Boundaries:** No component convexity, continuity or finite dimension. No reverse inclusion or closure is stated.

## C09

**Natural language / LaTeX.** The support set at a finite point of a function with no bottom values is closed:
\[(\forall y, f(y)\ne-\infty)\land x\in D(f)\Longrightarrow\operatorname{IsClosed}(S(f,x)).\]

1. **Objects/spaces:** Ambient norm topology on E; f and x.
2. **Quantifiers:** Every f and x obeying the premises.
3. **Assumptions:** Global no-bottom and x in D.
4. **Conclusions:** S(f,x) is closed in E.
5. **Constants:** None.
6. **Information/probability:** Deterministic topological conclusion.
7. **Boundaries:** No convexity or continuity of f, finite dimension, boundedness or nonemptiness is claimed.

## C10

**Natural language / LaTeX.** In finite dimension, the support set of a proper epigraph-convex function at an interior-domain point is compact:
\[P(f)\land C(f)\land x\in\operatorname{int}D(f)\Longrightarrow\operatorname{IsCompact}(S(f,x)).\]

1. **Objects/spaces:** Finite-dimensional real inner-product E; f and x.
2. **Quantifiers:** Every such E, proper convex f, and interior-domain x.
3. **Assumptions:** FiniteDimensional ℝ E, P(f), C(f), and ambient interior membership.
4. **Conclusions:** Compactness of S(f,x).
5. **Constants:** No radius or numerical bound is provided.
6. **Information/probability:** Deterministic compactness.
7. **Boundaries:** Positive dimension and separately assumed continuity are absent. Compactness alone is not an explicit nonemptiness statement, and this target does not cover arbitrary boundary points.

## C11

**Natural language / LaTeX.** The convex join of two compact sets is compact:
\[\operatorname{IsCompact}(s)\land\operatorname{IsCompact}(t)\Longrightarrow\operatorname{IsCompact}(s\Join t).\]

1. **Objects/spaces:** Ambient E; arbitrary subsets s and t.
2. **Quantifiers:** Every s,t satisfying compactness.
3. **Assumptions:** Compactness of each set; ambient compiled theorem structure.
4. **Conclusions:** Compactness of the union of segments joining s to t.
5. **Constants:** Segment parameter runs over the real unit interval.
6. **Information/probability:** Deterministic set-topological assertion.
7. **Boundaries:** No finite dimension, convexity or nonemptiness of s or t. The target is convexJoin, not the convex hull of an arbitrary compact set.

## C12

**Natural language / LaTeX.** The convex hull of a union of finitely many compact convex sets is compact:
\[(\forall i\in F,\operatorname{Convex}_{\mathbb R}s_i)\land(\forall i\in F,\operatorname{IsCompact}s_i)\Longrightarrow\operatorname{IsCompact}\!\left(\operatorname{co}\bigcup_{i\in F}s_i\right).\]

1. **Objects/spaces:** Ambient E; arbitrary index type I, family of subsets s, finite set F of indices.
2. **Quantifiers:** Every I, s and F; assumptions only for indices in F.
3. **Assumptions:** Each selected set is convex and compact. There is no `Fintype I` or `Nonempty I` binder here.
4. **Conclusions:** Compactness of the ordinary convex hull of the selected union.
5. **Constants:** F has no specified size; hull coefficients are real convex weights.
6. **Information/probability:** Deterministic assertion; finite index selection is input.
7. **Boundaries:** F can be empty. No finite-dimensional E, nonempty member sets, or conditions on indices outside F are required. Dropping convexity of member sets is not warranted by this target.

## C13

**Natural language / LaTeX.** In finite dimension, for a finite nonempty proper convex family continuous at a common-domain x, the hull of all active supports is compact:
\[(\forall i,\ P(f_i)\land C(f_i)\land x\in D(f_i)\land\operatorname{ContinuousAt}(f_i,x))\Longrightarrow\operatorname{IsCompact}(\operatorname{co}U_f(x)).\]

1. **Objects/spaces:** Finite-dimensional real inner-product E; finite nonempty I; f and x.
2. **Quantifiers:** Every such family and point; all components satisfy all premises.
3. **Assumptions:** Component properness, epigraph convexity, common-domain membership and ambient EReal continuity at x.
4. **Conclusions:** Compactness of the ordinary convex hull of U at x.
5. **Constants:** No numerical bound or uniform continuity modulus.
6. **Information/probability:** Deterministic compactness; no selected active branch is input.
7. **Boundaries:** Continuity applies even to inactive components. No relative-domain replacement, closure added to the hull, or equality with S(M,x) is stated here.

## C14

**Natural language / LaTeX.** At a point with finite f-value, continuity into EReal implies continuity of its toReal composition:
\[f(x)\ne+\infty\land f(x)\ne-\infty\land\operatorname{ContinuousAt}(f,x)\Longrightarrow\operatorname{ContinuousAt}(\rho\circ f,x).\]

1. **Objects/spaces:** Ambient E; extended-real f and real-valued composition rho∘f.
2. **Quantifiers:** Every f and x with the listed local premises.
3. **Assumptions:** Both infinite values excluded at x, plus EReal continuity there.
4. **Conclusions:** Real-valued continuity of y↦(f(y)).toReal at x.
5. **Constants:** None; rho is a fixed operation.
6. **Information/probability:** Deterministic local statement.
7. **Boundaries:** Does not assume P, global finiteness, convexity or finite dimension. The hypotheses exclude infinities at x, not explicitly at every other y.

## C15

**Natural language / LaTeX.** A support of the maximum at x has no greater inner product along y−x than a support at y of a component attaining the maximum at y:
\[g\in S(M_f,x),\quad k\in S(f_i,y),\quad M_f(y)=f_i(y)\Longrightarrow\langle g,y-x\rangle\le\langle k,y-x\rangle,\]
with the properness and finite-point premises detailed below.

1. **Objects/spaces:** Ambient E; finite nonempty I; family f; x,y,g,k∈E and i∈I.
2. **Quantifiers:** Every such family, points, index and vectors satisfying the premises; no existential choice is asserted.
3. **Assumptions:** All components proper; x in every D(f_j); y in D(f_i); i attains M at y; g supports M at x; k supports f_i at y.
4. **Conclusions:** The displayed inequality, with the same displacement y−x on both sides.
5. **Constants:** Coefficient one on both inner products; no error term or norm factor.
6. **Information/probability:** Deterministic relation for supplied supports and attainment.
7. **Boundaries:** i is active at y, not necessarily at x. Only y∈D(f_i) is an explicit domain premise at y. No convexity, continuity or finite dimension is assumed; no support-existence result is asserted.

## C16

**Natural language / LaTeX.** Under the finite-dimensional proper convex continuous-family hypotheses, every support g of the maximum and every direction d admit an active component support k whose inner product in that direction is at least g's:
\[\forall g\in S(M_f,x),\ \forall d\in E,\ \exists k\in U_f(x),\quad\langle g,d\rangle\le\langle k,d\rangle.\]

1. **Objects/spaces:** Finite-dimensional real inner-product E; finite nonempty I; family f, common point x, vectors g,d,k.
2. **Quantifiers:** For all eligible f,x, for every g and every d, if g∈S(M,x), some k exists. k may depend on f,x,g,d.
3. **Assumptions:** Every component proper and epigraph-convex; x in every component domain; every component ambient EReal-continuous at x; membership of g in S(M,x).
4. **Conclusions:** k lies in U, so some attaining i has k∈S(f_i,x), and the directional inequality holds.
5. **Constants:** Exact coefficient-one inequality; no additive tolerance, normalized direction or nonzero-direction requirement.
6. **Information/probability:** Deterministic existence; no computable or measurable selection guarantee.
7. **Boundaries:** The witness is an actual active support, not merely a hull vector. The conclusion is not one common k dominating all directions; d=0 is allowed. It is not assumed as a premise and does not identify a maximizing directional derivative.

## C17

**Natural language / LaTeX.** In finite dimension, the support set of a finite nonempty maximum at a common finite point equals the ordinary convex hull of every active component's support set, when all components are proper, epigraph-convex and ambient EReal-continuous at that point:
\[S(M_f,x)=\operatorname{co}U_f(x)
=\operatorname{co}\!\left(\bigcup_{\substack{i\in I\\ f_i(x)=M_f(x)}}S(f_i,x)\right).\]

1. **Objects/spaces:** Finite-dimensional real inner-product E, including dimension zero; finite nonempty I; extended-real family f; x∈E.
2. **Quantifiers:** Every such family and x under the premises. Equality means for every candidate g∈E, membership in S(M,x) is equivalent to membership in the hull.
3. **Assumptions:** For every i, P(f_i), C(f_i), x∈D(f_i), and ContinuousAt(f_i,x) in the ambient E-to-EReal topology.
4. **Conclusions:** Full equality, hence both inclusions, of the maximum's supporting-vector set and the ordinary real convex hull of U.
5. **Constants:** Exact equality, without tolerance; convex weights are real, nonnegative and sum to one. No extra boundedness constant.
6. **Information/probability:** Deterministic set equality; no feedback protocol, probability, regret, algorithmic decomposition or measurable-selection statement.
7. **Boundaries:** No closed-hull replacement, supplied decomposition, assumed direction witness, relative-domain continuity, global finite-valuedness, positive dimension or independent closedness/boundedness premise. In particular, the weaker assumptions sufficient for C01/C08 are not the complete hypotheses of this equality.

## Comparison and limits

The supplied neutral headers and supplied compiled types agree in the conclusion and premise scopes reconstructed above; no concrete mismatch was found within that supplied material. The compiled types retain normed-group and inner-product structure for all seventeen targets, while M itself is explicitly structure-free on E. C12 has an arbitrary index type and a finite selected subset, not a finite nonempty index-type assumption. C06 permits a bottom value at the point. C16 has direction-dependent existential witnesses. These distinctions are material and have been preserved.

Exact standalone kernel binders of borrowed S/P/D/Q/C are not printed; their defining operations are fully supplied. No actual compilation or verification of the packet provenance was performed by this decoder. The source-to-neutral mapping, proof validity, source premise fidelity, declaration ownership outside the packet, and any source/chapter/Goal acceptance remain outside this reconstruction. The seventeen targets are seventeen packet obligations, not seventeen independently identified source results.