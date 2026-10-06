# Neutral blind reconstruction v1

Actor task: `/root/neutral_two_function_decoder`.

This report reconstructs only the supplied neutral packet, using its exact definition bodies and actual compiled public types. It does not identify a numbered source, inspect proof bodies, or establish source acceptance. No compilation or tests were run. The requested actor configuration is not runtime-model attestation. No human or external review is claimed.

Notation: \(\overline{\mathbb R}=\mathrm{EReal}\), including \(-\infty,+\infty\); \(\iota:\mathbb R\to\overline{\mathbb R}\) is the canonical embedding. Whenever a real inner product is used, \(E\) has exactly the displayed real normed additive commutative group and inner-product-space structure. No completeness or positive dimension is assumed. Write \(r(z,x)=1-\langle z,x\rangle\), and \(A_{a,b}(y)=\iota(\langle a,y\rangle+b)\). These are report abbreviations, not additional owned declarations.

Every numbered entry below has seven semantic slots. Slots describe the public statements; they do not certify their proofs. In particular, the general structures needed by borrowed definitions are taken from their actual compiled types, which discard unused section parameters.

## TWO owned definitions

### H

1. **Spaces/objects:** A real inner-product space \(E\); \(H:E\to E\to\overline{\mathbb R}\).
2. **Quantifiers/order:** Implicit \(E\) and its two structural instances, then \(z\), then \(x\), both arbitrary vectors.
3. **Assumptions/regularity:** NormedAddCommGroup and InnerProductSpace over the reals only; no finite-dimensional assumption.
4. **Conclusion/content:** \(H(z,x)=\iota(\max\{1-\langle z,x\rangle,0\})\). It embeds the nonnegative real maximum as an extended-real value.
5. **Constants/normalization:** Threshold and intercept are exactly 1; comparison branch is exactly 0; no extra scale or label.
6. **Probability/information:** Deterministic definition; no random variable, filtration, feedback or information restriction.
7. **Boundary:** At \(r=0\), the value is 0. At \(z=0\), the value is 1 for every \(x\). Values are finite; this observation is specific to this body, not to arbitrary EReal functions.

### B

1. **Spaces/objects:** Same real inner-product-space structures; \(B:E\to\mathrm{Bool}\to E\to\overline{\mathbb R}\).
2. **Quantifiers/order:** Implicit \(E\) and instances, then \(z\), Boolean \(i\), and evaluation vector \(y\).
3. **Assumptions/regularity:** No hypotheses on the vectors or Boolean; no finite-dimensional restriction.
4. **Conclusion/content:** \(B(z,i,y)=\iota(\langle (\text{if }i\text{ then }-z\text{ else }0),y\rangle+(\text{if }i\text{ then }1\text{ else }0))\). It is a Boolean family of two affine functions.
5. **Constants/normalization:** False chooses zero slope and zero intercept; true chooses slope \(-z\) and intercept 1. Boolean order is not interchangeable in this definition.
6. **Probability/information:** Boolean is an ordinary index, not a random draw or a decision rule.
7. **Boundary:** Both branches are defined everywhere and finite, including when \(z=0\). There is no data-dependent branch selection in the definition itself.

## SEVEN borrowed definition contexts

### S

1. **Spaces/objects:** Real normed additive commutative group with inner product; \(f:E\to\overline{\mathbb R}\), \(x\in E\); output a subset of \(E\).
2. **Quantifiers/order:** Implicit \(E\) and instances, then \(f,x\); set membership quantifies \(g\), then universally every ambient \(y\).
3. **Assumptions/regularity:** No properness, convexity, finiteness, continuity or domain restriction on \(f\).
4. **Conclusion/content:** \(S(f,x)=\{g\in E:\forall y\in E,\ f(x)+\iota(\langle g,y-x\rangle)\le f(y)\}\). These are full global supporting vectors.
5. **Constants/normalization:** Unit coefficient for the inner product; extended-real addition and order are used exactly as defined.
6. **Probability/information:** Deterministic universal support inequality; no sampling or almost-sure qualification.
7. **Boundary:** Tests all ambient points, not only finite-domain or nearby points. Infinite values remain governed by EReal operations; no local derivative interpretation is inserted.

### P

1. **Spaces/objects:** Any type \(E\); \(f:E\to\overline{\mathbb R}\); output Prop. The compiled type has no norm, group or module instance.
2. **Quantifiers/order:** Implicit \(E\), then \(f\); conjunction of \(\forall x\) with \(\exists x\exists t\in\mathbb R\).
3. **Assumptions/regularity:** No prerequisites on \(f\) or \(E\).
4. **Conclusion/content:** \(P(f)\iff(\forall x\in E,\ f(x)\ne-\infty)\land(\exists x\in E\ \exists t\in\mathbb R,\ f(x)=\iota(t))\).
5. **Constants/normalization:** Excludes exactly bottom globally and requires an exactly real-valued witness; no boundedness constant.
6. **Probability/information:** Pure predicate; no stochastic or information assumptions.
7. **Boundary:** Does not require every value finite and permits top elsewhere. On an empty type the witness cannot exist. Convexity is not part of P.

### D

1. **Spaces/objects:** Any type \(E\), function \(f:E\to\overline{\mathbb R}\); output Set E. No structural instances in the compiled type.
2. **Quantifiers/order:** Implicit \(E\), then \(f\); membership tests each \(x\).
3. **Assumptions/regularity:** No P, convexity or regularity assumption.
4. **Conclusion/content:** \(D(f)=\{x\in E:f(x)<+\infty\}\).
5. **Constants/normalization:** Strict comparison with top, not an inequality with a finite threshold.
6. **Probability/information:** Deterministic set definition.
7. **Boundary:** Includes points with value bottom and excludes top. Thus the definition alone is not a finite-real-valued domain condition. D is contextual and does not occur in the thirteen target conclusions.

### Q

1. **Spaces/objects:** Any type \(E\), \(f:E\to\overline{\mathbb R}\); output a subset of \(E\times\mathbb R\), not \(E\times\overline{\mathbb R}\). No structural instances.
2. **Quantifiers/order:** Implicit \(E\), then \(f\); membership of the pair \((x,t)\).
3. **Assumptions/regularity:** No finiteness or regularity requirement.
4. **Conclusion/content:** \(Q(f)=\{(x,t)\in E\times\mathbb R:f(x)\le\iota(t)\}\), the epigraph with real heights.
5. **Constants/normalization:** Canonical real embedding and non-strict order; no margin.
6. **Probability/information:** Deterministic set construction.
7. **Boundary:** At bottom all real heights qualify; at top none qualify. No infinite height belongs to the product type.

### C

1. **Spaces/objects:** Any additive commutative group \(E\) with real Module structure; \(f:E\to\overline{\mathbb R}\). The compiled type requires neither norm nor inner product.
2. **Quantifiers/order:** Implicit \(E\), AddCommGroup and Module instances, then \(f\).
3. **Assumptions/regularity:** No continuity, properness or topology requirement.
4. **Conclusion/content:** \(C(f)\iff Q(f)\text{ is convex over }\mathbb R\). Equivalently, for \(p,q\in Q(f)\) and nonnegative real \(a,b\) with \(a+b=1\), \(ap+bq\in Q(f)\).
5. **Constants/normalization:** Convex weights are nonnegative and sum to exactly 1; scalar field is real.
6. **Probability/information:** Convex weights are mathematical scalars, with no probabilistic interpretation required.
7. **Boundary:** Endpoint weights are included. This definition asserts epigraph convexity only, with no separate no-bottom or finite-witness condition.

### M

1. **Spaces/objects:** Arbitrary types \(E\) and \(I\), with Fintype and Nonempty on \(I\); \(f:I\to E\to\overline{\mathbb R}\). No vector-space structure on E is required by the compiled type.
2. **Quantifiers/order:** Implicit \(E,I\) and the two index instances, then \(f,x\).
3. **Assumptions/regularity:** Index set finite and nonempty; component functions unrestricted.
4. **Conclusion/content:** \(M(f,x)=\max_{i\in I}f(i,x)\), defined by the nonempty finite supremum over Finset.univ.
5. **Constants/normalization:** Actual maximum, without averaging, weighting or an extra zero baseline.
6. **Probability/information:** No random index, measurable selector or algorithm is asserted.
7. **Boundary:** Empty families are excluded; infinite component values are allowed. The noncomputable/classical presentation supplies no computable-choice claim.

### U

1. **Spaces/objects:** Real inner-product space E; finite nonempty index type I; component functions \(f:I\to E\to\overline{\mathbb R}\); output Set E.
2. **Quantifiers/order:** Implicit E and structural instances, then I and index instances, then \(f,x\); membership of \(g\) existentially quantifies \(i\).
3. **Assumptions/regularity:** No properness, continuity or convexity requirements on components.
4. **Conclusion/content:** \(U(f,x)=\{g:\exists i\in I,\ f(i,x)=M(f,x)\land g\in S(f(i,\cdot),x)\}\). It unites the full support sets of all attaining components.
5. **Constants/normalization:** Exact attainment equality, not approximate maximization; no weights or convex hull in U itself.
6. **Probability/information:** Existential membership does not prescribe a selected index or information process.
7. **Boundary:** All tied attaining components contribute; inactive components do not. U need not itself be convex. Its global support test inherits S, not a local or restricted-domain test.

## THIRTEEN neutral proof targets

### L01

1. **Spaces/objects:** Real inner-product space E; affine extended-real function \(A_{a,b}\); support subset at x.
2. **Quantifiers/order:** Universally implicit E and instances, then \(a\in E,b\in\mathbb R,x\in E\), in that order.
3. **Assumptions/regularity:** Only the two space instances; no finite dimension or additional premise.
4. **Conclusion:** \(S(A_{a,b},x)=\{a\}\). The entire global support set of this affine function is exactly its slope vector.
5. **Constants/normalization:** Intercept b is arbitrary; coefficient of \(\langle a,y\rangle\) is 1; equality of sets, not mere membership.
6. **Probability/information:** Deterministic, at every x; no probabilistic qualification.
7. **Boundary:** Includes zero slope, all intercepts and zero-dimensional spaces. No claim about derivatives or proof construction follows.

### L02

1. **Spaces/objects:** Same real inner-product space and \(A_{a,b}:E\to\overline{\mathbb R}\).
2. **Quantifiers/order:** Implicit E and instances, then every a and b; no explicit x binder in the target.
3. **Assumptions/regularity:** Only the space instances, despite P itself requiring no such structure.
4. **Conclusion:** \(P(A_{a,b})\): \((\forall y, A_{a,b}(y)\ne-\infty)\land(\exists y\exists t\in\mathbb R,A_{a,b}(y)=\iota(t))\). The affine function is proper in exactly this sense.
5. **Constants/normalization:** Arbitrary real b and vector a, with no boundedness constant or fixed witness in the conclusion.
6. **Probability/information:** Deterministic predicate, no random witness.
7. **Boundary:** The conclusion is P, not an explicit assertion of convexity, continuity or an algorithm for finding witnesses.

### L03

1. **Spaces/objects:** Same E and affine function; real-height epigraph in \(E\times\mathbb R\).
2. **Quantifiers/order:** Implicit E and both space instances, then all a and b.
3. **Assumptions/regularity:** No additional premises, finite-dimensional hypothesis or point x.
4. **Conclusion:** \(C(A_{a,b})\), equivalently \(\{(y,t):\iota(\langle a,y\rangle+b)\le\iota(t)\}\) is real convex. This states affine epigraph convexity.
5. **Constants/normalization:** Arbitrary intercept; usual nonnegative weights summing to 1.
6. **Probability/information:** Deterministic convexity assertion.
7. **Boundary:** No strict or strong convexity, compactness, smoothness or coercivity is asserted; flat affine functions are included.

### L04

1. **Spaces/objects:** Same E; function \(A_{a,b}\) takes values in EReal with its inferred topology.
2. **Quantifiers/order:** Implicit E and instances, then all a, b, x.
3. **Assumptions/regularity:** No extra regularity assumption or finite-dimensional instance.
4. **Conclusion:** \(\operatorname{ContinuousAt}(A_{a,b},x)\). The real affine expression followed by the EReal embedding is continuous at every supplied x.
5. **Constants/normalization:** a and b arbitrary; no modulus, Lipschitz constant or rate specified.
6. **Probability/information:** Deterministic pointwise continuity statement.
7. **Boundary:** Codomain is EReal, not E or merely real numbers. The exact target is ContinuousAt, with x universally quantified; it does not state differentiability.

### L05

1. **Spaces/objects:** Same E; Bool-indexed B family; two functions E to EReal.
2. **Quantifiers/order:** Implicit E and instances, then every z. x is not an explicit theorem binder.
3. **Assumptions/regularity:** No finite dimension or side condition.
4. **Conclusion:** \(M(B(z,\cdot,\cdot))=H(z,\cdot)\) as functions; equivalently, \(\forall x,\ \max_{i\in\mathrm{Bool}}B(z,i,x)=\iota(\max\{1-\langle z,x\rangle,0\})\).
5. **Constants/normalization:** Maximum of exactly the two Boolean components, with threshold 1 and zero branch.
6. **Probability/information:** Deterministic function equality; no policy or selection rule.
7. **Boundary:** Equality covers every x, including ties at r=0, and is stronger in syntactic form than a single-point equality. No parameter is inferred to depend on x.

### L06

1. **Spaces/objects:** Finite-dimensional real inner-product space E; support set of H and active-component support union U.
2. **Quantifiers/order:** Implicit E, both space instances, then FiniteDimensional over the reals, then all z and x.
3. **Assumptions/regularity:** Finite dimensionality is explicitly present; no further premises on z or x.
4. **Conclusion:** \(S(H(z,\cdot),x)=\operatorname{conv}_{\mathbb R}U(B(z,\cdot,\cdot),x)\). Supporting vectors of H are exactly the real convex hull of the supports of attaining components.
5. **Constants/normalization:** Ordinary convexHull, with no topological closure added and no approximate attainment.
6. **Probability/information:** Deterministic identity, without sampling or information assumptions.
7. **Boundary:** Includes ties and zero dimension. It does not quantify over general families or assert the same result in infinite-dimensional spaces.

### L07

1. **Spaces/objects:** Real inner-product space E; a fixed Boolean affine component and its support set.
2. **Quantifiers/order:** Implicit E and instances, then every z, Boolean i, and x, in that order.
3. **Assumptions/regularity:** No finite dimension or branch-activity premise.
4. **Conclusion:** \(S(B(z,i,\cdot),x)=\{\text{if }i=\mathrm{true}\text{ then }-z\text{ else }0\}\). Each component has precisely its own constant slope as supporting vector.
5. **Constants/normalization:** The compiled Boolean conditional tests i=true; true gives -z and false gives the zero vector.
6. **Probability/information:** Deterministic for every index; i is not a random choice.
7. **Boundary:** Also applies to inactive components. It does not itself state that either slope supports the maximum at x.

### L08

1. **Spaces/objects:** Real inner-product space E; EReal values of the false component.
2. **Quantifiers/order:** Implicit E and instances, then every z and x.
3. **Assumptions/regularity:** No side conditions or finite-dimensional assumption.
4. **Conclusion:** \(B(z,\mathrm{false},x)=\iota(0)\). The false component is zero at every point.
5. **Constants/normalization:** Right-hand side is embedded real zero, not bottom.
6. **Probability/information:** Deterministic evaluation identity.
7. **Boundary:** Applies even where false is not attaining and at z=0; contains no activity assertion.

### L09

1. **Spaces/objects:** Real inner-product space E; EReal value of the true component.
2. **Quantifiers/order:** Implicit E and instances, then every z and x.
3. **Assumptions/regularity:** No side condition or finite-dimensional assumption.
4. **Conclusion:** \(B(z,\mathrm{true},x)=\iota(1-\langle z,x\rangle)\). The true component is the affine residual.
5. **Constants/normalization:** Exact intercept 1 and minus sign on the inner product.
6. **Probability/information:** Deterministic evaluation identity.
7. **Boundary:** The residual may be negative, zero or positive. This formula contains no maximum or clipping and does not assert activity.

### L10

1. **Spaces/objects:** Real inner-product space E; active support union U for B at x.
2. **Quantifiers/order:** Implicit E and instances, then every z and x, then the premise r(z,x)<0 as an implication.
3. **Assumptions/regularity:** Strictly negative real residual, equivalently inner product greater than 1; no finite dimension.
4. **Conclusion:** \(r(z,x)<0\Longrightarrow U(B(z,\cdot,\cdot),x)=\{0\}\). The active union is exactly the singleton zero vector.
5. **Constants/normalization:** Comparison with real zero and threshold 1; set contains vector zero.
6. **Probability/information:** Deterministic implication, with no event probability.
7. **Boundary:** Does not include r=0. It states the union U itself, not its convex hull or the support set of H directly.

### L11

1. **Spaces/objects:** Real inner-product space E; active support union U for B.
2. **Quantifiers/order:** Implicit E and instances, then every z and x, followed by the premise 0<r(z,x).
3. **Assumptions/regularity:** Strictly positive real residual, equivalently inner product less than 1; no finite dimension.
4. **Conclusion:** \(0<r(z,x)\Longrightarrow U(B(z,\cdot,\cdot),x)=\{-z\}\). The active union is exactly the negative-slope singleton.
5. **Constants/normalization:** Exact negative vector -z; no multiplication by a residual or loss value.
6. **Probability/information:** Deterministic implication.
7. **Boundary:** Excludes the tie. At z=0 the premise holds and the singleton is {0}. No direct H-support or convex-hull conclusion appears.

### L12

1. **Spaces/objects:** Real inner-product space E; active union U; unordered set with listed elements 0 and -z.
2. **Quantifiers/order:** Implicit E and instances, then every z and x, followed by r(z,x)=0.
3. **Assumptions/regularity:** Exact zero residual, equivalently inner product 1; no finite-dimensional assumption.
4. **Conclusion:** \(r(z,x)=0\Longrightarrow U(B(z,\cdot,\cdot),x)=\{0,-z\}\). Both tied components contribute their singleton supports.
5. **Constants/normalization:** The compiled set is insert 0 (singleton (-z)); no convex combinations are inserted in U.
6. **Probability/information:** Deterministic equality under an exact tie, with no tie-breaking procedure.
7. **Boundary:** This target concerns the endpoints, not the intervening segment. Set notation is not a multiset or a declared cardinality. In particular, the premise is impossible when z=0.

### L13

1. **Spaces/objects:** Finite-dimensional real inner-product space E; support set of H; vector-valued closed segment parameterized by a real scalar.
2. **Quantifiers/order:** Implicit E and both space instances, then FiniteDimensional, then every z and x. Within the middle set, for each g there exists a real alpha in [0,1].
3. **Assumptions/regularity:** Finite dimension required by the compiled type; no premise restricting the residual, since the conclusion performs the split.
4. **Conclusion:** The full support set is
   \[
   S(H(z,\cdot),x)=
   \begin{cases}
   \{0\},&1-\langle z,x\rangle<0,\\
   \{g\in E:\exists\alpha\in[0,1],\ g=-(\alpha z)\},&1-\langle z,x\rangle=0,\\
   \{-z\},&1-\langle z,x\rangle>0.
   \end{cases}
   \]
   The exact compiled decision order first tests negativity, then equality to zero, then uses the final branch. Real order makes that final branch precisely positivity.
5. **Constants/normalization:** Alpha is real; Icc includes both 0 and 1; the vector is the negation of alpha scalar-multiplied by z. Threshold is exactly 1. No other scaling, closure, or coordinate choice appears.
6. **Probability/information:** A deterministic exhaustive case split; the existential scalar is a set-membership witness, not a computable/measurable selection, random coefficient or strategy.
7. **Boundary:** At the tie both endpoints and every intervening convex combination are included. At z=0 the residual is 1, hence the final branch gives {0}. Zero-dimensional spaces are not excluded. The statement supplies no infinite-dimensional extension, algorithm, regret, feedback model, source identity or whole-program completion.

## Reconstruction boundary

All thirteen proof targets have been reconstructed individually; all two owned and seven borrowed definitions have been kept separate. L06 and L13 are the only listed targets carrying a FiniteDimensional instance. The general borrowed contexts P, D and Q have no structural instances; M needs only a finite nonempty index; C needs AddCommGroup and a real Module; S and U retain the inner-product structures. These distinctions follow the packet's actual compiled types, not a blanket copying of section parameters.

This is a semantic reconstruction from the packet alone. It records neither proof verification nor source-faithfulness acceptance. No repository files, source text, history, search results, prior verdicts or proof bodies were consulted. No tests or compilation were performed, and no statement about an independently attested runtime model, external actor, or human review is made.