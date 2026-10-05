# Blind reconstruction: Q0–Q4 and M01–M22

This fresh restricted-input pass read only `blind-packet-v1.md` in this directory as mathematical file input. It read no source identity, name map, proof body, prior verdict, log, or other file. Earlier unrelated actor history is not erased. This is a distinct automated decoder role, requested GPT-6 Astra / medium; the runtime model was not independently verified. No human/external-model review, compilation, proof validation, source acceptance, or chapter/Goal certification is claimed.

Independent raw-byte input SHA-256:
`fdb3770cbfb89203ed06c0f4de8cb0d112d733c4963da141ef55f5c2fef210c1`.

## Notation and context

Unless a header specifies stronger or additional structure, E is an additive commutative group and real module. No norm, topology, completeness, or finite-dimensional hypothesis is assumed. Write ι(r) for a real r embedded in EReal, with bottom −∞ and top +∞. Let D_f=Q0(f), epi_R(f)=Q1(f), Cvx(f)=Q2(f), I_V=Q3(V), and a⊞b=Q4(a,b). The epigraph here has **real** height coordinates, not EReal heights. All results are deterministic; none involves probability, information access, an algorithmic trajectory, or regret.

Imported EReal arithmetic and toReal are used but not defined in the packet. The formulas below retain those operations. In particular ⊞ is the explicitly defined operation −(−a+−b), not a license to replace it with ordinary EReal addition in mixed-infinity cases. The zero-scalar case in the displayed multiplication uses the formal EReal convention; under its usual zero multiplication rule 0·z=0, even for infinite z. No source/library file was consulted to validate implementations.

## Q0

1. **Objects:** f:E→EReal and subset D_f⊆E.
2. **Quantifiers:** Defined for every f and evaluated at every x∈E.
3. **Assumptions:** None on values or regularity.
4. **Conclusion:** D_f={x:f(x)<+∞}.
5. **Constants/normalization:** Strict cutoff at +∞; no numeric bound.
6. **Information/probability:** Deterministic set definition.
7. **Boundary:** −∞ values are included. D_f can be empty, notably for f≡+∞; it is not necessarily the finite-real-valued locus.

## Q1

1. **Objects:** f and a subset of E×ℝ.
2. **Quantifiers:** Every f; every pair (x,r) with real r.
3. **Assumptions:** None.
4. **Conclusion:** epi_R(f)={(x,r):f(x)≤ι(r)}.
5. **Constants/normalization:** Non-strict inequality; real height coordinate.
6. **Information/probability:** Deterministic membership condition.
7. **Boundary:** At f(x)=+∞ the fiber is empty; at f(x)=−∞ it is all ℝ; at finite f(x)=v it is [v,∞). The complete epigraph may be empty.

## Q2

1. **Objects:** Extended-real f and its real-height epigraph in the real product module E×ℝ.
2. **Quantifiers:** Every f.
3. **Assumptions:** None added to the definition.
4. **Conclusion:** Cvx(f) means epi_R(f) is convex over ℝ.
5. **Constants/normalization:** Usual convex combinations with nonnegative weights summing to one.
6. **Information/probability:** Deterministic predicate.
7. **Boundary:** No properness, finite witness, or exclusion of −∞. Empty epigraphs are convex; both constant +∞ and constant −∞ are allowed by this definition.

## Q3

1. **Objects:** V⊆E and extended-real indicator I_V:E→EReal.
2. **Quantifiers:** Every V and every x.
3. **Assumptions:** No convexity or nonemptiness of V required for definition.
4. **Conclusion:** I_V(x)=0 when x∈V, and +∞ otherwise.
5. **Constants/normalization:** Zero inside, positive infinity outside; not a 0/1 indicator.
6. **Information/probability:** Deterministic membership test, using classical case distinction.
7. **Boundary:** V=∅ gives constant +∞; V=E gives constant zero. It never takes −∞.

## Q4

1. **Objects:** Arbitrary a,b∈EReal and the operation a⊞b.
2. **Quantifiers:** All extended-real pairs.
3. **Assumptions:** None.
4. **Conclusion:** a⊞b=−(−a+−b), using formal EReal negation and addition.
5. **Constants/normalization:** Two argument negations and one outer negation; finite inputs are characterized in M15.
6. **Information/probability:** Deterministic algebraic definition.
7. **Boundary:** Mixed infinities must follow this operation. M16–M17 explicitly make +∞ absorbing, even when the other argument is −∞. For inputs without +∞, a −∞ argument yields −∞ under the usual extended-real arithmetic. No undefined-case exclusion is imposed.

## M01

1. **Objects:** V⊆E in a real module.
2. **Quantifiers:** For every V, equivalence with ∀x∈V ∀y∈V ∀θ∈ℝ satisfying 0<θ<1.
3. **Assumptions:** None on V beyond being a set.
4. **Conclusion:** V is convex iff θx+(1−θ)y∈V for all those strict weights and points.
5. **Constants/normalization:** Weights θ and 1−θ sum to one; only strict θ in the displayed right side.
6. **Information/probability:** Deterministic universal closure condition.
7. **Boundary:** Empty and singleton sets included; θ=0,1 are omitted from the right-side tests, not denied as convex combinations. No topology/closedness required.

## M02

1. **Objects:** f:E→EReal and D_f.
2. **Quantifiers:** Every f satisfying Cvx(f).
3. **Assumptions:** Convex real-height epigraph only.
4. **Conclusion:** D_f is convex.
5. **Constants/normalization:** D_f uses f<+∞, including −∞ values.
6. **Information/probability:** Deterministic implication.
7. **Boundary:** No properness or nonempty domain required. The result does not claim f is finite on D_f.

## M03

1. **Objects:** Arbitrary V and I_V.
2. **Quantifiers:** Every V⊆E.
3. **Assumptions:** None.
4. **Conclusion:** D_{I_V}=V as equality of sets.
5. **Constants/normalization:** Indicator zero is below +∞; outside value equals +∞.
6. **Information/probability:** Deterministic identity.
7. **Boundary:** Includes empty, nonconvex, and whole-space V.

## M04

1. **Objects:** V, extended indicator, and epigraph convexity.
2. **Quantifiers:** Every V.
3. **Assumptions:** No added conditions.
4. **Conclusion:** Cvx(I_V) iff V is convex.
5. **Constants/normalization:** The 0/+∞ indicator is the one used.
6. **Information/probability:** Deterministic equivalence.
7. **Boundary:** Empty V is included and its indicator has empty epigraph. No closedness, nonemptiness, or properness requirement.

## M05

1. **Objects:** f, real-height epigraph, D_f, and toReal(f(x)).
2. **Quantifiers:** Every f excluding −∞ at every point; set equality tests all (x,r)∈E×ℝ.
3. **Assumptions:** ∀x, f(x)≠−∞.
4. **Conclusion:** epi_R(f)={(x,r):x∈D_f and toReal(f(x))≤r}.
5. **Constants/normalization:** Real height r and non-strict inequality; domain membership retained as a conjunction.
6. **Information/probability:** Deterministic epigraph conversion with finiteness enforced by membership plus the hypothesis.
7. **Boundary:** +∞ is allowed outside D_f. Empty D_f allowed. Dropping the no-−∞ premise would change the interpretation; toReal alone does not certify finite values.

## M06

1. **Objects:** f and its real-valued conversion on D_f.
2. **Quantifiers:** Every f with no −∞ values.
3. **Assumptions:** ∀x, f(x)≠−∞.
4. **Conclusion:** Cvx(f) iff ConvexOn ℝ D_f (x↦toReal(f(x))). ConvexOn includes convexity of D_f as well as the function inequality there.
5. **Constants/normalization:** No loss scaling; exact equivalence.
6. **Information/probability:** Deterministic reduction to a real-valued domain statement.
7. **Boundary:** Empty domain included, with vacuous function tests. Values outside D_f can be +∞ and their conversion is irrelevant to ConvexOn restricted to D_f. No finite witness required.

## M07

1. **Objects:** f,D_f and extended-real convex-combination inequality.
2. **Quantifiers:** For every f under premises, equivalence with ∀x,y∈D_f ∀θ, 0<θ<1 implies the inequality.
3. **Assumptions:** No −∞ values anywhere, and D_f convex supplied separately.
4. **Conclusion:** Cvx(f) iff
   \[f(\theta x+(1-\theta)y)\le\iota(\theta)f(x)+\iota(1-\theta)f(y)\]
   for all specified x,y,θ.
5. **Constants/normalization:** Strict weights, unit sum, EReal multiplication/addition on the right.
6. **Information/probability:** Deterministic universal Jensen-type condition.
7. **Boundary:** Values at the tested domain points and their combination are finite under the premises. Empty D_f allowed. End weights 0,1 and pairs outside D_f are not part of this displayed criterion. Domain convexity is not to be silently omitted.

## M08

1. **Objects:** f and convex V; pointwise ordinary EReal sum f+I_V.
2. **Quantifiers:** Every f meeting its premises and every convex V.
3. **Assumptions:** No −∞ values of f, Cvx(f), and convexity of V.
4. **Conclusion:** Cvx(x↦f(x)+I_V(x)). This represents restricting f to V by assigning +∞ outside.
5. **Constants/normalization:** Ordinary addition, not ⊞; indicator uses 0/+∞.
6. **Information/probability:** Deterministic closure property.
7. **Boundary:** Empty V or disjoint V and D_f allowed, producing constant +∞. The no-−∞ premise prevents problematic ordinary mixed-infinity addition outside V. No closedness required.

## M09

1. **Objects:** Any real module E and real-valued f:E→ℝ, embedded into EReal.
2. **Quantifiers:** Every such E and f.
3. **Assumptions:** No further regularity.
4. **Conclusion:** Cvx(ι∘f) iff ConvexOn ℝ E f.
5. **Constants/normalization:** Whole space univ and unscaled real embedding.
6. **Information/probability:** Deterministic equivalence.
7. **Boundary:** All values are finite; no extended-real exceptional values or proper-domain restriction. Norm/topology unnecessary.

## M10

1. **Objects:** Real inner-product space E, vectors z,x, scalar b; affine real loss x↦⟨z,x⟩+b embedded in EReal.
2. **Quantifiers:** Every E with normed additive group and real inner-product structure, every z and b.
3. **Assumptions:** No sign condition on b or norm bound on z.
4. **Conclusion:** This embedded affine function has convex real-height epigraph.
5. **Constants/normalization:** Offset b is arbitrary; coefficient vector exactly z.
6. **Information/probability:** Deterministic convexity assertion.
7. **Boundary:** Includes z=0 and all b. No completeness or finite dimension required.

## M11

1. **Objects:** Real normed space E and x↦ι(‖x‖).
2. **Quantifiers:** Every E with NormedAddCommGroup and NormedSpace ℝ structures.
3. **Assumptions:** No inner product required.
4. **Conclusion:** The embedded norm function has convex real-height epigraph.
5. **Constants/normalization:** Norm itself, not squared norm or half squared norm.
6. **Information/probability:** Deterministic convexity.
7. **Boundary:** Zero vectors included; no completeness, finite dimension, or bounded-domain premise.

## M12

1. **Objects:** Real modules E,F, extended-real f:F→EReal, affine map A:E→F.
2. **Quantifiers:** Every such pair of spaces, every convex-epigraph f and affine A.
3. **Assumptions:** Cvx(f); A is affine over ℝ.
4. **Conclusion:** Cvx(f∘A).
5. **Constants/normalization:** Arbitrary affine map including translation; no invertibility or scale factor.
6. **Information/probability:** Deterministic precomposition closure.
7. **Boundary:** Constant/noninjective/nonsurjective A allowed. Infinite values and empty effective domain of the composition allowed; no properness required.

## M13

1. **Objects:** Arbitrary index type I, real module E, family f_i:E→EReal.
2. **Quantifiers:** Every I,E,f with Cvx(f_i) for every i.
3. **Assumptions:** Each member's real-height epigraph convex; no index nonemptiness or boundedness.
4. **Conclusion:** Cvx(x↦sup_i f_i(x)).
5. **Constants/normalization:** Pointwise EReal supremum over all indices, no finite-family restriction or averaging.
6. **Information/probability:** Deterministic closure under suprema.
7. **Boundary:** Empty index type gives the bottom function −∞ under the complete-lattice supremum convention. Unbounded-above families can give +∞. No properness or common finite point required.

## M14

1. **Objects:** Real-valued f:E→ℝ and g:ℝ→ℝ.
2. **Quantifiers:** Every such f,g satisfying all three premises.
3. **Assumptions:** Cvx(ι∘f), Cvx(ι∘g), and globally Monotone g (nondecreasing on all ℝ).
4. **Conclusion:** Cvx(x↦ι(g(f(x)))).
5. **Constants/normalization:** No scaling; ordinary function composition.
6. **Information/probability:** Deterministic monotone-convex composition property.
7. **Boundary:** Constant g permitted; strictly increasing is not required. All values here are real; this is not a composition theorem for arbitrary EReal-valued f,g or merely locally monotone g.

## M15

1. **Objects:** Real scalars a,b embedded into EReal and operation ⊞.
2. **Quantifiers:** Every real a,b.
3. **Assumptions:** Finiteness supplied by real types; no sign constraints.
4. **Conclusion:** ι(a)⊞ι(b)=ι(a+b).
5. **Constants/normalization:** Exact ordinary finite sum, no coefficient or offset.
6. **Information/probability:** Deterministic arithmetic identity.
7. **Boundary:** Zero/negative finite values included. Does not state agreement with ordinary EReal addition for arbitrary infinite arguments.

## M16

1. **Objects:** Arbitrary a∈EReal and +∞.
2. **Quantifiers:** Every a, including both infinities.
3. **Assumptions:** None.
4. **Conclusion:** a⊞(+∞)=+∞.
5. **Constants/normalization:** Positive infinity absorbs in the second argument.
6. **Information/probability:** Deterministic operation law.
7. **Boundary:** In particular (−∞)⊞(+∞)=+∞; no mixed-infinity exclusion.

## M17

1. **Objects:** Arbitrary a∈EReal and +∞ in the first argument.
2. **Quantifiers:** Every a.
3. **Assumptions:** None.
4. **Conclusion:** (+∞)⊞a=+∞.
5. **Constants/normalization:** First-argument absorption, complementing M16.
6. **Information/probability:** Deterministic arithmetic.
7. **Boundary:** Includes a=−∞ and a=+∞; output remains +∞.

## M18

1. **Objects:** a,b∈EReal, finite real height h, and real witnesses r,s.
2. **Quantifiers:** For every a,b,h, equivalence to existence of r,s satisfying all three conditions together.
3. **Assumptions:** h real; no finiteness assumption on a,b.
4. **Conclusion:**
   \[a\boxplus b\le\iota(h)\iff\exists r,s\in\mathbb R:\ a\le\iota(r),\ b\le\iota(s),\ r+s\le h.\]
5. **Constants/normalization:** Witness bound is r+s≤h, with unit coefficients.
6. **Information/probability:** Deterministic existential characterization of a finite-height sublevel condition.
7. **Boundary:** If either argument is +∞ no such finite upper bound witness exists and the inequality is false. −∞ arguments are allowed; finite witnesses can still be selected when no argument is +∞. h=±∞ is not an instance of this header.

## M19

1. **Objects:** Extended-real functions f,g on a real module E and pointwise ⊞.
2. **Quantifiers:** Every convex-epigraph pair f,g.
3. **Assumptions:** Cvx(f) and Cvx(g), no no-−∞ condition.
4. **Conclusion:** Cvx(x↦f(x)⊞g(x)).
5. **Constants/normalization:** Uses Q4 specifically, not ordinary EReal addition.
6. **Information/probability:** Deterministic convexity closure.
7. **Boundary:** Mixed infinities, empty effective domains, and no common finite point allowed. +∞ absorption is crucial to interpreting the displayed operation; no properness assertion follows.

## M20

1. **Objects:** Positive real a, arbitrary z∈EReal, finite real h.
2. **Quantifiers:** Every a>0, every z, every h∈ℝ.
3. **Assumptions:** Strict positivity of a only.
4. **Conclusion:** ι(a)z≤ι(h) iff z≤ι(h/a).
5. **Constants/normalization:** Division by exactly a; order direction unchanged because a>0.
6. **Information/probability:** Deterministic order equivalence.
7. **Boundary:** z=±∞ included. a=0 and negative a excluded; h is finite. No zero-division rule is inferred from this equivalence.

## M21

1. **Objects:** Extended-real f, real scalar a, pointwise multiplication by ι(a).
2. **Quantifiers:** Every f with Cvx(f), every a≥0.
3. **Assumptions:** Epigraph convexity and nonnegative, not strictly positive, scalar.
4. **Conclusion:** Cvx(x↦ι(a)f(x)).
5. **Constants/normalization:** Scalar acts on values, unlike affine precomposition acting on inputs.
6. **Information/probability:** Deterministic positive-scaling closure.
7. **Boundary:** a=0 explicitly included; its interpretation uses EReal's zero-product convention (the zero function under the usual convention). f may attain either infinity. Negative scaling is not claimed to preserve convexity.

## M22

1. **Objects:** Extended-real convex-epigraph f,g and nonnegative real scalars a,b.
2. **Quantifiers:** Every such f,g and every pair a≥0,b≥0.
3. **Assumptions:** Cvx(f), Cvx(g); no properness, common finite point, or weight-sum condition.
4. **Conclusion:** Cvx(x↦(ι(a)f(x))⊞(ι(b)g(x))).
5. **Constants/normalization:** Weights need not sum to one. Value scalings are combined with Q4, not ordinary EReal addition.
6. **Information/probability:** Deterministic closure under nonnegative weighted Q4-combinations.
7. **Boundary:** Either or both weights may be zero; infinities in f,g are allowed and evaluated by the formal scalar product followed by ⊞. With both zero the usual zero-product convention yields zero function. Negative weights and a replacement of ⊞ by ordinary addition are outside the statement.

## Scope limitations

All five definitions and 22 headers have seven-slot coverage. Infinity and empty-set regimes are part of the reconstructed scope, rather than implicit properness exclusions. Imported EReal arithmetic, ConvexOn and other library operations are not reproduced fully by the packet; this report uses their mathematical interpretation and flags the zero-product convention without claiming implementation verification. No proofs or original source were accessed, and no acceptance conclusion follows.
