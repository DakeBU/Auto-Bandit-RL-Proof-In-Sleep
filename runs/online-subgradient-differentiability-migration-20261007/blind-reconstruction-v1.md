# Blind semantic reconstruction v1

## Scope and seven slots

I received only `blind-packet-v1.md` for this actor turn. I read no source identities, proof bodies, previous verdicts, compilation results, or other files. This is a distinct restricted decoder's interpretation of supplied declarations, not human or external review, source acceptance, proof verification, or runtime attestation of a model. Requested configuration is GPT-6 Astra / medium; I cannot independently attest the runtime model from the packet.

The packet does not name a seven-slot schema. I use these explicit slots consistently: (1) objects and types; (2) supplied premises; (3) quantifiers; (4) locality and domain; (5) conclusion; (6) derived versus supplied regularity; (7) limits and degeneracies.

Shared context for N01–N11: E is a finite-dimensional real inner-product space with its normed additive group. Its dimension can be zero. R itself has no finite-dimensional binder. C(f) is convexity of the real-height epigraph. D(f) is {y | f(y) < top}; this definition alone includes bottom. S(f,x) tests every y in the entire ambient E using f(x) + coe(inner g (y-x)) <= f(y). No theorem silently restricts these support queries to D(f), a ball, or a feasible set. All differentiability and HasGradientAt predicates here are ambient, not within-domain derivatives. No stochastic process, algorithm, or probability statement is supplied.

## R — actual finite differentiable germ

1. **Objects and types:** f : E -> EReal, x : E; E only requires a real inner-product normed additive group in the actual definition.
2. **Supplied premises:** R is the property being defined, not an additional theorem assumption about convexity or properness.
3. **Quantifiers:** there exists a total real-valued h : E -> real such that its EReal embedding agrees with f eventually in the neighborhood filter of x, and h is differentiable at x.
4. **Locality and domain:** agreement holds on a genuine ambient neighborhood of x, including x; it is not merely agreement along D(f), a sequence, or a punctured neighborhood.
5. **Conclusion/content:** f has an actual locally finite, real-valued, ambient differentiable representative.
6. **Derived versus supplied regularity:** local finiteness, finiteness at x, interior membership in D(f), and differentiability of f.toReal follow from this content. h and f.toReal have the same germ; whenever gradients are available their gradients at x coincide. Local continuity follows. No global regularity is included.
7. **Limits and degeneracies:** bare differentiability of f.toReal does not imply R, since conversion loses infinity information. R does not itself assume or imply convexity, global finiteness, or global nowhere-bottomness. The zero-dimensional case is allowed.

## N01 — bound at a locally Lipschitz finite point

1. **Objects and types:** f, point x, real radius r, nonnegative real constant K, and vector g, with the shared finite-dimensional ambient structure.
2. **Supplied premises:** r > 0; every y in ball(x,r) has a real finite f(y); f.toReal is K-Lipschitz on that ball; g belongs to S(f,x).
3. **Quantifiers:** the local finiteness premise is forall y in the ball, exists a real value; the conclusion is for each supplied supporting g, with no existence of such a g promised.
4. **Locality and domain:** Lipschitz control and finiteness are local; g's support inequality still queries all ambient y.
5. **Conclusion:** norm(g) <= K.
6. **Derived versus supplied regularity:** finiteness at x and interior membership follow from the positive finite ball. Convexity and global nowhere-bottomness are not supplied. If a g exists, its support at the finite x rules out bottom at any ambient query.
7. **Limits and degeneracies:** this is a bound, not differentiability, existence, uniqueness, or continuity of subgradients. K can be zero and E can have dimension zero.

## N02 — local uniform boundedness

1. **Objects and types:** f and x with the shared ambient structure.
2. **Supplied premises:** f is nowhere bottom globally, C(f), and x is in interior(D(f)).
3. **Quantifiers:** there exists r > 0 and K >= 0 such that for every y in ball(x,r), every g in S(f,y) has norm at most K. The same r and K work for all those y and g.
4. **Locality and domain:** output boundedness is local around x; every membership in S is defined by all ambient queries.
5. **Conclusion:** a uniform local bound on the entire subgradient set at each nearby point.
6. **Derived versus supplied regularity:** local finite real values follow from interior(D(f)) plus nowhere-bottomness. Convexity supports further local regularity, but no continuity or Lipschitz constant is an input.
7. **Limits and degeneracies:** the stated output does not assert the subgradient sets are nonempty or singletons, nor a global bound.

## N03 — limit closure for a nontrivial filter

1. **Objects and types:** arbitrary index type iota, filter l, maps xs and gs into E, limit points x and g, and f.
2. **Supplied premises:** NeBot(l); global nowhere-bottomness; x in interior(D(f)); continuity of f.toReal at x; xs tends to x; gs tends to g; eventually gs(i) belongs to S(f,xs(i)).
3. **Quantifiers:** arbitrary non-bottom filter and arbitrary maps, not only sequences; support membership is eventual, not required for all indices.
4. **Locality and domain:** limits and continuity are ambient. Each eventual supporting vector satisfies inequalities against every ambient query y.
5. **Conclusion:** g belongs to S(f,x).
6. **Derived versus supplied regularity:** continuity is explicitly supplied, not derived here from convexity: C(f) is absent. Interior plus nowhere-bottomness yields a finite neighborhood. NeBot is an explicit class premise and prevents vacuous bottom-filter limits.
7. **Limits and degeneracies:** convergence of gs is an input, so this theorem does not establish selection convergence, boundedness, existence, or uniqueness.

## N04 — convergence of arbitrary subgradient selections

1. **Objects and types:** arbitrary iota and filter l, f, x, a proposed unique g, and maps xs and gs into E.
2. **Supplied premises:** NeBot(l); global nowhere-bottomness; C(f); x in interior(D(f)); S(f,x) = {g}; xs tends to x; eventually gs(i) belongs to S(f,xs(i)).
3. **Quantifiers:** every non-bottom filter and every selection satisfying the eventual membership condition are covered; there is no assumed convergence of gs.
4. **Locality and domain:** ambient convergence and an ambient singleton; support queries remain global even though xs approaches x locally.
5. **Conclusion:** gs tends to g along l.
6. **Derived versus supplied regularity:** continuity of f.toReal and local boundedness are not supplied inputs. They may be intermediate consequences of convexity, nowhere-bottomness, and interior. The packet does not reveal actual proof dependencies. Singleton equality supplies both existence and uniqueness at x.
7. **Limits and degeneracies:** no global continuous selection is constructed, and no differentiability is an input. NeBot is mandatory in the actual type. The conclusion applies to supplied selections; it does not construct them.

## N05 — singleton forces interior

1. **Objects and types:** f, x, and g in the shared finite-dimensional ambient space.
2. **Supplied premises:** C(f); a real finite value f(x); S(f,x) = {g}.
3. **Quantifiers:** for every g satisfying that full singleton equality, the same x is shown interior.
4. **Locality and domain:** the conclusion is ambient interior, not relative interior. Singleton membership is defined using all ambient support queries.
5. **Conclusion:** x belongs to interior(D(f)).
6. **Derived versus supplied regularity:** interior is output, not input. Global nowhere-bottomness is not assumed; existence of the finite-point supporting g excludes bottom at every y. Together with point finiteness this yields P(f) as defined in the packet. These are consequences, not an added properness contract.
7. **Limits and degeneracies:** no closedness or lower semicontinuity premise appears. The type does not itself state differentiability. Zero-dimensional spaces are included.

## N06 — singleton vector is the actual derivative gradient

1. **Objects and types:** f, x, and g under the shared ambient assumptions.
2. **Supplied premises:** exactly C(f), real finiteness at x, and S(f,x) = {g}.
3. **Quantifiers:** every singleton representative g under these premises is identified with a derivative, not merely some unspecified vector.
4. **Locality and domain:** the derivative is ambient Frechet differentiation of the total map y |-> f(y).toReal, not a derivative restricted to D(f).
5. **Conclusion:** HasGradientAt(f.toReal, g, x). Its derivative sends v to inner g v; consequently f.toReal is differentiable and its gradient at x is g.
6. **Derived versus supplied regularity:** differentiability is output. Interior is not an input; N05 states it from the same premises. Global nowhere-bottomness follows from finite-point support. Hence genuine local finiteness is available, rather than relying only on the numeric toReal conversion.
7. **Limits and degeneracies:** the header is a gradient identity, not just a bare DifferentiableAt proposition. It states no global smoothness or continuity of gradients. It neither assumes nor concludes closedness.

## N07 — unpacking the genuine germ

1. **Objects and types:** f, x, and evidence hd : R(f,x), with finite dimension present in the theorem type even though absent from R's definition.
2. **Supplied premises:** only R(f,x), beyond the ambient structure.
3. **Quantifiers:** the conclusion first asserts eventually y near x there exists a real value of f(y); it does not require the same real value for all y.
4. **Locality and domain:** actual neighborhood finiteness, ambient interior, and ambient differentiability.
5. **Conclusion:** the conjunction of local real finiteness, x in interior(D(f)), and DifferentiableAt(real, f.toReal, x).
6. **Derived versus supplied regularity:** all three are output consequences of the representative germ. Convexity, properness, nowhere-bottomness outside the neighborhood, and continuity are not additional premises.
7. **Limits and degeneracies:** this is an implication from R, not a claim that its last conjunct alone is equivalent to R; it says nothing about subgradient existence.

## N08 — uniqueness relative to the canonical toReal gradient

1. **Objects and types:** f, x, and an arbitrary supporting vector g.
2. **Supplied premises:** global nowhere-bottomness; x in interior(D(f)); ambient differentiability of f.toReal at x; g in S(f,x).
3. **Quantifiers:** every such g equals the same canonical gradient.
4. **Locality and domain:** the derivative is ambient and local; membership in S imposes every ambient support query.
5. **Conclusion:** g = gradient(f.toReal, x).
6. **Derived versus supplied regularity:** local real finiteness comes from the explicit nowhere-bottom and interior premises. This is why differentiability of toReal is meaningful here as a genuine local real germ. Convexity is not supplied or needed in this header.
7. **Limits and degeneracies:** the conclusion is conditional uniqueness, not existence or singleton equality. An empty S would satisfy the universal uniqueness reading vacuously.

## N09 — complete identity for every differentiable representative

1. **Objects and types:** f, x, and an arbitrary total real representative h under the shared finite-dimensional structure.
2. **Supplied premises:** C(f); explicit real finiteness at x; neighborhood agreement coe(h) = f; ambient differentiability of h at x.
3. **Quantifiers:** for every h satisfying those germ premises, the entire subgradient set is exactly the singleton containing that h's gradient. This is stronger than exists g with singleton equality and stronger than at-most-one membership.
4. **Locality and domain:** representative equality holds eventually in the full neighborhood filter; differentiability is ambient; the resulting subgradient satisfies inequalities against every ambient y, including outside the finite neighborhood and outside D(f).
5. **Conclusion:** S(f,x) = {gradient h x}. Equivalently for every g in E, g is in S(f,x) iff g = gradient h x; in particular gradient h x is itself globally supporting. This supplies both existence and uniqueness.
6. **Derived versus supplied regularity:** germ agreement already implies point finiteness, making the written hx semantically redundant in this direction, but it remains an actual argument. It also gives local finiteness, interior, and equality of h's germ with f.toReal. Thus gradient h x = gradient(f.toReal,x). Any two admissible differentiable representatives have identical gradients at x. Neither global properness, global nowhere-bottomness, interior, nor closedness is supplied. The concluded finite-point supporting gradient entails global nowhere-bottomness and hence P(f); convexity plus the local real germ also precludes a bottom value via segments. Those are consequences, not hidden added hypotheses.
7. **Limits and degeneracies:** a bare smooth toReal function cannot replace the representative agreement premise. The theorem does not require all of f to be finite, h to be convex globally, or h and f to agree globally. It supplies no second derivative or global gradient regularity.

## N10 — forward terminal with representative hidden

1. **Objects and types:** f and x under the shared ambient structure.
2. **Supplied premises:** C(f), explicit real finiteness at x, and R(f,x).
3. **Quantifiers:** there exists g in E such that the entire S(f,x) equals {g}.
4. **Locality and domain:** R is an ambient finite differentiable germ; the output is the globally queried subgradient set.
5. **Conclusion:** nonempty singleton subdifferential. N09 identifies its g with gradient h x for every admissible representative h, hence also with gradient(f.toReal,x).
6. **Derived versus supplied regularity:** interior and local finiteness are derived from R, not separately assumed. The explicit hx follows from R but is retained in the type. Global nowhere-bottomness/properness follows once the finite-point singleton is obtained, not from an independently supplied global assumption.
7. **Limits and degeneracies:** this header states only the forward implication. It must not be misreported as the full equivalence, nor as only uniqueness without existence.

## N11 — complete two-way terminal

1. **Objects and types:** f : E -> EReal and x in a finite-dimensional real inner-product space.
2. **Supplied premises:** C(f) and exists r : real, f(x) = coe(r). These are the only function/point premises before the equivalence. There is no supplied global properness, global nowhere-bottomness, interior condition, closedness, continuity, local Lipschitz bound, or selected subgradient net.
3. **Quantifiers:** for every such f and x, R(f,x) iff exists g in E, S(f,x) = {g}. The right side is existence of an exact singleton, not merely at most one subgradient.
4. **Locality and domain:** the left side asserts an ambient finite real differentiable germ, and the right side is an ambient subgradient set defined by every-query support. Neither side is relative to a domain or an affine hull.
5. **Conclusion:** both directions hold under the same convexity and point-finiteness contract. Forward: any genuine differentiable representative yields the unique globally supporting gradient. Reverse: an exact singleton forces interior (N05) and identifies its vector as the ambient gradient of f.toReal (N06); finite-point support excludes bottom globally, so that interior supplies actual local finite values and h = f.toReal witnesses R. This is semantic reconstruction from the statements, not inspection of the proof body or its call graph.
6. **Derived versus supplied regularity:** in either established side, local finiteness and interior follow. Under singleton, nowhere-bottomness and P(f) are derived using finite-point support. On the R side, convexity and the terminal theorem yield them. For every g with S(f,x) = {g} and every differentiable h representing the f germ, g = gradient h x = gradient(f.toReal,x), with HasGradientAt(f.toReal,g,x). N11's literal output is the iff; these full identities are articulated by N06/N09 and uniqueness. The listed regularity premises of intermediate N01–N04 and N08 must not be imported into the N11 input contract.
7. **Limits and degeneracies:** only point finiteness is explicitly required besides convexity; it is not legitimate to describe the theorem as requiring global properness or an interior point in advance. Finite dimension is a real typeclass requirement. Dimension zero is permitted. No claim about a literature source, source correction, full research Goal completion, or compiled validity follows from these headers alone.

## Stress case: smooth conversion without a finite germ

In E = real take A = {0} and f = I(A), evaluated at x = 0. This is the convex indicator of a singleton. Its toReal conversion is the identically zero real function (both 0 and top convert to zero), hence is ambient differentiable with zero gradient. Nevertheless there is no ambient neighborhood of 0 on which f is finite: every neighborhood contains nonzero y with f(y) = top. Therefore R(f,0) fails. Directly from every-query support, S(f,0) is all of E: the query at 0 gives 0 <= 0 and all other queries have top on the right. In positive dimension this is not a singleton, consistently with N11. In dimension zero this particular counterexample disappears: {0} is the whole space, f is finite, R holds, and S = E = {0}. Thus a dimension-zero exclusion must not be silently added to the theorems, or omitted when presenting the positive-dimensional counterexample.

## Reconstruction boundary

All findings above concern the complete R definition, actual headers and @types provided in this packet. I have no basis here to certify kernel checking, implementation/proof dependencies, source correspondence, an earlier review, or project acceptance. I performed no independent filesystem or source search. Requested actor task: /root/differentiability_blind.
