# Restricted blind reconstruction: finite sums, v1

I read only the current supplied `blind-packet-v1.md` for this task. This actor previously completed a separate restricted differentiability packet; therefore I do not claim a fresh actor without prior mathematical context. I did not reread that packet or its outputs here. I have not read source identities, proof bodies, review verdicts, compilation results, or other project files. Requested configuration: GPT-6 Astra / medium; runtime model provenance is unattested. This is neither human nor external review and does not certify source acceptance, compilation, or a user/project/book Goal.

The seven slots below are: 1 objects/types; 2 supplied premises; 3 quantifiers/witnesses; 4 ambient/domain scope; 5 conclusion; 6 derived versus supplied regularity; 7 limits/degeneracies. The packet does not supply a differently named seven-slot template.

## Shared semantic conventions

Ordinary EReal addition is bottom-dominant at mixed infinities. U(a,b) = -(-a + -b) is top-dominant there. They cannot be interchanged without appropriate hypotheses. D(f) = {y | f(y) < top} includes bottom for a generic f. P(f) expressly excludes bottom at every point and supplies at least one real finite value. Thus D of a proper component is exactly its finite-value domain. C(f) is convexity of its epigraph with REAL heights. Q(f) requires every real-height sublevel set {y | f(y) <= coe(r)} to be closed; it is not a claim that D(f) is closed.

S(f,x) is the set of g satisfying f(x) + coe(inner g (y-x)) <= f(y) for EVERY y in the entire ambient E. It is not restricted to D(f), the qualification point, or feasible query points, and is defined for nonproper f as well.

The actual types have finite-dimensional real inner-product E for exactly N03, N04, N06, N07, N08, N09. N01, N02, N05 are scalar statements without E or any E typeclasses. M has a real inner-product normed additive group E but no finite-dimensional requirement. There is no supplied CompleteSpace binder; completeness can be derived for the six finite-dimensional settings. E is nonempty and may have dimension zero. No probability or algorithm occurs.

## M — full finite Minkowski witness definition

1. **Objects/types:** an arbitrary Fintype iota, a family f : iota -> E -> EReal, and query x : E; output a Set E. E has NormedAddCommGroup and InnerProductSpace real, with no finite-dimensional binder.
2. **Supplied premises:** none about the functions beyond their types; no properness, convexity, closedness, or qualification.
3. **Quantifiers/witnesses:** g is in M(f,x) iff there exists an actual simultaneous vector assignment G : iota -> E such that every G(i) belongs to S(f(i),x) AND the finite vector sum of G(i) equals g.
4. **Ambient/domain scope:** all components are queried at the same x; each support membership tests every ambient y, independently of the other support tests.
5. **Conclusion/content:** M is the genuine finite Minkowski sum of the component subgradient sets. Membership in the sum function's S does not by itself constitute an M witness.
6. **Derived versus supplied regularity:** none is supplied or created by this definition. Existence of G gives actual component members; uniqueness or a canonical choice is not asserted.
7. **Limits/degeneracies:** an empty iota gives M = {0}; a one-element iota gives the corresponding S; one empty component set makes M empty. The vector sum is in E, not EReal, so the witness sum itself has no infinity ambiguity.

## N01 — agreement of two scalar additions

1. **Objects/types:** a,b : EReal, with no ambient E.
2. **Supplied premises:** a != bottom and b != bottom.
3. **Quantifiers/witnesses:** for all such a,b; no existential witness.
4. **Ambient/domain scope:** scalar arithmetic only.
5. **Conclusion:** U(a,b) = a+b.
6. **Derived versus supplied regularity:** either input may be top; real finiteness is not required. Excluding bottom removes the mixed-infinity conflict.
7. **Limits/degeneracies:** this does not equate the operations unconditionally: at (top,bottom), ordinary addition is bottom whereas U is top. No topology, convexity, or dimensional hypothesis occurs.

## N02 — a selected finite scalar sum is not bottom

1. **Objects/types:** arbitrary type iota, Finset s, scalar family a : iota -> EReal; no Fintype for all of iota and no E classes.
2. **Supplied premises:** every a(i) with i in s is not bottom.
3. **Quantifiers/witnesses:** the premise is only for selected indices; the conclusion concerns the sum over s written as sum i in s, a(i).
4. **Ambient/domain scope:** no function domain or ambient query.
5. **Conclusion:** that finite EReal sum is not bottom.
6. **Derived versus supplied regularity:** no assumption excludes top, so the sum can be top. No claim of real finiteness follows.
7. **Limits/degeneracies:** empty s gives zero and satisfies the conclusion. Terms outside s are unconstrained.

## N03 — convexity of a selected function sum

1. **Objects/types:** finite-dimensional real inner-product E, arbitrary iota, Finset s, family f : iota -> E -> EReal.
2. **Supplied premises:** for every selected i and every ambient y, f(i,y) != bottom; for every selected i, C(f(i)).
3. **Quantifiers/witnesses:** only i in s are constrained; nowhere-bottomness quantifies over all y, not only a common domain.
4. **Ambient/domain scope:** the result concerns y |-> sum over selected i of f(i,y) on all E; epigraph heights are real.
5. **Conclusion:** C of that sum function.
6. **Derived versus supplied regularity:** N02 gives global nowhere-bottomness of the sum. Neither properness of the components nor a common finite point is an input, so properness of the sum is not obtained from this header.
7. **Limits/degeneracies:** empty s yields the zero convex function. The sum may be identically top. No Q, continuity, or subgradient identity is stated; the actual finite-dimensional binder remains part of the contract even if one expects a weaker mathematical result.

## N04 — pointwise real finiteness survives a finite sum

1. **Objects/types:** finite-dimensional real inner-product E, Fintype iota, family f, and x : E.
2. **Supplied premises:** for each i there exists a real r with f(i,x) = coe(r).
3. **Quantifiers/witnesses:** the real r may depend on i; the output supplies one real value for the aggregate at x.
4. **Ambient/domain scope:** this is a condition at the supplied x only. No other y is constrained.
5. **Conclusion:** exists r : real, sum_i f(i,x) = coe(r).
6. **Derived versus supplied regularity:** convexity, global nowhere-bottomness, properness, and closedness are absent. If a common real representative is chosen for each term, its real sum represents the output.
7. **Limits/degeneracies:** empty iota is allowed and the output is zero. The actual theorem has finite-dimensional E despite the arithmetic nature of its conclusion; it must not be reported as one of the three scalar-only declarations.

## N05 — no infinite component in a nontop nonbottom sum

1. **Objects/types:** Fintype iota and a : iota -> EReal; no E or E typeclasses.
2. **Supplied premises:** every a(i) is not bottom, and sum_i a(i) is not top.
3. **Quantifiers/witnesses:** for every i, output exists r : real with a(i) = coe(r); the real witness can vary by i.
4. **Ambient/domain scope:** scalar finite sum only.
5. **Conclusion:** each summand is real finite.
6. **Derived versus supplied regularity:** nonbottomness of the total follows by finite summation, so the total is itself finite. The explicit termwise nonbottom premise is what prevents bottom-dominant addition from hiding a top component.
7. **Limits/degeneracies:** for empty iota the output is vacuous and the sum is zero. Dropping the nonbottom premise would allow mixed top and bottom with a bottom total, invalidating the conclusion.

## N06 — common interior gives interior for the sum

1. **Objects/types:** finite-dimensional real inner-product E, Fintype iota, family f, and point z.
2. **Supplied premises:** every f(i,y) is nonbottom for every i,y; z belongs to interior(D(f(i))) for every i.
3. **Quantifiers/witnesses:** the same z is interior for all components; the finite index set allows a common neighborhood.
4. **Ambient/domain scope:** these are ordinary ambient interiors, not relative interiors. The sum is defined on all E.
5. **Conclusion:** z is in interior(D(sum_i f(i))).
6. **Derived versus supplied regularity:** nowhere-bottomness turns domain membership into real finiteness; locally all terms are finite, hence their finite sum is finite. Convexity, Q, and P are not inputs, although the supplied z together with global nonbottomness gives finite witnesses for each component and the aggregate.
7. **Limits/degeneracies:** empty iota gives the zero function with domain E, and the conclusion holds for every z. This does not prove the stronger-looking mixed condition used later by simply assuming every domain is interior: the last component in N09 need not be interior.

## N07 — binary decomposition at a finite query point

1. **Objects/types:** finite-dimensional real inner-product E, functions f,h, query x, and vector g.
2. **Supplied premises:** P(f), P(h), C(f), C(h); f(x) and h(x) are each explicitly real finite; g is in S(f+h,x); exists z in interior(D(f)) intersect D(h).
3. **Quantifiers/witnesses:** for each supplied g, output exists p with p in S(f,x) and g-p in S(h,x). The actual component vectors are p and g-p, whose sum is g.
4. **Ambient/domain scope:** qualification z is independent of query x. Only f's domain must be interior at z; h's domain need only contain z, possibly at its boundary. Both component support conclusions test all ambient y. No relative interior is substituted.
5. **Conclusion:** an actual decomposition of g into two globally supporting component vectors.
6. **Derived versus supplied regularity:** properness supplies global nowhere-bottomness. Qualification supplies a common finite point, hence properness of the aggregate. Query finiteness is explicitly supplied here, not merely derived silently. Q/closedness is not an input to this helper.
7. **Limits/degeneracies:** this helper is not itself a set equality for arbitrary x. It constructs a decomposition conditional on a supplied g; it does not assert every x admits a subgradient. Its missing Q premise cannot be used to remove Q from N09's stated contract.

## N08 — unconditional direction of the sum rule

1. **Objects/types:** finite-dimensional real inner-product E, arbitrary Fintype iota, family f, arbitrary x : E.
2. **Supplied premises:** P(f(i)) for every i, and no additional functional assumption.
3. **Quantifiers/witnesses:** for every g in M(f,x), its actual simultaneous component witnesses imply g in S(sum_i f(i),x). The statement quantifies over every x.
4. **Ambient/domain scope:** every support inequality for the input components and output sum ranges over all ambient y. x is not restricted to the common domain or a qualification set.
5. **Conclusion:** M(f,x) is a subset of S(sum_i f(i),x), in this direction only.
6. **Derived versus supplied regularity:** no convexity, Q, common finite point, qualification, or query-finiteness assumption occurs. Calling the inclusion unconditional means independent of those extra assumptions, not independent of component properness or the actual ambient typeclasses. If M membership is available in a nonempty family, each component support plus its proper finite witness forces finiteness at x; this is derived, not an input.
7. **Limits/degeneracies:** empty iota is allowed: M = {0} and the zero sum has S = {0}. Proper components need not have a common domain, so the aggregate can be identically top and improper. For generic S, an identically top aggregate has S = E at every x, not the empty set; the inclusion remains true and may be strict.

## N09 — exact positive-family equality under mixed qualification

1. **Objects/types:** finite-dimensional real inner-product E, n : natural, family f indexed by Fin(n+1), arbitrary query x : E.
2. **Supplied premises:** for every component, P, C, and Q; additionally exists z such that z is in D(f(last n)), and for every index i unequal to last n, z is in interior(D(f(i))).
3. **Quantifiers/witnesses:** one qualification point z works simultaneously for all components and is chosen independently of the universally queried x. The equality means that every g supporting the aggregate at x has actual vectors G(i) supporting each component at that same x with sum G(i)=g, and conversely every such witness sum supports the aggregate.
4. **Ambient/domain scope:** the last domain is required only to contain z; z may be on its boundary. All other domains use ordinary ambient interiors. Neither relative interiors nor an interior condition at x is substituted. Every support membership on both sides still tests all ambient y.
5. **Conclusion:** S(sum_i f(i),x) = M(f,x) for every x, with both inclusion directions, including the decomposition direction absent from N08.
6. **Derived versus supplied regularity:** query-finiteness premises hfx/hhx of N07 are absent here. Proper components plus qualification ensure a common finite z; by finite summation the aggregate is finite at z and nowhere bottom globally, hence proper. For x outside the aggregate's domain, its S is empty; some component is top at x and that proper component has empty S, hence M is empty too. For a nonempty S at x, aggregate properness forces query finiteness, and N05 then yields each component's query finiteness. These are consequences used to understand the all-x equality, not extra inputs. Q is explicitly retained for EVERY component, including last, irrespective of weaker helper hypotheses.
7. **Limits/degeneracies:** the family is positive, never empty: n=0 gives a singleton. In that singleton case all nonlast-interior requirements are vacuous; the qualification reduces to existence of a last-domain point, already ensured by P. The conclusion reduces to the one-component identity, but P/C/Q remain in the actual header. Dimension zero is permitted. No arbitrary-family extension, closure of a Minkowski sum, uniqueness of decomposition, domain closedness, algorithm, or source theorem acceptance is claimed.

## Infinity and qualification checks

For a proper component f and x with f(x)=top, choose its real finite witness y. Every candidate g would require top + finite <= f(y), which is false; hence S(f,x) is empty. In contrast, for the GENERIC function identically top, every query has top on both sides, so S(f,x)=E. These facts must not be conflated by importing a convention that all subdifferentials at infinite values are definitionally empty: that is not the supplied S.

A concrete N08 stress case in E=real is f=I({0}) and h=I({1}). Each is proper, convex, and has closed real sublevels, but their domains are disjoint. Their ordinary sum is identically top. At every x at least one component has empty S, so M is empty, whereas S of the aggregate is all of E. Thus N08 holds strictly and N09's common-point qualification is absent. This example is explicitly in positive dimension; in dimension zero proper components are necessarily finite at the unique point, so this disjoint-domain construction cannot occur.

N09 does not require the last domain's qualification point to be interior. For example, in E=real let one component be the zero function and the last component be I([0,infinity)). A qualification point z=0 is interior to the first domain E and on the boundary of the last domain; the stated mixed condition permits it. Query x remains arbitrary and need not equal z.

These checks reconstruct the contracts from the supplied declarations. They are not inspection of proof bodies, dependency graphs, source material, kernel results, or programme completion.

## File access accounting

Content read this task: E:/ABRL/worktrees/research-online-book/runs/online-subgradient-sum-migration-20261007/blind-packet-v1.md only.
Written this task: E:/ABRL/worktrees/research-online-book/runs/online-subgradient-sum-migration-20261007/blind-reconstruction-v1.md and E:/ABRL/worktrees/research-online-book/runs/online-subgradient-sum-migration-20261007/blind-receipt-v1.json only. Raw-byte hash reads also cover those outputs and the input, as listed in the receipt. No file search was performed.

Actor task: /root/differentiability_blind. Prior actor history is disclosed above; current semantic input is only this packet.
