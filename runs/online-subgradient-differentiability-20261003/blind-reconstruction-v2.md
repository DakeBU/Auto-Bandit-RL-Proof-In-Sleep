# Source-blind reconstruction, version 2

Actor: `/root/closed_blind`, distinct source-blind decoder assigned GPT-6 Astra / medium.

Read inventory for this turn: only `E:/ABRL/worktrees/research-online-book/runs/online-subgradient-differentiability-20261003/blind-packet-v2.txt`, read and hashed. No external-source search or other file read.

Packet SHA256: `62137DAA802F8946F6C435FB1B66AC1BC7BD2EF130489464A984CFD4CC7E9BAD`.

Prior context: this actor previously decoded version 1 of this packet and the closed/proper, basic-subgradient, and interior-support packets. The actor therefore has prior mathematical and contract context. No source text or source-review verdict was consulted. Earlier reconstruction files were not reread for this version.

## Slot 1: Ambient setting and definitions

E is any finite-dimensional real inner product space. The function f maps E into the extended reals. Its real epigraph uses only finite real vertical coordinates; IsConvexExtended asserts convexity of that epigraph. The effective domain is {x : f(x) < positive infinity}; as a definition alone it includes negative-infinity values.

SourceSubdifferential f x consists of vectors g such that f(x) + <g,y-x> <= f(y) for every y in all E. SourceDifferentiableAt means that some everywhere-defined real-valued h agrees with f after real-to-EReal embedding on an ambient neighborhood of x and is differentiable at x.

## Slot 2: Unchanged equivalence

For any epigraph-convex f and finite-valued point x, SourceDifferentiableAt f x is equivalent to the existence of g with SourceSubdifferential f x exactly equal to {g}. This is an exact singleton condition, with both existence and uniqueness. The displayed equivalence does not explicitly assume properness or interior membership. Its conclusion by itself does not name the singleton element as a gradient; version 2 now includes a separate endpoint that does so.

## Slot 3: Unchanged interior prerequisite

For epigraph-convex f, finite-valued x, and any g, equality of the entire subdifferential at x to {g} implies membership of x in the ambient topological interior of the effective domain. This is ambient interior, not relative interior. No boundary-point or restricted-domain differentiability interpretation is introduced.

## Slot 4: New gradient-identity endpoint and quantifiers

For every permitted E, every extended-valued f with convex real epigraph, every x at which f equals some finite real value, and EVERY real-valued function h on E, if the embedded h equals f eventually in the neighborhood filter of x and h is differentiable at x, then

    SourceSubdifferential f x = {gradient h x}.

Here h is universally quantified as a theorem argument; it is not a particular internally chosen witness and is not merely existentially selected in the conclusion. Both eventual equality and differentiability are required for that arbitrary h. Thus the endpoint explicitly identifies the unique subgradient with the gradient of every admissible differentiable local real representative.

Under the standard meaning of gradient on a real inner product space, gradient h x is the vector representing the derivative of h at x: the derivative applied to a direction v is <gradient h x,v>. The theorem directly states a singleton equality with that vector. It does not separately state an equality of continuous-linear-map expressions for the derivative, but the use of gradient carries the standard derivative-representing meaning. The imported definition of gradient was not inspected.

## Slot 5: Global support and representative independence

The equality implies both that gradient h x satisfies the global inequality for every y in E and that every vector satisfying that same global inequality equals gradient h x. It is not merely membership, a local support assertion, or an equality only on the effective domain.

Although agreement between h and f is only local near x, the supporting inequality asserted by the conclusion is global for f. There is no requirement that h be convex or agree with f globally. Its values away from the neighborhood may vary freely, provided the stated local agreement and differentiability hold.

If two real functions h and k both satisfy these hypotheses for the same f and x, this endpoint identifies the same subdifferential with both singleton gradients, hence their gradient vectors are equal. The theorem therefore provides representative-independent gradient identification through its universal quantification. At y=x the supporting affine expression equals f(x), giving exact contact.

## Slot 6: Finiteness, interior, and absent assumptions

The finite-value premise hx is explicit in the new endpoint. Local equality to a real-valued representative also entails finite values at x and throughout some ambient neighborhood, so hx is logically redundant given he, but it remains part of the displayed contract.

The new endpoint does not explicitly require SourceProper or interior membership. Neighborhood agreement implies interior membership in the effective domain. Its conclusion, together with finiteness at x, excludes negative-infinity values anywhere because a finite supporting expression cannot be below negative infinity. Positive-infinity values away from the finite neighborhood remain allowed, and the support inequality at those values is automatic.

Neither the new endpoint nor the earlier statements require closedness or lower semicontinuity. Finite-dimensionality and real inner product structure remain explicit. Zero dimension is not excluded. The statements do not apply at an infinite-valued x under their supplied hx hypotheses. The local representative condition is not a punctured-neighborhood condition and does not restrict differentiation to a subspace or relative domain.

## Slot 7: Context limits and status

Version 2 supplies an explicit generic gradient-identification endpoint in addition to the prior equivalence and interior implication. Its quantifier structure covers every differentiable local real representative satisfying the given agreement, which addresses the identification left unnamed in the equivalence alone.

The packet contains statement signatures without proof bodies or imports. Standard meanings were used for neighborhood-filter equality, differentiability, gradient, convexity, and interior. This reconstruction does not verify library implementation details, mathematical truth of the proposed statements, compilation, source fidelity, or acceptance. No proof edits or external-source inspection were performed.
