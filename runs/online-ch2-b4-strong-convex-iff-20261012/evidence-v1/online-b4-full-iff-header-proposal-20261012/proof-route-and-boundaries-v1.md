# Full Lemma 4.2 iff: exact-header proposal only

The route is mathematically dependency-ready. The proposed one-theorem header is unelaborated and unfrozen. No proof BODY, placeholder, build, canonical module, or canary BODY is authorized by this packet. Parent source proposal and exact pinned PDF are bound in the manifest.

## Source scope and explicit delta

Definition4.1 printed34/PDF46 defines strong convexity for a proper function on a convex subset of its domain, with lambda>=0 and an arbitrary norm. Lemma4.2 on that page assumes V subset dom partial f, not merely dom f, and states the full iff with every source subgradient. The header spells the all-point nonempty GLOBAL subdifferential premise directly. Properness is inherited from the definition; convexity of V and nonnegative lambda are the printed assumptions. The stronger domain inclusion needed by the forward adapter is derived rather than added.

An algebraic e:E equivalent R^d represents the source's finite-dimensional carrier while allowing its separately chosen norm to stay on E. The pairing is coordinate Euclidean pairing only. Norm equivalence, isometry, Euclidean squared-norm curvature and an inner-product structure on E are unnecessary. This is explicit coordinate representation of the finite-dimensional source, including d=0; the iff is not claimed for arbitrary infinite-dimensional carriers.

Both sides use finite feasible values internally. The right-hand toReal inequality is therefore equivalent to the source inequality, not a convention assigning zero to an infinite endpoint. Every bottom is excluded by properness, and top is excluded at supported points by the existing properness-witness argument. For empty V both sides are vacuous; no witness in V is required. Lambda=0 remains included. There is no added global convexity of f, closedness, differentiability, support-existence theorem, minimizer or attainment assumption.

## Source proof topology and printed correction

Forward source node: base support at y, evaluate at alpha*x+(1-alpha)*y, combine with interpolation, divide by alpha>0, let alpha decrease to zero. This is faithfully exposed separately from the implementation's reused adapter proof via an affine tilt/minimum growth.

Converse source nodes: z=alpha*x+(1-alpha)*y lies in V; choose actual g in partial f(z) from the printed all-point premise; apply the hypothesized growth inequality at (z,x) and (z,y); weight by alpha and 1-alpha; cancel the pairing; simplify norm factors; obtain interpolation.

The source printed35/PDF47 incorrectly places an equality between the zero pairing and the weighted function/curvature expression. The correct chain is
0 = <g, alpha*(x-z)+(1-alpha)*(y-z)> <= alpha*f(x)+(1-alpha)*f(y)-f(z)-(lambda/2)*alpha*(1-alpha)*||x-y||^2.
This packet proposes proving the valid iff statement and explicitly records that local proof correction. It does not assert or silently prove the erroneous equality. For f(t)=t^2, lambda=1, x=1,y=-1,alpha=1/2,z=0,g=0, the right expression is1/2, making the printed 0=1/2 false while the corrected inequality is true. This numerical source-correction witness is a proposal, not a Lean canary.

## Planned implementation, with no new public assumptions

1. Define the coordinate function fbar(u)=f(e.symm u). Derive its no-bottom part by hf.1 at e.symm u; transport the actual finite witness w,r from hf.2 to e(w),r. This is a proof-local SourceProper package with the original witness, not a public premise.
2. For arbitrary p in V, unpack hsub p to obtain g. Apply subgradient_point_finite fbar hfbar (e p) g hg. Simplify e.symm(e p) to derive f p<top. Together with hf.1 p obtain coe((f p).toReal)=f p. The construction does not assume V nonempty.
3. Forward: apply stronglyConvex_sourceSubgradient_growth d e f V lam hf hV derived_hdom hlam hstrong p hp g hg q hq. Future imported audit must see this exact provider with actual operand identities.
4. Converse: fix x,y,a with feasible endpoints and0<a<1. Let b=1-a,z=a*x+b*y. Convexity gives z in V. Choose a single global g from hsub z; apply the right side twice, at p=z,q=x and p=z,q=y using that same g. Multiply by nonnegative a,b and add.
5. Linearity of e and real inner pairing gives a<g,e(x-z)>+b<g,e(y-z)>=<g,e(a*(x-z)+b*(y-z))>=0. The vector identity is a*(x-z)+b*(y-z)=0. Use only algebraic linearity, not norms of e.
6. Original-space identities x-z=b*(x-y), y-z=(-a)*(x-y) give squared norms b^2||x-y||^2 and a^2||x-y||^2. Thus a*(lambda/2)*b^2*N+b*(lambda/2)*a^2*N=(lambda/2)*a*b*N. Rearrange to the real interpolation inequality. No division by lambda or a norm and no strict curvature is needed.
7. Rewrite all feasible F values through derived finite identities and coerce the real inequality into the exact EReal left side. Ordinary arithmetic never combines top with bottom.

## Failure conditions and later discriminating tests

Reject any implementation that adds hdom, finiteDimensional/continuity/isometry, a minimizer, support-existence beyond hsub, global convexity, or an inner product on E. Reject a converse that takes two unrelated chosen supports or replaces norm_E with norm of coordinates. Reject inference of the source's erroneous equality. Preserve all failed elaborations if a later freeze permits work; header changes require renewed review.

Later public-canary proposals should cover an actual converse call, empty V and lambda=0, and coordinate scaling in a non-Euclidean chosen norm. A separate negative premise test can use f(t)=-t^2 on R: it is proper and has no GLOBAL support at any point, so the universal growth statement is vacuous without hsub, while zero-strong-convex interpolation at -1 and1 fails. This shows why V subset dom f cannot replace the printed V subset dom partial f. No canary statement or BODY is frozen here.

The target is the full iff under the exact source all-point support premise; independent support existence, closedness/attainment, cumulative support production, stability, full Lemma7.5 and corrected Theorems7.47/15.31 remain OPEN. The pending cumulative sufficient producer does not automatically supply hsub. C2 accepted=false, seven open forward containers, six future claims and null mandatory denominator remain unchanged. No chapter or C1-16 completion follows.
