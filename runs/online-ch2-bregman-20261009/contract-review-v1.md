# Bounded Bregman SOURCE/CONTRACT review

Verdict: accepted-with-explicit-delta; no blocking mathematical or metadata repair. Stabilization only: no new proof body, Test, kernel closure, package or chapter acceptance. Reused distinct automated source reviewer with prior staged history; requested Astra/medium is not human/external/absolute-blind or runtime attestation.

Source-first: read the five frozen original-page text extractions (physical26/75/76/277/278; printed14/63/64/265/266) before the proposed headers. Independently rehashed the v10 PDF cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17 and freshly extracted all five pages with pypdf; each agrees with its saved text after edge whitespace only. No fresh pixel-view claim: this bounded packet contains these text/PDF files, not new PNGs. An initial read-only filename guess used nonexistent -text-v1 names; actual source-pdfN.txt names were then read. No file changed.

All 51 current indexed RAW inputs and all 2887 baseline hashes independently match before/after; common.fixed() passed. Definition-term and all five native statement fingerprints independently recomputed. Neutral context SHA and the distinct reconstruction agree with the definition and scoped types. API v1 actually failed on missing Even.convexOn_pow import; v2 adds Convex.Mul and exits0 with actual declarations, not new theorem proofs. The two generated OWN templates were preserved before draft specialization after the create-only collision; this is preparation metadata, not a mathematical target revision.

Definition6.4 has source X by intX, strict convexity and source differentiability. The canonical real extension Dpsi(a,b)=psi(a)-psi(b)-fderiv psi b(a-b) deliberately totalizes this expression. At nondifferentiable b its derivative defaults to zero; for psi=abs, a=0,b=1 is ordinary, but at b=0 the expression is merely the total algebraic extension unless regularity is supplied. No source metric, positivity or uniqueness follows from the definition alone. Self and three-point identities remain valid even with these default maps, because each fderiv value is still linear. The exact source orientation is preserved.

The nonnegative target is sound on convex X with both points in X and an actual ambient derivative at the base. The segment from y to x turns convexity into a scalar slope inequality; derivative at parameter0 is fderiv psi y(x-y), so psi(x)-psi(y) dominates it. Neither strictness nor an interior hypothesis is necessary for this derived real ambient-extension result; the source extension/locality bridge is still mandatory.

For the actual-minimum target take h(z)=eta inverse Dpsi(z,x). Its derivative at p is eta inverse times (fderiv psi p-fderiv psi x). The accepted real convex-minimizer comparison gives fp-fu bounded by that functional at u-p; multiplying by positive eta and the three-point identity at (p,x,u) gives exactly D(u,x)-D(u,p)-D(p,x). This checks both residual signs and every comparator. hdx is deliberately retained for source-base fidelity even though purely formal differentiation of the fixed linear map would not need it. hp is essential because IsMinOn alone has no membership. No minimizer, recurrence or subgradient oracle is manufactured. Concave psi can give negative divergence (for example psi(z)=-z^2 with distinct points), so the one-step theorem does not authorize discarding either residual without extra convexity.

The gradient bridge is exactly the actual pinned HasGradientAt.fderiv_apply under CompleteSpace and real InnerProductSpace. It recovers source pairing without imposing those classes on the normed core. Parent OnlineProximalComparison has its actual segment/minimum producer and unchanged accepted body; its prior PR208 evidence is reused within that bounded scope, not as closure of Algorithm15.8.

The dependency DAG is coherent: definition first, algebraic identities and nonnegative/gradient leaves from available Mathlib, then the one-step from the accepted minimizer comparison and three-point algebra. The planned nonquadratic canary numbers are plausible (D(0,1/2)=11/64, D(1/2,0)=9/64); proposed Test contracts still require separate exact type review. No current Test proof is assessed.

Permitted next work is stabilization of these exact five hashes and complete definition/context, then dependency-ready finite proof bodies only in new BanditRLProof/OnlineBregmanProximal.lean. Do not weaken the frozen hypotheses or replace actual fderiv by independent derivative data. Necessary local proof steps/imports may use the pinned shared project; any extra named helper must be explicitly inventoried and reviewed, not counted as a new source result. OWN versioned stabilization/proving metadata may preserve exact before snapshots for currently indexed mutable task/journal rows; no false future unchanged-live-byte claim. Roots, Tests, readers, old production, pins and global state are outside this permission. Full source X/interior/local extensions, EReal finite/subgradient/convexity/minimum bridge, actual attained current-loss recursion/interiority, same-run fixed/variable telescopes, and the source constant-step exercise remain required. All eight Chapter2 forwards, general source container and whole Goal remain open; no Chapter6/15 acceptance or source erratum.

Per-target seven-slot findings and exact future reader obligations follow in the receipt. Required repairs: none.

## BanditRL.OnlineBregman.divergence_self

- objects: Arbitrary real normed E; total real psi and x.
- quantifiers: All psi,x; no premises.
- assumptions: No derivative/convexity/inner product/completeness.
- conclusion: D(x,x)=0 exactly.
- normalization: Zero displacement, no scale.
- information: Pure algebra; no time or policy.
- boundary: Defaults included; no converse/strict separation/nonnegativity.

## BanditRL.OnlineBregman.three_point_identity

- objects: Same normed E,psi and three points; actual continuous dual maps.
- quantifiers: All x,y,z without membership.
- assumptions: No differentiability/convexity.
- conclusion: D(z,x)+D(x,y)-D(z,y)=(Dpsi(y)-Dpsi(x))(z-x).
- normalization: Signs and derivative order match Lemma6.7.
- information: Algebraic comparison, not iterates.
- boundary: Generalizes source interior/strict assumptions; default fderiv does not establish a source derivative.

## BanditRL.OnlineBregman.divergence_nonneg

- objects: ConvexOn real X psi and two points.
- quantifiers: All x,y in same X; derivative only at second point y.
- assumptions: ConvexOn includes convex X; ambient DifferentiableAt y.
- conclusion: Nonnegative ordered divergence.
- normalization: No factor/strict positivity.
- information: Deterministic first-order support.
- boundary: Boundary y allowed if ambient derivative; no outside-X/default positivity; singleton/zero dimension permitted.

## BanditRL.OnlineBregman.proximal_one_step

- objects: V,convex real f,total psi,positive eta,previous x,actual feasible minimum p.
- quantifiers: Given x,p,hmin then EVERY u in V; same psi,eta,p.
- assumptions: hp explicit; BOTH hdx/hdp; no x membership,f derivative,psi convexity,closedness/FD.
- conclusion: eta(fp-fu)<=D(u,x)-D(u,p)-D(p,x).
- normalization: Objective eta inverse; positive eta; both residuals retained with negative signs.
- information: Supplied global IsMinOn, not existence/selection/current-inclusive recursion.
- boundary: x outsideV valid; residual values need not be positive absent psi convexity; no dropping terms; T absent.

## BanditRL.OnlineBregman.divergence_eq_gradient

- objects: Complete real inner-product E; same canonical divergence and gradient.
- quantifiers: Every psi,x,y with derivative at y.
- assumptions: CompleteSpace only this section; ambient derivative at y.
- conclusion: D(x,y)=psi(x)-psi(y)-inner(gradient psi y)(x-y).
- normalization: Gradient first slot and displacement orientation exact.
- information: Representation only; no policy/loss gradient claim.
- boundary: Source finite Euclidean fits; does not add completeness to normed core or infer positivity.
