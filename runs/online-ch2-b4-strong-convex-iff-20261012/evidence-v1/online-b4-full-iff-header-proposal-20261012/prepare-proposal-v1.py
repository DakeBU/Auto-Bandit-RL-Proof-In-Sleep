import hashlib,json,subprocess
from pathlib import Path
R=Path('E:/ABRL/worktrees/research-online-book'); P=Path(__file__).resolve().parent
def put(name,obj):
 b=(json.dumps(obj,ensure_ascii=False,indent=2)+'\n').encode() if not isinstance(obj,str) else obj.encode()
 with (P/name).open('xb') as f:f.write(b)
def rec(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
header='''import BanditRLProof.OnlineStrongConvexSourceSubgradient

noncomputable section
open Set
namespace BanditRL.OnlineConvex

theorem stronglyConvex_iff_sourceSubgradient_growth {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (d : ℕ) (e : E ≃ₗ[ℝ] EuclideanSpace ℝ (Fin d))
    (f : E → EReal) (V : Set E) (lam : ℝ)
    (hf : SourceProper f) (hV : Convex ℝ V) (hlam : 0 ≤ lam)
    (hsub : ∀ p ∈ V,
      (SourceSubdifferential (fun u => f (e.symm u)) (e p)).Nonempty) :
    (∀ x ∈ V, ∀ y ∈ V, ∀ a : ℝ, 0 < a → a < 1 →
      f (a • x + (1 - a) • y) ≤
        (a : EReal) * f x + ((1 - a : ℝ) : EReal) * f y -
          (((lam / 2) * a * (1 - a) * ‖x - y‖ ^ 2 : ℝ) : EReal)) ↔
    (∀ p ∈ V, ∀ q ∈ V, ∀ g : EuclideanSpace ℝ (Fin d),
      g ∈ SourceSubdifferential (fun u => f (e.symm u)) (e p) →
        (f p).toReal + inner ℝ g (e (q - p)) +
          (lam / 2) * ‖q - p‖ ^ 2 ≤ (f q).toReal)

end BanditRL.OnlineConvex
'''
put('proposed-header-v1.txt',header)
ledger=[
 dict(binder='E, NormedAddCommGroup E, NormedSpace ℝ E',classification='TYPING',expanded='Real normed carrier with arbitrary original norm; no inner product on E, completeness or finite-dimensionality premise.'),
 dict(binder='d,e',classification='TYPING',expanded='Finite algebraic coordinate equivalence to EuclideanSpace ℝ (Fin d), supplying the coordinate pairing and source R^d carrier. No isometry or relation between coordinate Euclidean norm and E norm. d=0 allowed.'),
 dict(binder='f,V,lam',classification='TYPING',expanded='Extended-real function, literal feasible subset, real curvature coefficient. Original values and set retained.'),
 dict(binder='hf',classification='SOURCE',expanded='Definition4.1 properness inherited by the strong-convexity predicate: forall x, f x != bottom; exists x and real r with f x=coe r. The global witness is used to exclude top at supported points, including after coordinate transport.'),
 dict(binder='hV',classification='SOURCE',expanded='Printed convex set V. For x,y in V and nonnegative weights summing to one, their weighted sum belongs to V. Empty V allowed.'),
 dict(binder='hlam',classification='SOURCE',expanded='Printed lambda >=0; zero allowed, no division by lambda.'),
 dict(binder='hsub',classification='SOURCE',expanded='Exact printed V subset dom partial f: for every p in V there exists an actual vector g whose GLOBAL coordinate support inequality holds at every u in R^d. No support construction is concluded; no restriction of support evaluation to V.'),
 dict(binder='left x,y,a',classification='TYPING',expanded='Universal feasible endpoints, strict 0<a<1. Original E norm and coefficient lambda/2*a*(1-a). Finite values follow internally; endpoint weights need not be added to the source statement.'),
 dict(binder='right p,q,g',classification='TYPING',expanded='Universal p,q in V and EVERY global coordinate subgradient at p, not merely a chosen support. Pairing uses e(q-p); quadratic penalty uses original norm(q-p).')]
put('binder-ledger-v1.json',dict(binders=ledger,no_EXCESS=True,derived_not_assumed=['SourceProper (fun u => f (e.symm u))','V subset effectiveDomain f','finite real identities at every point of V','segment membership','same support used for both converse endpoint inequalities'],definition_audit={'SourceSubdifferential':'Literal set of all g satisfying forall ambient u, f(e.symm(e p))+coe(inner g (u-e p)) <= f(e.symm u). No default selection and no finite-point restriction hidden in definition.','effectiveDomain':'Below-top set, which generically includes bottom; hf separately excludes bottom.','SourceProper':'Global no-bottom plus genuine finite witness.','strong_convexity':'Expanded EReal interpolation, with properness/convex domain/nonnegative coefficient as external source standing assumptions.'}))
pdf=Path('E:/ABRL/worktrees/research-online-ogd/tmp/pdfs/orabona-v10.pdf')
assert rec(pdf)['sha256']=='cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17'
source=subprocess.check_output(['pdftotext','-f','46','-l','47','-layout',str(pdf),'-']).decode('utf-8')
put('source-pages46-47-v1.txt',source)
reuse=[
 {'declaration':'BanditRL.OnlineConvex.stronglyConvex_sourceSubgradient_growth','decision':'reuse_existing','role':'Entire forward implication; exact original f,V,lambda,e and derived domain, supplied g. Actual imported VALUE call required after future BODY authorization.'},
 {'declaration':'BanditRL.OnlineConvex.subgradient_point_finite','decision':'reuse_existing','role':'After transporting properness to f composed e.symm, proves each supported coordinate point finite. No new public domain premise.'},
 {'declaration':'BanditRL.OnlineConvex.theorem_2_21','decision':'adapt_existing','role':'Read its two weighted support inequalities and cancellation proof topology. Not an actual dependency promise: theorem only yields zero-curvature real ConvexOn in an inner-product carrier, and cannot establish the arbitrary-original-norm quadratic term.'},
 {'declaration':'strongConvexOn_iff_convex','decision':'out_of_scope','role':'Mathlib subtract-squared-norm characterization assumes InnerProductSpace on the same carrier. Cannot substitute it for arbitrary E norm. No Euclidean penalty transport.'},
 {'declaration':'stronglyConvex_support_growth / stronglyConvex_minimum_growth','decision':'reuse_existing','role':'Already indirect parents through installed adapter; do not add artificial direct calls or wrappers.'},
 {'declaration':'EReal.coe_toReal / coe_le_coe_iff / coe_add / coe_mul / coe_sub; map_add,map_smul,map_sub; norm_smul,norm_neg; real inner linearity','decision':'reuse_existing','role':'Existing APIs for real/extended-real transport and original norm homogeneity; exact tactic elaboration remains untested.'}]
search=subprocess.run(['rg','-n','-g','Online*.lean',r'theorem stronglyConvex|theorem subgradient_point_finite|theorem theorem_2_21',str(R/'BanditRLProof')],capture_output=True,text=True)
put('reuse-search-v1.txt',search.stdout+'\nSTDERR:\n'+search.stderr+'\nexit='+str(search.returncode)+'\n')
put('reuse-audit-v1.json',dict(classification='adapt_existing',module='BanditRLProof/OnlineStrongConvexSubgradientIff.lean',one_public_theorem=True,extra_public_helpers=False,searched=reuse,search_scope='Current Online*.lean declarations plus Mathlib Analysis/Convex/Strong.lean; no existing full arbitrary-norm source-coordinate iff found in this bounded search.',search_failure_history='Initial rg used an unexpanded Windows Online* path, producing error123; repeated with -g Online*.lean and directory succeeds. No mathematical evidence inferred from the failed command.',genuine_future_consumers=['Converts all-point source quadratic-growth characterizations to/from Def4.1 curvature for actual cumulative parents once their source support-existence premises are proved.','Full source Lemma4.2 iff boundary itself; does not resolve existence/attainment/stability.'],proof_graph='IFF forward -> installed adapter -> supplied-support/minimum growth; point finiteness -> subgradient_point_finite; converse -> same actual g at segment point, weighted endpoint growth, original norm homogeneity. Teaching order is not extra proof-term dependency.'))
proposal='''# Full Lemma 4.2 iff: exact-header proposal only

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
'''
put('proof-route-and-boundaries-v1.md',proposal)
inputs=['tmp/online-b4-full-iff-planning-20261012/route-proposal-v1.json','BanditRLProof/OnlineStrongConvexSourceSubgradient.lean','BanditRLProof/OnlineStrongConvexSupport.lean','BanditRLProof/OnlineSubgradientBasic.lean','BanditRLProof/OnlineClosedProper.lean','BanditRLProof/OnlineConvexExtended.lean','.lake/packages/mathlib/Mathlib/Analysis/Convex/Strong.lean','docs/contracts/online-ch2-complete-target-freeze-v1/effective-targets-frozen-v3.2.json','lean-toolchain','lake-manifest.json']
assert rec(R/inputs[0])['sha256']=='b21b33219eb83f5c9c43cc58e2d938683c73235554a78965ffa5f339bba53c60'
put('input-bindings-v1.json',dict(head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R).decode().strip(),tracked_status=subprocess.check_output(['git','status','--porcelain'],cwd=R).decode().strip(),source_pdf=rec(pdf),inputs=[rec(R/p) for p in inputs]))
put('manifest-v1.json',dict(status='PROPOSAL_ONLY_UNFROZEN_UNELABORATED_NO_BODY',header=rec(P/'proposed-header-v1.txt'),artifacts=[rec(p) for p in sorted(P.iterdir()) if p.is_file()],readiness='Mathematical route dependency-ready; exact header requires independent blind/source review, local freeze and separate elaboration/BODY authorization.',source_equality_typo='Explicit correction proposed in proof-route; unchanged false equality not claimed.',Lean_processes_started=0,canonical_edits=False))
print(json.dumps(dict(header=rec(P/'proposed-header-v1.txt'),manifest=rec(P/'manifest-v1.json'))))
