from pathlib import Path
import json,hashlib,subprocess
R=Path('E:/ABRL/worktrees/research-online-book');P=Path(__file__).resolve().parent
def put(n,x):
 b=x.encode() if isinstance(x,str) else (json.dumps(x,ensure_ascii=False,indent=2)+'\n').encode()
 with (P/n).open('xb') as f:f.write(b)
def rec(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return dict(path=str(p.resolve()),bytes=p.stat().st_size,sha256=h.hexdigest())
freeze=R/'docs/contracts/online-ch2-complete-target-freeze-v1/effective-targets-frozen-v3.2.json';j=json.loads(freeze.read_text(encoding='utf-8'))
rows=[x for x in j['effective_targets'] if x.get('source_id') in ['forward:prescient-lookahead','additional:prescient-lookahead-nonpositive-stability','Lemma7.5','Algorithm7.8-Theorem7.47','Algorithm15.9-Theorem15.31','dual-norm-Lipschitz-adapter']]
put('frozen-B4-selected-rows-v1.json',rows)
header='''import BanditRLProof.OnlineStrongConvexSupport
import BanditRLProof.OnlinePrescientBregmanSource
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

noncomputable section
open Set Finset
namespace BanditRL.OnlineConvex

theorem cumulative_optimistic_stability {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : Set E) (hV : Convex ℝ V)
    (psi hint : E → ℝ) (loss : ℕ → E → EReal) (n : ℕ) (lam : ℝ)
    (hbot : ∀ i < n + 1, ∀ x, loss i x ≠ ⊥)
    (hdom : ∀ i < n + 1, V ⊆ effectiveDomain (loss i))
    (hlam : 0 ≤ lam)
    (hstrong : let G : E → EReal := fun x =>
        (psi x : EReal) + ∑ i ∈ range (n + 1), loss i x + extendedIndicator V x
      ∀ x ∈ V, ∀ y ∈ V, ∀ a : ℝ, 0 < a → a < 1 →
        G (a • x + (1 - a) • y) ≤
          (a : EReal) * G x + ((1 - a : ℝ) : EReal) * G y -
            (((lam / 2) * a * (1 - a) * ‖x - y‖ ^ 2 : ℝ) : EReal))
    (p : E) (hp : p ∈ V)
    (hprediction : IsMinOn (fun x =>
      (psi x : EReal) + ∑ i ∈ range n, loss i x + (hint x : EReal)) V p)
    (g : E →L[ℝ] ℝ)
    (hdifference : ∀ z ∈ V,
      (loss n p).toReal - hint p + g (z - p) ≤ (loss n z).toReal - hint z)
    (q : E) (hq : q ∈ V) :
    let G : E → EReal := fun x =>
      (psi x : EReal) + ∑ i ∈ range (n + 1), loss i x + extendedIndicator V x
    (G p).toReal - (G q).toReal ≤
      g (p - q) - (lam / 2) * ‖p - q‖ ^ 2

end BanditRL.OnlineConvex
'''
put('neutral-header-proposal-v1.txt',header)
put('binder-ledger-v1.json',dict(status='PROPOSED_DERIVED_FINITE_BRANCH_NOT_FULL_NUMBERED_THEOREM',binders=[
 dict(binder='E/norm/real module',classification='TYPING',meaning='Arbitrary original norm. Continuous dual is the support-growth interface; conditional extension beyond finite source carrier.'),
 dict(binder='V,hV',classification='SOURCE',meaning='Literal convex source feasible set. Nonempty follows from actual hp. Closedness not needed for this conditional local inequality; remains mandatory for source attainment parent.'),
 dict(binder='psi,hint,loss,n',classification='TYPING',meaning='Current regularizer, current hint, actual loss sequence through current index n. n counts prior losses; G uses range(n+1). Ambient real psi/hint are extensions of their source domains, only values on V used.'),
 dict(binder='hbot',classification='SOURCE',meaning='Original source losses exclude bottom globally; required for ordinary EReal sum.'),
 dict(binder='hdom',classification='RULED',meaning='Declared finite-value branch: every included loss below top on all V, jointly with hbot finite there. Stronger than Algorithm7.8 played-point domain requirement; full extended/infinite-comparator branches remain OPEN. Already printed common-domain requirement in Algorithm15.9.'),
 dict(binder='hlam,hstrong',classification='SOURCE',meaning='Exact total current-inclusive objective curvature, no componentwise regularizer curvature assumption. Lambda0 valid for sharp inequality; positive lambda needed separately for division-based Young bound.'),
 dict(binder='p,hp,hprediction',classification='SOURCE',meaning='Actual Algorithm7.8 prediction rule at the explicit prior-prefix-plus-hint function. This is supplied actual algorithmic minimization, not a hidden minimum of G or affine tilt, not an attainment theorem.'),
 dict(binder='g,hdifference',classification='RULED',meaning='Explicit source-generalizing interface: continuous-linear support of current loss-minus-hint restricted to V. Source global coordinate subgradient implies this local support after real-value and coordinate-functional transport. No all-point support or global support of G is assumed.'),
 dict(binder='q,hq',classification='TYPING',meaning='Any feasible comparison point; can later be next prediction or approved terminal ghost. No minimizer property at q required.')],mandatory_delta='Two qualified interfaces are explicit: finite common-domain branch and local continuous-dual difference support. Independent review must approve these as a derived intermediate, never as full Lemma7.5/7.47 or a silent replacement of frozen originals.'))
proposal='''# Next B4 edge: actual cumulative optimistic stability

Proposal only. No header elaboration, BODY, Lean execution, or production mutation. This chooses ONE derived finite-branch stability theorem, with its neutral unelaborated header separated from these source notes. It is mathematically valid and structurally dependency-ready; it still requires independent source/blind review and freeze. The finite/common-domain and continuous-dual local-support deltas are explicit review decisions, not hidden source equivalences.

## Exact mathematical role

For n prior losses, define A=psi+sum_(i<n)loss_i and G=psi+sum_(i<n+1)loss_i+indicator(V). Let p be an actual minimizer on V of A+hint, and let g support loss_n-hint at p on V. Assume the actual G has lambda-strong curvature, not that psi supplies all curvature. Then for every feasible q,
G(p)-G(q) <= g(p-q)-(lambda/2)||p-q||^2.
All displayed values are finite under the declared branch. The new content is the construction of support for G from the actual prediction and difference-loss support. The existing supplied-support theorem alone does not establish this missing algorithmic premise.

This exact difference is the stability summand G_t(x_t)-G_t(x_(t+1)) in the existing finite_regret_identity. Unlike a new minimum-growth wrapper, this statement permits nonzero g and p that does NOT minimize G. The hprediction binder is transparently the source Algorithm7.8 minimizer of prior losses plus hint; it cannot be changed to IsMinOn G. No performance bound or curvature of a different objective is smuggled into the inputs.

## Pinned source anchors and proof spine

Orabona v10 SHAcef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17. Lemma7.5 printed101-102/PDF113-114 constructs loss support at the prior-loss minimizer and then applies Lemma4.2. Algorithm7.8 and Theorem7.47 printed129-130/PDF141-142 replace prior loss objective by A+hint and use a subgradient of loss-hint. The source uses Theorem6.27 zero support plus Theorem2.23 sum inclusion. The proposed implementation proves the resulting support directly by adding the actual minimum inequality and the loss-minus-hint support inequality. These are the same source algebraic dependencies, without introducing a public artificial zero-support helper. Existing stronglyConvex_support_growth then supplies the exact quadratic improvement.

No claim that this proves the source's existence/uniqueness paragraph: Theorem6.9 and its closedness/coercivity/domain qualifications remain unproved by this edge. Source closedness and subdifferentiability hypotheses needed for those later parent conclusions are not demanded by this conditional inequality. The source hypotheses are preserved in the full parent; this extracted local implication is stronger where those unused existence hypotheses are dropped.

## Internal construction, no proof search performed

Use no-bottom plus below-top for included losses to obtain actual finite real identities. Finite sum preserves no-bottom; on V the actual G is a finite coercion and outside V its indicator gives top. The feasible p witnesses nonempty V, so existing sourceProper_of_domain gives SourceProper G. Derive G's feasible domain inclusion; do not assume properness/domain of a returned objective.

For z in V, hprediction gives A(p)+hint(p)<=A(z)+hint(z). hdifference gives loss_n(p)-hint(p)+g(z-p)<=loss_n(z)-hint(z). Add them and use the range(n+1) decomposition, obtaining G(p)+g(z-p)<=G(z). Call stronglyConvex_support_growth on actual G,V,lambda,p,q with this produced local support and the original hstrong. Rearrange via g(p-q)=-g(q-p) and norm symmetry. No use of the proposed conclusion or a fake minimum of G.

The pending cumulative regularizer producer is a sufficient way to supply hstrong for some downstream components, but imposing its regularizer-curvature assumptions here would improperly narrow the more general total-objective source branch. Its properness construction can be reused internally conceptually; the current public theorem bundles it with regularizer curvature, so direct reuse would require an unjustified hypothesis. Do not split out a new properness wrapper merely to manufacture a dependency: the existing sourceProper_of_domain plus explicit finite sum is sufficient.

The accepted full iff does not produce support existence, so it cannot discharge hdifference. The installed vector adapter converts source coordinates when needed, but the natural proof here consumes a continuous dual directly. A future source-vector caller must derive the coordinate functional internally as already reviewed in the adapter, retaining the original norm. Do not add an isometry or replace the penalty with coordinate Euclidean norm.

## Source/interface deltas requiring explicit review

Algorithm7.8 permits extended losses and only requires its played point in the current loss domain. This header intentionally selects the common finite-on-V branch, so full infinite-comparator/undefined-difference cases remain separate. It must not be labelled the full theorem. Algorithm15.9 already has V subset dom loss_t; this condition is not a newly discovered omission there. Below-top alone includes bottom, so hbot is independent.

Algorithm7.8's hint is printed as V->R and psi on X. Here real ambient extensions are harmless because hprediction and hdifference use only V. Crucially the header asks only LOCAL support on V, so its truth does not depend on an arbitrary off-V extension of the hint. Global coordinate source support implies this local hypothesis; the converse is not asserted. The conditional arbitrary normed-space version generalizes the finite-dimensional source and makes no finite-dimensional attainment claim.

## Real consumers and nonredundancy

For Theorem7.47, substitute n=t-1,psi=psi_t,hint=hint_t,p=x_t,q=x_(t+1). This produces each G_t stability summand before finite_regret_identity adds regularizer differences and the terminal gap. Lemma7.5 is hint=0. The positive-lambda dual-norm Young bound remains a separate missing scalar/operator-norm edge; lambda0 here is legal and never divided by.

For BTRL15.31 the analogous negative-stability case is already available directly from existing minimum growth at the actual current-objective minimizer. Do not create another BTRL minimum-growth wrapper merely to reuse this theorem. What BTRL still needs is real trajectory/attainment, sum assembly and the approved terminal correction.

## Frozen terminal obstructions remain operative

The exact frozen repaired optimistic target retains G_T(z)-G_T(u) in the finite identity. A repeated final hint can leave this terminal gap POSITIVE; the leaf above cannot delete it. The approved route uses an unhinted ghost h_(T+1)=0,psi_(T+1)=psi_T and an attained minimizer z of G_T, separately proving all conditions. Repeating the hint instead requires its explicit correction h_(T+1)(u)-h_(T+1)(z), not cancellation. Truncating the final stability summand alone does not repair optimistic regret: the frozen positive terminal-gap obstruction remains.

For repaired BTRL, choose ghost x_(T+1)=x_T and sum negative movement only through t<T; the optional stronger terminal term is -lambda_T||u-x_T||^2/2. Repeating the final loss is refuted by the frozen0<=-1/36 example and is not an accepted completion. This proposal chooses no ghost and asserts no terminal inequality.

## Review/failure gates

Reject replacement of actual hprediction by a minimizer of G; a pre-assumed support of G or stability bound; an added norm-estimate premise standing in for the dual bound; a new hstrong on the regularizer instead of the actual total; or cancellation of any terminal gap without the exact approved ghost/minimizer argument. Reject a source-vector caller that assumes an isometry, treats local support as global, or ignores finite-value transport.

A later discriminating consumer should use n=0,psi(x)=x^2/2,hint=0,p=0,current loss=x on V=[-1,1]. G's minimizer is -1, so p is not a minimizer of G. The produced nonzero support g(z)=z gives tight G(0)-G(-1)=1/2 at lambda1; no growth conclusion is supplied as premise. This is a suggested canary only, without frozen header/BODY. Terminal negative examples remain separate tests of the parent assembly.

All broader B4 obligations remain OPEN: general cumulative production, actual global support existence, qualified attainment/uniqueness, full Lemma7.5 including dual bound, 7.47 and15.31 repaired performance theorems. C2 seven open-forward containers plus six future claims, null mandatory denominator and accepted=false remain unchanged; no C1-16 endpoint shipping claim.
'''
put('source-contract-proposal-v1.md',proposal)
reuse=[['OnlineStrongConvexMinimum.stronglyConvex_minimum_growth','existing, not duplicated; already supplies BTRL per-round negative movement when actual minimizer exists'],['OnlineStrongConvexSupport.stronglyConvex_support_growth','actual intended proof dependency after internally producing support of actual current cumulative G'],['OnlinePrescientBregmanSource.sourceProper_of_domain','actual intended properness parent on G; finite prefix proof remains local'],['OnlineCumulativePotential.finite_regret_identity','real downstream assembler consumes precisely G_t(x_t)-G_t(x_(t+1)); no terminal drop licensed'],['OnlineStrongConvexSourceSubgradient','installed coordinate interface, not forced as decorative proof dependency'],['pending cumulative_regularizer_source_strongConvex','sufficient provider for some curvature inputs; too strong to invoke universally here'],['pending full iff','reviewed iff under all-point support assumption; does not construct the difference support and cannot replace missing existence']]
put('reuse-and-boundaries-v1.json',dict(reuse= reuse,search_scope='Read-only inspection of exact listed installed source and prior reviewed pending packets; no proof search or new API search performed.',target='One derived actual finite-cumulative optimistic stability edge',header_not_elaborated=True,source_faithful_full_parent=False,qualified_intermediate=True,missing_assumptions='No hidden mathematical premise required for stated conditional leaf; full source parent still needs attainment/global-support/dual-norm/terminal prerequisites.',mandatory_independent_decisions=['Finite-common-domain branch qualification','Local continuous-dual support weakening of source global coordinate support','Actual algorithmic minimizer binder interpretation'],Lean_processes_started=0))
pdf=Path('E:/ABRL/worktrees/research-online-ogd/tmp/pdfs/orabona-v10.pdf')
for a,b in [(113,114),(141,142),(278,279)]:put(f'source-pages{a}-{b}-v1.txt',subprocess.check_output(['pdftotext','-f',str(a),'-l',str(b),'-layout',str(pdf),'-']).decode('utf-8'))
inputs=[freeze,R/'BanditRLProof/OnlineStrongConvexMinimum.lean',R/'BanditRLProof/OnlineStrongConvexSupport.lean',R/'BanditRLProof/OnlineStrongConvexSourceSubgradient.lean',R/'BanditRLProof/OnlineCumulativePotential.lean',R/'BanditRLProof/OnlinePrescientBregmanSource.lean',R/'tmp/online-b4-cumulative-producer-integration-proposal-20261012/OnlineCumulativeStrongConvex-candidate-v1.lean',R/'tmp/online-b4-full-iff-body-20261012/candidate-v1.lean',pdf]
put('input-bindings-v1.json',dict(head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R).decode().strip(),tracked_status=subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],cwd=R).decode().strip(),inputs=[rec(p) for p in inputs]))
put('manifest-v1.json',dict(status='PROPOSAL_ONLY_NO_BODY_NO_LEAN',header=rec(P/'neutral-header-proposal-v1.txt'),artifacts=[rec(p) for p in sorted(P.iterdir()) if p.is_file()],readiness='Mathematical route ready for separate semantic review; finite-branch/local-dual deltas must be approved before freeze. No theorem or chapter acceptance.'))
print(json.dumps(dict(header=rec(P/'neutral-header-proposal-v1.txt'),manifest=rec(P/'manifest-v1.json'))))
