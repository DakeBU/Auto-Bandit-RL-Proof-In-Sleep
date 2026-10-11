from pathlib import Path
import hashlib,json
P=Path(__file__).resolve().parent
def put(n,s):
 b=s.encode() if isinstance(s,str) else (json.dumps(s,ensure_ascii=False,indent=2)+'\n').encode()
 with (P/n).open('xb') as f:f.write(b)
def rec(p):return dict(path=p.name,bytes=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest())
context='''import BanditRLProof.OnlineStrongConvexSubgradientIff

noncomputable section
open Set
namespace BanditRL.Tests.OnlineStrongConvexSubgradientIffCanary
open BanditRL.OnlineConvex

abbrev E := Fin 2 → ℝ
abbrev U := EuclideanSpace ℝ (Fin 2)
def feasible : Set E := {x | ∀ i, x i ∈ Set.Icc (-1 : ℝ) 1}
def objective (x : E) : EReal :=
  (((x 0 ^ 2 + x 1 ^ 2) / 2 + x 0 : ℝ) : EReal)
def coordinates : E ≃ₗ[ℝ] U := (WithLp.linearEquiv 2 ℝ E).symm
def scaledCoordinates : E ≃ₗ[ℝ] U :=
  coordinates.trans (LinearEquiv.smulOfNeZero ℝ U 2 two_ne_zero)
def covector (p : E) : U :=
  (1 / 2 : ℝ) • coordinates (fun i => p i + if i = 0 then 1 else 0)
def query : E := fun _ => 1
def negativeSquare (x : ℝ) : EReal := ((-x ^ 2 : ℝ) : EReal)

'''
first='''theorem box_converse_originalNorm :
    (∀ x ∈ feasible, ∀ y ∈ feasible, ∀ a : ℝ, 0 < a → a < 1 →
      objective (a • x + (1 - a) • y) ≤
        (a : EReal) * objective x + ((1 - a : ℝ) : EReal) * objective y -
          ((((1 : ℝ) / 2) * a * (1 - a) * ‖x - y‖ ^ 2 : ℝ) : EReal)) ∧
    SourceProper objective ∧
    (∀ p ∈ feasible,
      covector p ∈ SourceSubdifferential
        (fun u => objective (scaledCoordinates.symm u)) (scaledCoordinates p)) ∧
    (∀ p ∈ feasible, ∀ q ∈ feasible, ∀ g : U,
      g ∈ SourceSubdifferential
        (fun u => objective (scaledCoordinates.symm u)) (scaledCoordinates p) →
        (objective p).toReal + inner ℝ g (scaledCoordinates (q - p)) +
          (1 / 2 : ℝ) * ‖q - p‖ ^ 2 ≤ (objective q).toReal) ∧
    ‖query‖ ^ 2 = (1 : ℝ) ∧
    ‖scaledCoordinates query‖ ^ 2 = (8 : ℝ) ∧
    inner ℝ (covector 0) (scaledCoordinates query) = (1 : ℝ) ∧
    covector 0 ≠ 0 ∧
    objective 0 = (0 : EReal) ∧ objective query = (2 : EReal) ∧
    ¬ ((objective 0).toReal + inner ℝ (covector 0) (scaledCoordinates query) +
      (1 / 2 : ℝ) * ‖scaledCoordinates query‖ ^ 2 ≤ (objective query).toReal) ∧
    (1 / 2 : ℝ) * (objective query).toReal +
      (1 / 2 : ℝ) * (objective (-query)).toReal - (objective 0).toReal -
      (1 / 2 : ℝ) * (1 / 2 : ℝ) * (1 / 2 : ℝ) * ‖query - (-query)‖ ^ 2 =
        (1 / 2 : ℝ)
'''
second='''theorem absent_support_vacuity :
    SourceProper negativeSquare ∧
    (∀ p : ℝ, SourceSubdifferential negativeSquare p = ∅) ∧
    (∀ p q : ℝ, ∀ g ∈ SourceSubdifferential negativeSquare p,
      (negativeSquare p).toReal + inner ℝ g (q - p) +
        ((0 : ℝ) / 2) * ‖q - p‖ ^ 2 ≤ (negativeSquare q).toReal) ∧
    ¬ (∀ x y : ℝ, ∀ a : ℝ, 0 < a → a < 1 →
      negativeSquare (a • x + (1 - a) • y) ≤
        (a : EReal) * negativeSquare x + ((1 - a : ℝ) : EReal) * negativeSquare y -
          ((((0 : ℝ) / 2) * a * (1 - a) * ‖x - y‖ ^ 2 : ℝ) : EReal)) ∧
    negativeSquare 0 = (0 : EReal) ∧
    (1 / 2 : EReal) * negativeSquare (-1) +
      (1 / 2 : EReal) * negativeSquare 1 = (-1 : EReal)
'''
suffix='\nend BanditRL.Tests.OnlineStrongConvexSubgradientIffCanary\n'
put('canonical-context-v1.txt',context)
put('box-converse-header-v1.txt',first)
put('vacuity-header-v1.txt',second)
put('canonical-context-and-statements-v1.txt',context+first+'\n'+second+suffix)
put('scratch-context-and-statements-v1.txt',(context+first+'\n'+second+suffix).replace('import BanditRLProof.OnlineStrongConvexSubgradientIff','import FullIffCandidate',1))
put('contract-proposal-v1.json',dict(status='UNFROZEN_UNELABORATED_STATEMENT_PROPOSAL_ONLY_NO_BODY',source='Orabona v10 Definition4.1/Lemma4.2 printed34/PDF46; printed proof35/PDF47 equality correction.',minimality='Two closed declarations. First combines actual converse consumer, all-point global support production, scaled-coordinate norm discriminator and strict source residual; second isolates necessity of hsub with lambda0. Empty-V canary deferred: lawful edge documented in core, but adds less distinct discrimination here.',binder_ledger={'context':'Concrete definitions only; original E=Fin2→R has sup norm; U carries coordinate Euclidean pairing; e=2 times canonical algebraic coordinates. Objective globally finite quadratic, feasible box is restriction only. No top-outside indicator is claimed or needed.','public_parameters':'None. Both theorems are closed. No component curvature, support, domain, or performance premise is exposed.','quantifiers':'All point supports produced at every p in box; growth holds for EVERY global g, not only displayed covector. First interpolation requires strict source weights. Negative case has all real endpoints and no source support existence.'},first_conj_provider={'required':'Iff.mpr of stronglyConvex_iff_sourceSubgradient_growth at d2,e=scaledCoordinates,f=objective,V=feasible,lam1 with internally proved properness, convex box, nonnegative coefficient, all-point hsub, and independently proved EVERY-g growth.','forbidden':'Do not prove growth by calling the forward iff/adapter using the desired interpolation; do not merely return an independently proved interpolation with a decorative iff call.','genuine_growth_route':'Global quadratic supports have unique covector=(p+(1,0))/2 in scaled coordinates. Derive this algebraically from the global support inequality at a displacement chosen from the gradient mismatch; the residual squared sum forces mismatch zero. Then exact quadratic expansion bounds sup-norm squared by sum of squares. No prior strong interpolation theorem is used to derive the growth premise.','global_hsub':'For each feasible p (indeed every ambient p), displayed covector supports at every ambient coordinate u by nonnegative quadratic remainder. Globals remain globals; no merely box-local support.','norm_discrimination':'At q=(1,1), original squared norm1, scaled coordinate squared norm8, covector pairing1, f(q)=2. Wrong coordinate penalty yields5<=2 and is explicitly negated.','strict_source_residual':'At x=q,y=-q,a=1/2,z0,g=covector0, weighted pairings cancel, but weighted function/curvature residual=1/2. Thus printed equality to0 is false; source corrected inequality remains true.'},negative_case={'function':'f(t)=-t^2 is globally real/proper, V=R convex, lambda0.','support_empty_route':'For any p and supposed scalar g, test the global inequality at p+1 and p-1. Expanding gives g<=-2p-1 and g>=-2p+1, contradiction.','vacuous_growth':'Every support-indexed implication is true because no support exists, with no use of iff under invalid hsub.','interpolation_false':'x=-1,y=1,a=1/2 gives0<=-1, false.','source_scope':'Counterexample to REMOVING hsub, not to Lemma4.2. Properness and domain inclusion alone do not make right-side universal supports nonvacuous.'},pending=['Independent source review and exact public-header freeze','Canonical versus scratch import authorization','BODY and imported precise converse provider audit','No declaration-count/chapter/benchmark completion'],Lean_processes_started=0,source_identity_blind_policy='Supply only canonical context/statements or their transparent scratch import variant to future blind actor; keep this contract and source annotations separate.'))
put('manifest-v1.json',dict(status='PROPOSAL_ONLY',artifacts=[rec(p) for p in sorted(P.iterdir()) if p.is_file()]))
print(json.dumps(rec(P/'canonical-context-and-statements-v1.txt')))
