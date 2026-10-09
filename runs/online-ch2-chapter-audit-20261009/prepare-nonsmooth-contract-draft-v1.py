from common_v1 import *
import base64
fixed()
sys.path.insert(0,str(ROOT))
from tools.abrl_lifecycle import statement_hash

queries=[['reference-index'],['list-mathlib'],['list-papers'],['list-weapons'],
 ['search-memory','hinge'],['search-memory','absolute'],
 ['list-lean-decls','hinge'],['list-lean-decls','hinge','--statement'],
 ['list-lean-decls','SourceDifferentiableAt','--statement'],
 ['list-lean-decls','coordinate_absolute_not_differentiable','--statement']]
for i,args in enumerate(queries):
 tick=time.monotonic()
 p=subprocess.run([sys.executable,'-B','-X','utf8',str(RUN/'retrieval-scoped-v1.py')]+args,cwd=str(ROOT),stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 write(RUN/('nonsmooth-retrieval-command-%02d-v1.json'%i),dict(command=[sys.executable,'-B','-X','utf8','OWN retrieval-scoped-v1.py']+args,
  cwd=ROOT.as_posix(),actual_exit=p.returncode,seconds=time.monotonic()-tick,stdout_sha256=hashlib.sha256(p.stdout).hexdigest(),stdout_base64=base64.b64encode(p.stdout).decode('ascii')))
 assert p.returncode==0,args

headers=[
 ('shifted_absolute_convex_differentiable_iff','''theorem shifted_absolute_convex_differentiable_iff (c : ℝ) :
    ConvexOn ℝ Set.univ (fun x : ℝ => |x - c|) ∧
      ∀ x : ℝ, DifferentiableAt ℝ (fun w : ℝ => |w - c|) x ↔ x ≠ c'''),
 ('hinge_convex_differentiable_iff','''theorem hinge_convex_differentiable_iff {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (a : E) :
    ConvexOn ℝ Set.univ (fun x : E => max (1 - inner ℝ a x) 0) ∧
      ∀ x : E, DifferentiableAt ℝ (fun w : E => max (1 - inner ℝ a w) 0) x ↔
        inner ℝ a x ≠ 1'''),
 ('labelled_hinge_convex_differentiable_iff','''theorem labelled_hinge_convex_differentiable_iff {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (y : ℝ) (z : E) :
    ConvexOn ℝ Set.univ (fun x : E => max (1 - y * inner ℝ z x) 0) ∧
      (∀ x : E, DifferentiableAt ℝ (fun w : E => max (1 - y * inner ℝ z w) 0) x ↔
        y * inner ℝ z x ≠ 1) ∧
      (Differentiable ℝ (fun w : E => max (1 - y * inner ℝ z w) 0) ↔ y • z = 0)''')]
targets=[]
for name,header in headers:
 targets.append(dict(declaration='BanditRL.OnlineConvex.'+name,owning_module='BanditRLProof/OnlineNonsmoothExamples.lean',
  exact_proposed_header=header,statement_hash=statement_hash(header),phase='draft before distinct blind/source review'))
write(CONTRACT/'nonsmooth-targets-draft-v1.json',dict(
 stage='DRAFT finite dependency-ready new leaf, three proposed public terminals for two main-text example families',
 source_card='ORABONA-V10-CH2-NONSMOOTH-INTRO-P16',source_sha256=PDF_SHA,
 source_anchor='Section2.2 opening paragraph printed16/PDF28: |x-10| and max(1-y_t inner(z_t,x),0)',
 exact_source_text='For example, ℓt(x)=|x−10|. ... For example, the hinge loss, ℓt(x)=max(1−yt⟨zt,x⟩,0), is not differentiable.',
 source_fingerprint=load(CONTRACT/'source-fingerprint-v1.json')['source_pages'][8],
 mathematical_progress_boundary='Actual ambient convexity and differentiability/nondifferentiability criteria close the introductory examples, reusing accepted full subdifferential and singleton-gradient producers. Not just a numerical sample or support-formula consumer; zero-labelled/zero-feature constant cases exposed.',
 targets=targets,
 proposed_source_repair=dict(pinned_source_unchanged=True,
  original_ambiguity='Unqualified hinge is not differentiable could be read as every point or every label/feature, both false. Labels/features are unconstrained in the displayed paragraph.',
  explicit_proposal='At each point, the hinge is differentiable iff its affine margin is not exactly zero. It is globally differentiable iff y•z=0; otherwise a genuine boundary kink exists. This is an explicit qualification, not author-endorsed erratum.',
  simple_counterexample='y=0 or z=0 gives constant max(1,0)=1, differentiable everywhere.',
  required_review='distinct anti-anchored source review and separate repair verdict; no silent replacement of pinned wording'),
 seven_slots=dict(objects='scalar shifted absolute loss; labelled real finite-dimensional inner-product hinge, including EuclideanSpace real(Fin d) for every d, including0',
  quantifiers='all shifts c, labels y, features z and query x; all ambient points for global Differentiable criterion',
  assumptions='only stated real normed inner-product finite-dimensional ambient structure; no nonzero label/feature, label±1, bounded norm/domain, probability or derivative-oracle premise',
  conclusion='global convexity and exact ambient Fréchet DifferentiableAt iff; labelled terminal also exact global Differentiable iff effective normal y•z vanishes',
  constants='absolute thresholdc includes printed10; hinge margin1 and zero floor0 unchanged; pointwise and global differentiability distinguished',
  information='static deterministic loss functions, no learner/policy/feedback assertion or supplied support conclusion',
  boundary='genuine kink only on margin equality; zero effective normal is constant1 and smooth; no source claim that every point of a nonconstant hinge is nonsmooth, no chapter/Goal completion'),
 reuse_plan=dict(decision='adapt_existing',
  existing=['BanditRL.OnlineConvex.example_2_27','BanditRL.OnlineConvex.affine_convex','BanditRL.OnlineConvex.convexExtended_coe_iff','BanditRL.OnlineConvex.theorem_2_22_gradient','not_differentiableAt_abs_zero','DifferentiableAt.abs','ConvexOn.sup','convexOn_univ_norm','ConvexOn.comp_affineMap','convexOn_const'],
  intended_route='Absolute translation and smoothness off0; max of two affine functions convex. Genuine hinge kink: two distinct actual supports from accepted full hinge formula contradict differentiable singleton support. Off boundary use local equality with one affine branch. Label normal a=y•z. Global necessity constructs x=(inner a a)^(-1)•a when a≠0, giving inner a x=1.',
  status='project-local source examples; any reusable generic leaf mathlib-candidate, no dependency/toolchain change',
  retrieval_cards=['MLIB-CONVEX-LINALG','MLIB-ORDER-ALGEBRA'],
  proof_weapon='none; existing concrete convex/subgradient/calculus APIs, no inspiration certified as proof'),
 permitted_edits=['OWN RUN/contract/task/obligation/conversion files','NEW BanditRLProof/OnlineNonsmoothExamples.lean','NEW Tests/OnlineNonsmoothExamplesCanary.lean','later public roots append imports and bounded reader/registry contribution after candidate validation'],
 forbidden='No old production/Test/header changes, source mutation, root reordering, pin upgrades, global active SGB/frontier/trials/memory rewrite, generated _site, Chapter3+ competitive proof writing',
 review_pending=['blind decode of exact proposed terminal types','anti-anchored source and explicit-repair contract review'],chapter_complete=False,whole_Goal_status='ACTIVE'))

neutral=[]
for i,(_,header) in enumerate(headers,1):
 neutral.append(header.replace('theorem '+headers[i-1][0],'theorem Terminal%d'%i,1))
packet='''# Neutral statement-only reconstruction packet

Read only this packet and context; do not search repository/source/history, infer source identity, or prove/check anything. Reconstruct each exact terminal in natural language and LaTeX, all seven semantic slots, degenerate cases and distinction between local-point and global differentiability. Source identity and prior verdict deliberately absent.

Notation: real normed inner-product finite-dimensional E; inner is real inner product; ConvexOn on Set.univ is ambient global convexity; DifferentiableAt is ordinary ambient real Fréchet differentiability at the specified point; Differentiable means at every ambient point; y•z is real scalar multiplication. No hidden section variables.

```lean
open scoped InnerProductSpace
'''+ '\n\n'.join(neutral)+'\n```\n'
write(RUN/'nonsmooth-blind-packet-v1.md',packet)
write(RUN/'nonsmooth-blind-input-v1.json',dict(packet_path=(RUN/'nonsmooth-blind-packet-v1.md').as_posix(),packet_sha256=sha(RUN/'nonsmooth-blind-packet-v1.md'),
 input_scope='Only this neutral packet and notation. Statement-only draft, no proof, source identity, prior review or result claims.'))
fixed();print('Actual scoped reference index/retrieval commands completed; exact three-terminal draft and source-blind packet prepared before proof coding.')
