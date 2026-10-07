"""Freeze the required unnumbered two-dimensional source observation, before proofs."""
from pathlib import Path
import hashlib,json,subprocess,sys
sys.stdout.reconfigure(encoding='utf-8')
R=Path(__file__).resolve().parent; ROOT=R.parents[1]
assert Path('.').resolve()==ROOT
BASE='57f96796d3bbbb42486a547cecce7d6b3da6e4ef'
TASK='ONLINE-CONVEX-NONDIFFERENTIABILITY-20261007'
C=Path('docs/contracts/online-convex-nondifferentiability-v1')
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def write(p,x):
 p=Path(p);assert not p.exists(),p;p.parent.mkdir(parents=True,exist_ok=True)
 p.write_bytes(x if isinstance(x,bytes) else (x.rstrip('\n')+'\n' if isinstance(x,str) else json.dumps(x,ensure_ascii=False,indent=2)+'\n').encode('utf-8'))
assert subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()==BASE
assert subprocess.check_output(['git','branch','--show-current'],text=True).strip()=='codex/research-online-convex-nondifferentiability'
write(R/'.gitattributes','* -text')
old=Path('runs/online-lipschitz-migration-20261007')
write(R/'run-command.py',(old/'run-command.py').read_bytes())
write(R/'scoped-reference-index-v1.py',(old/'scoped-reference-index-v1.py').read_bytes())
pr=json.loads(subprocess.check_output(['gh','api','repos/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/pulls/176']))
assert pr['head']['sha']==BASE and pr['state']=='open' and pr['draft'] and not pr['merged'];write(R/'base-PR176-fresh-v1.json',pr)
main=subprocess.check_output(['git','-C','E:/ABRL/research','rev-parse','HEAD','origin/main'],text=True).splitlines()
assert main[0]==main[1] and not subprocess.check_output(['git','-C','E:/ABRL/research','status','--porcelain'],text=True).strip()
write(R/'canonical-worktree-audit-v1.json',dict(canonical_main=main[0],canonical_clean=True,origin_main=main[1],fresh_fetch_preceded_initialization=True,exact_stacked_base=BASE,base_PR=176,base_OPEN_DRAFT_unmerged=True,worktrees=subprocess.check_output(['git','worktree','list','--porcelain'],text=True),shared_git='E:/ABRL/research/.git',other_checkouts_stores_links_preserved=True))
pdf=Path('../research-online-ogd/tmp/pdfs/orabona-v10.pdf');image=Path('tmp/online-lipschitz-source-pdf31-v1.png')
assert sha(pdf)=='cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17'
from pypdf import PdfReader
write(R/'source-printed19-pdf31.txt',PdfReader(str(pdf)).pages[30].extract_text())
write(C/'source-card.json',dict(id='ORABONA-V10-CH2-UNNUMBERED-2D-NONDIFFERENTIABILITY',source_url='https://arxiv.org/pdf/1912.13213v10',version='21June2026 v10',cached_PDF=pdf.as_posix(),sha256=sha(pdf),printed_page=19,pdf_page=31,image=image.as_posix(),image_sha256=sha(image),anchor='Final convex-analysis paragraph before section2.3',source_statement='The real-valued function f:R2->R, f(x)=|x1|, is convex and not differentiable on the segment from (0,0) to (0,1).',required=True,unnumbered_maintext=True,old_inventory_omission_is_required_enumeration_gap=True,independent_exercise=False,chapter_complete=False,goal_complete=False))
imports='import Mathlib.Analysis.InnerProductSpace.PiL2\nimport Mathlib.Analysis.Calculus.Deriv.Abs\nimport Mathlib.Analysis.Normed.Module.Convex\n'
definition='def coordinateAbsolute (x : EuclideanSpace ℝ (Fin 2)) : ℝ := |x 0|'
headers={
 'coordinateAbsolute':definition.split(' :=')[0],
 'coordinate_absolute_convex':'theorem coordinate_absolute_convex :\n    ConvexOn ℝ Set.univ coordinateAbsolute',
 'coordinate_absolute_not_differentiable':'theorem coordinate_absolute_not_differentiable (x : EuclideanSpace ℝ (Fin 2))\n    (hx : x 0 = 0) : ¬ DifferentiableAt ℝ coordinateAbsolute x',
 'convex_nondifferentiable_segment':'theorem convex_nondifferentiable_segment :\n    ConvexOn ℝ Set.univ coordinateAbsolute ∧\n    ∀ x ∈ segment ℝ (0 : EuclideanSpace ℝ (Fin 2)) (PiLp.single 2 1 1),\n      ¬ DifferentiableAt ℝ coordinateAbsolute x'}
write(C/'headers.json',{n:dict(statement=s,sha256=hashlib.sha256(s.encode()).hexdigest(),kind='def' if n=='coordinateAbsolute' else 'theorem') for n,s in headers.items()})
write(C/'complete-definition.lean',imports+'\nnamespace BanditRL.OnlineConvex\n'+definition+'\nend BanditRL.OnlineConvex\n')
propositions=['ConvexOn ℝ Set.univ coordinateAbsolute','∀ x : EuclideanSpace ℝ (Fin 2), x 0 = 0 → ¬ DifferentiableAt ℝ coordinateAbsolute x','ConvexOn ℝ Set.univ coordinateAbsolute ∧ ∀ x ∈ segment ℝ (0 : EuclideanSpace ℝ (Fin 2)) (PiLp.single 2 1 1), ¬ DifferentiableAt ℝ coordinateAbsolute x']
write(R/'leaves/target-types-v1.lean',imports+'\nnamespace BanditRL.OnlineConvex\n'+definition+'\n'+'\n'.join('#check ('+s+')' for s in propositions)+'\n#print coordinateAbsolute\nend BanditRL.OnlineConvex\n')
apis=['PiLp.proj','PiLp.projₗ','PiLp.continuousLinearEquiv','convexOn_univ_norm','ConvexOn.comp_linearMap','not_differentiableAt_abs_zero','DifferentiableAt.comp','DifferentiableAt.abs','ContinuousLinearMap.differentiableAt','ContinuousLinearEquiv.differentiableAt','PiLp.single_eq_same','PiLp.single_eq_of_ne','Set.segment','Set.left_mem_segment','Set.right_mem_segment']
write(R/'leaves/pinned-APIs-v1.lean',imports+'\n'+'\n'.join('#check @'+n for n in apis))
fixed_paths=['lean-toolchain','lakefile.lean','lake-manifest.json','runs/active_frontier.json','BanditRLProof.lean','Tests.lean','BanditRLProof/OnlineLipschitzSubgradient.lean','Tests/OnlineLipschitzSubgradientCanary.lean','BanditRLProof/OnlineSubgradientDifferentiability.lean','BanditRLProof/OnlineSubgradientAbsolute.lean','BanditRLProof/OnlineAffineSubgradient.lean','docs/contracts/online-book-v1/source-inventory.json','website/content/readings.json','website/content/highlights.json','website/content/chapters.json']
for p in fixed_paths:write(R/'snapshots'/('before-'+p.replace('/','--')+'.txt'),Path(p).read_bytes())
write(R/'draft-freeze-v1.json',dict(stage='draft',exact_base=BASE,headers={n:hashlib.sha256(s.encode()).hexdigest() for n,s in headers.items()},complete_definition_sha256=sha(C/'complete-definition.lean'),fixed_files={p:sha(p) for p in fixed_paths},new_public_definitions=1,new_public_proofs=3,source_observations=1,source_numbered_results=0,proof_ready=False,source_package_accepted=False,chapter_complete=False,goal_complete=False))
contract='''# Required unnumbered convex nondifferentiability observation, v1

Source: Orabona arXiv1912.13213v10 (21June2026), printed19/PDF31, final convex-analysis paragraph before section2.3. Required maintext, not an independent exercise. f:R2->R, f(x)=|x1| is convex and not differentiable anywhere on the CLOSED segment from (0,0) to (0,1), including both endpoints. The old numbered inventory omitted this unnumbered observation; this is a required enumeration gap, not an excluded or zero obligation.

Exact Lean definition/three headers are frozen in headers.json and complete-definition.lean. EuclideanSpace real Fin2 is the actual Euclidean L2 norm topology. Lean index0 denotes printed x1; index1 is printed second coordinate. coordinateAbsolute is an everywhere real-valued function, not an EReal.toReal projection. ConvexOn real univ is global convexity. DifferentiableAt real is the ordinary AMBIENT Frechet notion at each query, not differentiability along/within the vertical segment. The intended stronger reusable leaf proves failure at ALL points with first coordinate zero, with no restriction on the second coordinate; the exact source terminal also proves global convexity and specializes the ALL segment quantifier. No supplied convexity/nondifferentiability oracle, scalar-only witness or single-point substitute.

Dependency route: pull convexity of real norm/absolute value through the actual first-coordinate linear map; for p0=0 restrict a hypothetical ambient derivative to the differentiable horizontal curve t->p+t e1, obtaining differentiability of scalar abs at0, contradicted by the actual pinned theorem. Segment membership has coordinate0=0 by its true convex-combination definition, giving the same terminal. This is one lower route. Real finite dimension2 is source-exact; no probability/online feedback/regret/support-selection assumption. No claim about nondifferentiability of the function RESTRICTED to the vertical segment, where it is constant. No general measure-zero differentiability theorem or additional arbitrary-dimensional extension.

Before theorem bodies: actual existing declaration/memory/pinned API search; compile complete definition and target propositions without axioms/sorry; distinct neutral decoder and anti-anchored source reviewer perform seven-slot CONTRACT review. Definition plus target types alone are NOT theorem compilation. Stabilize native headers after actual source review; prove only these dependency-ready leaves. Preserve source/headers/definition bytes; any target change requires a new version and review.

Allowed edits: new BanditRLProof/OnlineConvexNondifferentiability.lean; new Tests/OnlineConvexNondifferentiabilityCanary.lean; additive imports in shared BanditRLProof.lean/Tests.lean; a source-qualified third observation card/notation/highlight/curated links in existing online-lipschitz reader subtree; additive unnumbered inventory overlay; scoped native journals/task/contracts/evidence/contribution manifest. No existing mathematics/pins/otherBook reader changes, no per-book proof tree. Actual shared declaration export/registry must incorporate new nodes, preserving old IDs/URLs. Conceptual audit none-found-with-reason unless actual separate bridge evidence exists. Global SGB frontier unchanged.

Nondegenerate canaries: source closed segment endpoints and nonzero vertical interior query (0,1/2); ambient failure at every vertical coordinate including outside the segment; ordinary ambient differentiability off the axis at first coordinate+1 and -1. Explicit actual dimension2/finite real values/coordinate order. Scalar abs failure alone does not close the 2D terminal; contrast ambient failure with genuinely constant vertical restriction.

Acceptance separately requires actual theorem bodies/focused build/public named types/axiom audit/frozen guards/actual dependency values; BODY semantic review; sharedroot/Tests/fullharness/current shadow/exactPRbase contributor/fullhistory/source-qualified mapping/currentsite checks and actualpixels; FINAL semantic review/nativeaccepted/real appattached draftPR. File/actor conventions and CLI-enforced gates remain distinct. Zero exits are command evidence, never automatic compiled labels.

Stacked base is OPEN DRAFT PR176 exact57f96796d3bbbb42486a547cecce7d6b3da6e4ef; canonicalmain6847b678a73db68dee5101d6f05c2453c1405afc remains clean/unmerged. Legacyqueue0 is not Chapter2 mandatory total; Chapter2 totalnull/incomplete. All remaining Chapter1/2 maintext, Lemma2.31/causal OSD/linearization/Example2.32/unitanalysis/nine OTHER Chapter1 main-relative contract gaps/necessaryappendices REQUIRED; chapters3-16 unenumerated, wholeGoal ACTIVE/unbudgeted. No merge/deploy/mainlive/retirement/private/anonymous/generated_site edits.
'''
write(C/'contract.md',contract)
for directory in ['tasks','conversion-windows','proof-obligations']:write(Path(directory)/(TASK+'.md'),contract)
write(C/'initial-dependency-DAG.json',dict(terminal='BanditRL.OnlineConvex.convex_nondifferentiable_segment',dependencies={'coordinate_absolute_convex':['coordinateAbsolute','convexOn_univ_norm','ConvexOn.comp_linearMap','PiLp.projₗ'],'coordinate_absolute_not_differentiable':['coordinateAbsolute','PiLp.continuousLinearEquiv','DifferentiableAt.comp','not_differentiableAt_abs_zero'],'convex_nondifferentiable_segment':['coordinate_absolute_convex','coordinate_absolute_not_differentiable','Set.segment']},status='architectural obligations; compiled actual value graph pending'))
write(R/'00_context.md','WholeGoalACTIVE/unbudgeted, requestedGPT6Astra medium. ExactPR176base57f96796, cleanDIRECT429nonignoredraw/oneignoredruntime/localremoteRESTmatch verified beforebranch. Freshcanonicalfetch/mainclean; othercheckoutsstoreslinks preserved. Required unnumbered source observation, new proof package, not another migration-count completion. ExistingPDF reused/freshSHA/extraction; no versionchange. Currentsourcepage requires fresh actualpixel view. CONTRACT/decoder/reviewer/body/allgates/PRpending. Prior source/read/reader/adapter failures preserved in oldruns. Readonly prior exploration guessed nonexistent OnlineAbsoluteSubgradient.lean/freeze-draft-v1.py/tools/book_registry.py; corrected actualcatalog paths, no mathematical or gate failure implied.')
write(R/'10_upper_director-v1.md','Required exact 2D convex+ALLclosedsegment ambient nondifferentiability source terminal. One lower proof route via actual linear coordinate and differentiable horizontal restriction. Old migrations legacy0 is not chaptercomplete; add unnumbered inventory overlay. No OSD competing proof work until this package gate.')
write(R/'20_architect-v1.md','Pull realnorm convexity through actual PiLp firstcoordinate linear map. If ambient f differentiable at p with p0=0, comp along smooth t->p+t e1 gives scalarabs differentiableat0, contradiction. Segment true membership forces firstcoordinate0. Nonzero (0,1/2) + offaxis ±1 and constant verticalrestriction verify semantic boundary; not subgradient-oracle consumer.')
write(R/'memory_digest.md','Required unnumbered2D observation found; draftexactrealEuclidean2/globalconvex/ambientFrechet failure onALLclosedsegmentinclendpoints. Strongerleaf ALLverticalaxis explicitlyqualified. Definition/target-types-only not proof. Sourceblind/source review/gatespending, GoalACTIVE.')
write(R/'retrieval-index-v1.md','ORABONA-V10-CH2-UNNUMBERED-2D-NONDIFFERENTIABILITY; actual pinned Mathlib normconvexity/PiLp maps/scalarabs nonderivative/composition/segment. Project search and compiled API checks pending. No newgeneric duplicate or externaluncheckeddependency.')
write(R/'initialized-before-first-use-v1.json',dict(rows=[dict(path=p.as_posix(),sha256=sha(p)) for p in [*R.glob('*.py'),*(R/'leaves').glob('*.lean')]],source_package_accepted=False,chapter_complete=False,goal_complete=False))
print('Required unnumbered2D source target frozen; 1def/3prospectiveproofs, NOTyetcompiled/stabilized.')
