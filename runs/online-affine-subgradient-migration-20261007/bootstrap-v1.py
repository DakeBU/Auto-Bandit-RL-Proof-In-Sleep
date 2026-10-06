"""Freeze faithful Theorem2.28 reuse after actual parent delivery; no inherited acceptance."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
ROOT=Path('.').resolve();RUN=Path(__file__).resolve().parent
assert ROOT==RUN.parents[1]
BASE='42da35d05a3cbc26f5ec6b5082ef9135b7d7caf7'
PUBLIC=Path('BanditRLProof/OnlineAffineSubgradient.lean');CANARY=Path('Tests/OnlineAffineSubgradientCanary.lean')
CONTRACT=Path('docs/contracts/online-affine-subgradient-migration-v1');TASK='ONLINE-AFFINE-SUBGRADIENT-MIGRATION-20261007';PRE='BanditRL.OnlineConvex.'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'))
def write(p,x):
 p=Path(p);assert not p.exists(),p;p.parent.mkdir(parents=True,exist_ok=True)
 p.write_bytes(x if isinstance(x,bytes) else ((x.rstrip('\n')+'\n') if isinstance(x,str) else json.dumps(x,ensure_ascii=False,indent=2)+'\n').encode())
assert subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf-8').strip()==BASE
assert subprocess.check_output(['git','branch','--show-current'],encoding='utf-8').strip()=='codex/research-online-affine-subgradient-migration'
sys.path.insert(0,str(ROOT));from tools.abrl_lifecycle import lean_declaration_header
decls=re.findall(r'^(theorem|def)\s+(\w+)\b',PUBLIC.read_text(encoding='utf-8'),re.M);assert decls==[('theorem','theorem_2_28')]
h=lean_declaration_header(PUBLIC,'theorem_2_28');hh=hashlib.sha256(h.encode()).hexdigest()
assert hh==load('docs/contracts/online-affine-subgradient-v1/contract-manifest.json')['statement_hash']
headers={'theorem_2_28':dict(statement=h,hash=hh,kind='theorem')};write(CONTRACT/'headers.json',headers)
borrowed={}
for file,names in [('BanditRLProof/OnlineSubgradientBasic.lean',['SourceSubdifferential']),('BanditRLProof/OnlineClosedProper.lean',['SourceProper']),('BanditRLProof/OnlineConvexExtended.lean',['effectiveDomain','realEpigraph','IsConvexExtended'])]:
 t=Path(file).read_text(encoding='utf-8')
 for n in names:
  m=re.search(r'(?m)^def '+n+r'\b.*?(?=\n\s*(?:/--|theorem|def)\b)',t,re.S);assert m,(file,n)
  borrowed[n]=dict(body=m.group(0).split('\n/--')[0].strip(),owner=file,owner_sha256=sha(file))
write(CONTRACT/'scoped-contexts.json',dict(ambient='variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]',owned_definitions={},borrowed_definitions=borrowed,production_contexts=['SourceSubdifferential','SourceProper'],canary_contexts=['effectiveDomain','realEpigraph','IsConvexExtended'],actual_implicit_binders='Primary theorem adds BOTH real finite dimensions, whose completeness instances supply actual adjoint. Borrowed properness arbitrary carrier; support intrinsic norm/inner; no blanket FD on shared definitions.'))
snap=[]
files=[PUBLIC,CANARY,*map(Path,['BanditRLProof.lean','Tests.lean','lean-toolchain','lakefile.lean','lake-manifest.json','runs/active_frontier.json','runs/lifecycle_sessions.jsonl','runs/trials.jsonl','MANIFEST.md','website/content/readings.json','website/content/highlights.json','website/content/chapters.json','BanditRLProof/OnlineHinge.lean','BanditRLProof/OnlineSubgradientAbsolute.lean']),*map(Path,sorted({r['owner'] for r in borrowed.values()}))]
for p in files:
 q=RUN/'snapshots'/('before-'+p.as_posix().replace('/','--')+'.txt');write(q,p.read_bytes());snap.append(dict(path=p.as_posix(),raw_sha256=sha(p),snapshot=q.as_posix()))
write(RUN/'historical-raw-supersession-v1.json',dict(rows=snap,prior_files_preserved=True))
canary=re.findall(r'^(theorem|(?:noncomputable )?def)\s+(\w+)\b',CANARY.read_text(encoding='utf-8'),re.M)
cp=['AffineProbe.'+n for k,n in canary if k=='theorem'];cd=['AffineProbe.'+n for k,n in canary if k!='theorem'];assert len(cp)==7 and len(cd)==2
fixed=[p.as_posix() for p in files if p.suffix=='.lean' and p not in [PUBLIC,CANARY]]+['lean-toolchain','lakefile.lean','lake-manifest.json','runs/active_frontier.json']
write(RUN/'draft-freeze-v1.json',dict(stage='draft',headers={'theorem_2_28':hh},proof_names=['theorem_2_28'],definition_names=[],original_module_sha256=sha(PUBLIC),whole_old_canary={CANARY.as_posix():sha(CANARY)},fixed_shared_files={p:sha(p) for p in fixed},retained_public_proofs=1,retained_public_definitions=0,whole_canary_proofs=7,whole_canary_definitions=2,new_public_proofs=0,new_definitions=0,new_test_proofs=0,source_formal_results=1,source_package_accepted=False,chapter_complete=False,goal_complete=False))
targets=[PRE+'theorem_2_28']+cp+cd
write(RUN/'public-named-declarations-v1.json',dict(production=[PRE+'theorem_2_28'],production_proofs=[PRE+'theorem_2_28'],production_definitions=[],whole_canary_proofs=cp,whole_canary_definitions=cd,axiom_probe=targets,unique_checks=10))
pdf=Path('../research-online-ogd/tmp/pdfs/orabona-v10.pdf');assert sha(pdf)=='cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17'
from pypdf import PdfReader
write(RUN/'source-printed18-pdf30.txt',PdfReader(str(pdf)).pages[29].extract_text())
img=Path('tmp/online-subgradient-sum-source-pdf30-v1.png');assert sha(img)=='c4354de7297923fd82f74645ddd50fdb582f90b6eeb9a7536fd9f33ec5489ebd'
write(CONTRACT/'source-card.json',dict(id='ORABONA-V10-T2.28',version='arXiv1912.13213v10,21June2026',url='https://arxiv.org/pdf/1912.13213v10',cached_PDF=pdf.as_posix(),sha256=sha(pdf),printed_page=18,PDF_page=30,image=img.as_posix(),image_sha256=sha(img),source_formal_results=1,exact_terminal=PRE+'theorem_2_28',independent_exercises_excluded=[],chapter_complete=False,goal_complete=False))
prior=Path('runs/online-hinge-migration-20261007');entries=subprocess.check_output(['git','ls-tree','-r','-z',BASE,'--',prior.as_posix()]).split(b'\0');objects={e.split(b'\t',1)[1].decode():e.split(b'\t',1)[0].split()[2].decode() for e in entries if e};bound=[];ignored=[];cache={}
for p in sorted(prior.rglob('*')):
 if not p.is_file():continue
 q=subprocess.run(['git','check-ignore','-q','--',p.as_posix()]);assert q.returncode in [0,1]
 if q.returncode==0:ignored.append(p.as_posix());continue
 assert p.as_posix() in objects;obj=objects[p.as_posix()]
 if obj not in cache:cache[obj]=subprocess.check_output(['git','cat-file','blob',obj])
 assert cache[obj]==p.read_bytes(),p;bound.append(dict(path=p.as_posix(),git_blob=obj,raw_sha256=sha(p)))
assert len(bound)==509
write(RUN/'prior-delivery-raw-binding-v1.json',dict(status='passed',exact_PR174_head=BASE,raw_files=len(bound),rows=bound,ignored_runtime_preserved=ignored,prior_PR='OPEN-DRAFT-unmerged',prior_failure='Actual raw auditv1 failed due CRLF Git normalization; reviewed bytes preserved/tasklocal -text repairv2 and DIRECT509rawpassed, original failure retained.'))
contract='''# Theorem2.28 affine transport source contract v1 — current draft

One mandatory printed Theorem2.28, printed18/PDF30. Source arbitrary proper f:Rm->(-infinity,+infinity], every matrix A in R^(m*d), b in Rm and x in Rd; h(y)=f(Ay+b). Exact full set-image inclusion A-transpose ∂f(Ax+b) SUBSET ∂h(x). No convexity, differentiability, continuity, closedness, Lipschitz, rank, injectivity, surjectivity, nonzero A/b, dimension positivity or equality claim. The actual composition is inline and the actual adjoint is used, never supplied support/adjoint formula. Every g in the entire source support set and every ambient target y are quantified. Deterministic convex analysis, no feedback/probability/regret/selection guarantee.

Representation: arbitrary coordinate-free finite-dimensional real inner-product E/F include source Euclidean instances. Both FD are explicit; finite-dimensional completeness supplies Mathlib adjoint with no extra CompleteSpace. Continuous linear A models the matrix; automatic finite-dimensional continuity and adjoint/transpose under orthonormal coordinates are explained, but no separate coordinate-isometry/functor certificate is constructed. hp:SourceProper f remains an explicit SOURCE premise even though the retained body uses only global support algebra. Borrowed SourceProper globally excludes bottom and exhibits one finite witness, on arbitrary carriers. Borrowed SourceSubdifferential uses norm/inner and tests EVERY ambient point; beyond printed proper convention it admits improper inputs. f is proper here, h need not be separately proper. If queried f(Ax+b)=top, proper f has no global support there (finite witness contradicts top<=finite); left image empty, so inclusion is vacuous even if generic support of an all-top composite is all E. No hidden finite-query premise or composite-proper restriction. Source statement at outside domain is retained literally, not silently cut to effectiveDomain. Equality can fail.

Actual producer: destruct image witness g; hg(Ay+b) yields global support inequality for EVERY y; cancel b and rewrite linear subtraction to A(y-x); actual adjoint_inner_left transforms the inner product, preserving EReal inequality. Only one retained public proof, ZERO owned definitions/newproof/newTEST/newregistry. Whole existing seven scalar canary proofs/two TEST definitions retained: actual doubling map adjoint2g and proper |.|; nonzero A2/nonzero shift1/query-1/2 transports actual source g1/2 to target1. Proper nonconvex -|.| has empty source supports at0 (test +/-1) and fails convex epigraph midpoint; zero map/rankdeficiency gives exact empty image, actual constant0 composite supports{0}, strict inclusion and actual theorem use. No actual2D/matrix coordinate test or all-top composite canary claimed.

Freeze exact single header82587fe92f5705cd28adb86e7e554c97855a1930f46f660d79a5fc0a6fca2f76, original complete module, wholeoldcanary, borrowed contexts/shared source parents/roots/pins/globalSGB. Single lower retrieval-reuse route, no mathematical progress from declaration count. Current compilation, actual API/types/value dependencies, sourceblind neutral decoder and distinct anti-anchored CONTRACT precede stabilization; re-elaborate actual body/kernel/canary/nativefence before candidate. Full root/Tests/harness/exactstackbase contributor/scoped checks/taskshadow/sharedregistry/site/actualpixels plus distinct BODY/FINAL/native acceptance required before delivery. Required distinct automated actors requested Astra medium, no human/external/runtime attestation. CLI enforcement and file/prompt/role conventions distinct.

Only ordinary leading explanatory comment and online-affine-subgradient reader subtrees allowed after review. All original mathematical/canary/shared parent bytes fixed. Same Lean/Lake/mathlib4.29.1/Bookregistry; no Optlib/dependency upgrades or perBook graph duplication. Exact OPENdraftPR174 base42da35d05a3cbc26f5ec6b5082ef9135b7d7caf7, freshly canonicalmain/originmain6847b678a73db68dee5101d6f05c2453c1405afc clean/sharedGitE:/ABRL/research/.git; independent extended-topics38526b997f61d2d9af715bee51d711f91500ffe6 preserved. Old affine draft20261003 historical/unchanged, never inherit acceptance.

Legacy1->0 ONLY this package AFTER actual reviewedPR, and ZERO is NOT chapter completion or total mandatory count. Next source/audit all remaining Chapter1/2 maintext including Lipschitz/OSD/linearization and nineOTHERChapter1mainrelative contributorcontractgaps/necessaryappendix required. Chapter2mandatorytotalnull/incomplete, Chapters3-16unenumerated, wholeGoalACTIVE/unbudgeted. No merge/deploy/mainlive/_site/private/anonymous edits/worktree retirement.
'''
write(CONTRACT/'contract.md',contract)
write(CONTRACT/'initial-dependency-DAG.json',dict(status='source architecture only; compiled constant graph separate',terminal=PRE+'theorem_2_28',nodes={'theorem_2_28':['SourceSubdifferential','SourceProper','ContinuousLinearMap.map_sub','ContinuousLinearMap.adjoint_inner_left']},source_premise_unused_but_retained=['SourceProper f'],new_math_nodes=0))
write(RUN/'proof-obligations-draft-v1.json',dict(required_terminal=dict(name=PRE+'theorem_2_28',statement_hash=hh,state='draft sourcecontract'),canary_proofs=cp,canary_definitions=cd,legacy_before=1,chapter2_mandatory_total=None,chapter_complete=False,goal_complete=False))
for d in ['tasks','conversion-windows','proof-obligations']:write(Path(d)/(TASK+'.md'),contract)
write(RUN/'00_context.md','TotalGoalACTIVE/unbudgeted/requestedAstra medium. Freshfetchcanonicalmain/originmain6847b678a73db68dee5101d6f05c2453c1405afc clean, sharedGitE:/ABRL/research/.git; extended-topics38526b997f61d2d9af715bee51d711f91500ffe6 preserved. ActualPR174OPENdraft/unmerged/appattached DIRECT42da35d05a3cbc26f5ec6b5082ef9135b7d7caf7 clean/localremoteRESTsame/509rawmatched. Fresh scoped branch from this exactbase. Root actually reread PDF30 and original PNG this round. One retained source proof/7wholecanaryproof2TESTdefs/zero newmath. Parentrawfailure retained and fixed tasklocalattributes; current run exact-byte policy starts BEFORE first commit. Readonly860d47 guessed freeze-draft-v1.py nonexistent; actual rg/bootstrap then read, no gate inferred. No policyholds/deletion/merge/deploy/modelupgrade/competing futurechapter work.')
write(RUN/'10_upper_director-v1.md','Close only exact full-image inclusion for actual affine composition without convexity/rank/extra proper-composite/equality premise; reuse_existing one lower leaf. Required remaining entire maintext persists. Originalbody proof and sourcecontract/hp retained; no wrapper.')
write(RUN/'20_architect-v1.md','Imagewitness g -> actual hg(Ay+b) all targety -> cancel translation and map_sub -> actual adjoint_inner_left -> exact EReal support. FDcompleteness instances, no sourcefinitequery added; outdomain emptyimage boundary explicit. Canaries catch nonzero map+translation and proper nonconvex strict inclusion/rankzero.')
write(RUN/'memory-digest-draft-v1.md','Only T2.28draft; sourceproper/nonconvex permitted; inclusionONLY. CoordinatefreeFD/adjoint delta explicit, hpunusedretained/allquery genericproper convention. Legacy1pendingPR notallmandatorycount; Chapter2incomplete/3-16unenumerated/wholeGoalACTIVE.')
write(RUN/'retrieval-index-draft-v1.md','ORABONA-V10-T2.28; MLIB-CONVEX-LINALG. Actual sharedglobal-support+proper+map_sub+adjoint_inner_left. LocalMathlib retrieval/pinned#check/types/graph mustpass, no externalOptlib or coordinate certificate claimed.')
write(RUN/'leaves/actual-types-v1.lean','import Tests.OnlineAffineSubgradientCanary\nset_option pp.universes true\n'+'\n'.join('#check @'+n for n in targets)+'\n'+'\n'.join('#print '+PRE+n for n in borrowed))
write(RUN/'leaves/public-all-axioms-v1.lean','import Tests.OnlineAffineSubgradientCanary\n'+'\n'.join('#print axioms '+n for n in targets))
write(RUN/'leaves/pinned-APIs-v1.lean','import Tests.OnlineAffineSubgradientCanary\n'+'\n'.join('#check @'+n for n in ['ContinuousLinearMap.adjoint','ContinuousLinearMap.adjoint_inner_left','ContinuousLinearMap.map_sub',PRE+'SourceSubdifferential',PRE+'SourceProper',PRE+'abs_subgradient_zero',PRE+'affine_subdifferential','Set.mem_image_of_mem','EReal.coe_add','EReal.coe_le_coe_iff','EReal.coe_ne_bot']))
template=Path('runs/online-hinge-migration-20261007/leaves/export-public-dependencies-v1.lean').read_text(encoding='utf-8').replace('OnlineHingeCanary','OnlineAffineSubgradientCanary')
for name,names in [('export-ready-dependencies-v1.lean',[PRE+'theorem_2_28']),('export-public-dependencies-v1.lean',targets)]:
 t=template;start=t.index('def targets : Array Name := #[');end=t.index(']\n',start)+1;t=t[:start]+'def targets : Array Name := #[\n '+',\n '.join('`'+n for n in names)+']'+t[end:];t=t.replace('selected actual hinge nodes','selected actual affine transport nodes');write(RUN/'leaves'/name,t)
write(RUN/'draft-generated-before-use-v1.json',dict(before_first_use=True,rows=[dict(path=p.as_posix(),sha256=sha(p)) for d in [CONTRACT,RUN/'leaves'] for p in d.rglob('*') if p.is_file()]))
print('One full-image inclusion frozen with retained source properness; seven wholecanaryproof/twoTESTdefs. Stabilization pending.')
