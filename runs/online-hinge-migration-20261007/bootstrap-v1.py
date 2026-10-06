"""Freeze the existing hinge producer and source; do not inherit old draft acceptance."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
ROOT=Path('.').resolve();RUN=Path(__file__).resolve().parent
assert ROOT==RUN.parents[1]
BASE='8375aa0353a4230ec23c0ccbb8f337a16246c134'
PUBLIC=Path('BanditRLProof/OnlineHinge.lean');CANARY=Path('Tests/OnlineHingeCanary.lean')
CONTRACT=Path('docs/contracts/online-hinge-migration-v1');TASK='ONLINE-HINGE-MIGRATION-20261007';PRE='BanditRL.OnlineConvex.'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'))
def write(p,x):
 p=Path(p);assert not p.exists(),p;p.parent.mkdir(parents=True,exist_ok=True)
 p.write_bytes(x if isinstance(x,bytes) else ((x.rstrip('\n')+'\n') if isinstance(x,str) else json.dumps(x,ensure_ascii=False,indent=2)+'\n').encode())
assert subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf-8').strip()==BASE
assert subprocess.check_output(['git','branch','--show-current'],encoding='utf-8').strip()=='codex/research-online-hinge-migration'
sys.path.insert(0,str(ROOT));from tools.abrl_lifecycle import lean_declaration_header
raw=PUBLIC.read_text(encoding='utf-8');decls=re.findall(r'^(theorem|def)\s+(\w+)\b',raw,re.M)
proofs=[n for k,n in decls if k=='theorem'];defs=[n for k,n in decls if k=='def']
assert len(proofs)==13 and defs==['sourceHinge','hingeFamily'],(proofs,defs)
headers={n:dict(statement=lean_declaration_header(PUBLIC,n),hash=hashlib.sha256(lean_declaration_header(PUBLIC,n).encode()).hexdigest(),kind=k) for k,n in decls}
old=load('docs/contracts/online-hinge-v1/contract-manifest.json')
for n,h in old['fingerprints'].items():assert headers[n]['hash']==h,n
write(CONTRACT/'headers.json',headers)
owned={}
for n in defs:
 m=re.search(r'(?m)^def '+n+r'\b.*?(?=\n\s*(?:theorem|def)\b)',raw,re.S);assert m,n;owned[n]=m.group(0).strip()
borrowed={}
for file,names in [('BanditRLProof/OnlineSubgradientBasic.lean',['SourceSubdifferential']),('BanditRLProof/OnlineClosedProper.lean',['SourceProper']),('BanditRLProof/OnlineConvexExtended.lean',['effectiveDomain','realEpigraph','IsConvexExtended']),('BanditRLProof/OnlineSubgradientMax.lean',['SourceFiniteMax','SourceActiveSubgradientUnion'])]:
 t=Path(file).read_text(encoding='utf-8')
 for n in names:
  m=re.search(r'(?m)^def '+n+r'\b.*?(?=\n\s*(?:/--|theorem|def)\b)',t,re.S);assert m,(file,n)
  body=m.group(0).split('\n/--')[0].strip();borrowed[n]=dict(body=body,owner=file,owner_sha256=sha(file))
write(CONTRACT/'scoped-contexts.json',dict(section='noncomputable section; open Set; namespace BanditRL.OnlineConvex',ambient='variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]',owned_definitions=owned,owned_full_body_sha256={n:hashlib.sha256(t.encode()).hexdigest() for n,t in owned.items()},borrowed_definitions=borrowed,actual_implicit_binders='Verify compiled @types; only two retained statements explicitly add FiniteDimensional, definitions need intrinsic inner-product structure. No blanket FD on affine and active-index helpers.'))
snap=[]
for p in [PUBLIC,CANARY,Path('BanditRLProof.lean'),Path('Tests.lean'),Path('lean-toolchain'),Path('lakefile.lean'),Path('lake-manifest.json'),Path('runs/active_frontier.json'),Path('runs/lifecycle_sessions.jsonl'),Path('runs/trials.jsonl'),Path('MANIFEST.md'),*map(Path,['website/content/readings.json','website/content/highlights.json','website/content/chapters.json']),*map(Path,{r['owner'] for r in borrowed.values()})]:
 target=RUN/'snapshots'/('before-'+p.as_posix().replace('/','--')+'.txt');write(target,p.read_bytes());snap.append(dict(path=p.as_posix(),raw_sha256=sha(p),snapshot=target.as_posix()))
write(RUN/'historical-raw-supersession-v1.json',dict(rows=snap,all_prior_files_preserved=True))
cp=re.findall(r'^theorem\s+(\w+)\b',CANARY.read_text(encoding='utf-8'),re.M);assert len(cp)==5
cp=['HingeProbe.'+n for n in cp]
fixed=[r['path'] for r in snap if r['path'].endswith('.lean') and r['path'] not in [PUBLIC.as_posix(),CANARY.as_posix()]]+['lean-toolchain','lakefile.lean','lake-manifest.json','runs/active_frontier.json']
write(RUN/'draft-freeze-v1.json',dict(stage='draft',headers={n:r['hash'] for n,r in headers.items()},proof_names=proofs,definition_names=defs,original_module_sha256=sha(PUBLIC),whole_old_canary={CANARY.as_posix():sha(CANARY)},fixed_shared_files={p:sha(p) for p in fixed},full_owned_definition_sha256={n:hashlib.sha256(t.encode()).hexdigest() for n,t in owned.items()},retained_public_proofs=13,retained_public_definitions=2,whole_canary_proofs=5,whole_canary_definitions=0,new_production_proofs=0,new_definitions=0,new_test_proofs=0,source_body_examples=1,source_claims=3,source_package_accepted=False,chapter_complete=False,goal_complete=False))
targets=[PRE+n for k,n in decls]+cp
write(RUN/'public-named-declarations-v1.json',dict(production=[PRE+n for k,n in decls],production_proofs=[PRE+n for n in proofs],production_definitions=[PRE+n for n in defs],whole_canary_proofs=cp,whole_canary_definitions=[],axiom_probe=targets,unique_checks=20))
pdf=Path('../research-online-ogd/tmp/pdfs/orabona-v10.pdf');assert sha(pdf)=='cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17'
from pypdf import PdfReader
write(RUN/'source-printed18-pdf30.txt',PdfReader(str(pdf)).pages[29].extract_text())
img=Path('tmp/online-subgradient-sum-source-pdf30-v1.png');assert sha(img)=='c4354de7297923fd82f74645ddd50fdb582f90b6eeb9a7536fd9f33ec5489ebd'
write(CONTRACT/'source-card.json',dict(id='ORABONA-V10-EX2.27',title='Online Learning: A Modern Introduction Using Convex Optimization',version='arXiv:1912.13213v10,21June2026',url='https://arxiv.org/pdf/1912.13213v10',cached_PDF=pdf.as_posix(),sha256=sha(pdf),printed_page=18,PDF_page=30,actual_page_image=img.as_posix(),image_sha256=sha(img),source_body_examples=1,source_claims=3,required_source_terminal='example_2_27',retained_foundation_proofs=12,retained_terminal_proofs=1,retained_owned_definitions=2,excluded_independent_exercises=[],chapter_complete=False,goal_complete=False))
prior=Path('runs/online-subgradient-max-migration-20261007');entries=subprocess.check_output(['git','ls-tree','-r','-z',BASE,'--',prior.as_posix()]).split(b'\0');objects={e.split(b'\t',1)[1].decode():e.split(b'\t',1)[0].split()[2].decode() for e in entries if e};bound=[];ignored=[]
for p in sorted(prior.rglob('*')):
 if not p.is_file():continue
 q=subprocess.run(['git','check-ignore','-q','--',p.as_posix()]);assert q.returncode in [0,1]
 if q.returncode==0:ignored.append(p.as_posix());continue
 assert p.as_posix() in objects;obj=objects[p.as_posix()];assert subprocess.check_output(['git','cat-file','blob',obj])==p.read_bytes(),p
 bound.append(dict(path=p.as_posix(),git_blob=obj,raw_sha256=sha(p)))
assert len(bound)==565
write(RUN/'prior-delivery-raw-binding-v1.json',dict(status='passed',exact_PR173_head=BASE,raw_files=len(bound),rows=bound,ignored_runtime_preserved=ignored,prior_PR='OPEN-DRAFT-unmerged',prior_chapter_goal_not_completed=True))
contract='''# Example2.27 hinge source contract v1 — draft

ONE main-text example, THREE required branches of ONE full set equality. For every z,x in finite-dimensional real inner-product E (including source Euclidean instances), actual hinge loss max(1-inner(z,x),0) embedded into EReal. The full ambient global supporting set is {0} for negative margin, {-alpha z | alpha in [0,1]} at zero margin, {-z} otherwise (positive margin). Entire set, both inclusions, both endpoints and intermediate mixtures. No z nonzero, positive dimension, norm bound, data-label restriction, selected support, algorithm or regret premise. z=0 gives constant1 and positive margin, hence {0}; it does not instantiate the boundary branch. The generic all-ambient global support API admits arbitrary improper functions, but this hinge and both affine components are everywhere finite/proper/convex/continuous, making the source instance proper without an extra supplied premise. No coordinate-isometry/functor certificate is separately proved.

TWO retained full definitions sourceHinge and hingeFamily, and THIRTEEN retained proofs: ONE source terminal plus TWELVE supporting library facts. Affine support singleton is derived directly from every-y global inequalities and inner-self positivity at y=x+g-a, with no finite dimension premise. Properness/convexity/continuity of actual affine components are derived, not supplied. Actual Bool finite-maximum identity instantiates the accepted full Theorem2.26 with all hypotheses produced. Active index sets are classified by real margin sign; ordinary hull of a singleton/two points yields the complete three-way set. Only hinge_subdifferential_hull and example_2_27 explicitly add finite dimension, inherited intrinsic real inner-product structure remains on definitions and other helpers. Reusable affine helpers generalize beyond Euclidean finite dimension, not extra numbered source results. Finite-dimensional completeness derived where upstream needed, no explicit extra CompleteSpace.

Whole FIVE old scalar canary proofs unchanged: strict-zero at z1,x2; strict-slope at z1,x0; FULL closed boundary interval[-1,0] at z1,x1; actual fractional -1/2 in full support but not active component union,1 rejected; z0 yields{0} for EVERY scalar x. This checks nondegenerate branches but not actual2D hinge geometry or boundary vector zero. No new TEST/registry or proof nodes.

Freeze all15 headers, full owned definitions, original entire module, oldcanary, borrowed support/properness/domain/convexity/actualMax declarations, shared roots/pins/globalSGB. Default single lower retrieval-reuse route. Distinct restricted neutral decoder and anti-anchored CONTRACT/BODY/FINAL actors required by the actual repository skill; requested Astra/medium, automated not human/external/runtime-attested. Root may stage director/middle/architect/worker, no optional competing multi-agent experiment. Source contract, conversion window, proof obligations, current API retrieval and actual compiler types/dependency graph precede stabilized/proving; actual body/canary/kernel/fences before candidate; full root/Tests/harness/task-only shadow/site/registry/pixels and FINAL/native acceptance before scoped delivery. CLI-enforced gates and prompt/file/role conventions remain distinct.

Only online-hinge reader subtrees and ordinary leading public comment may change after semantic review; all mathematical and canary bytes retained. Shared Lean/Lake/registry, no perBook copies/pin upgrade or unverified Optlib import. Exact OPENdraft PR173 base 8375aa0353a4230ec23c0ccbb8f337a16246c134; canonical main/originmain6847b678a73db68dee5101d6f05c2453c1405afc clean after fresh fetch, shared Git E:/ABRL/research/.git, all565 current Max run raw Git blobs verified. Extended-topics head independently advanced249b3fef... and is preserved. Old20261003 hinge draft unchanged/historical, acceptance never inherited.

Legacy2->1 ONLY OnlineHinge AFTER actual reviewed PR delivery, not at draft/compile. Next Theorem2.28 affine and all remaining Chapter1/2 maintext/necessary appendices remain REQUIRED, including nine OTHER Chapter1 main-relative contribution-contract gaps; chapter2mandatorytotal null/incomplete,3–16unenumerated, totalGoalACTIVE/unbudgeted. No merge/deploy/main/live/generated _site/private/anonymous change or worktree retirement.
'''
write(CONTRACT/'contract.md',contract)
dag={'example_2_27':['hinge_subdifferential_hull','hinge_active_negative','hinge_active_positive','hinge_active_zero','convexHull_singleton','convexHull_pair','segment_eq_image'],'hinge_subdifferential_hull':['hinge_max_identity','theorem_2_26','affine_proper','affine_convex','affine_continuous'],'hinge_family_support':['affine_subdifferential'],'affine_subdifferential':['global supporting inequalities','inner_self_eq_zero','real_inner_self_nonneg']}
write(CONTRACT/'initial-dependency-DAG.json',dict(status='architect source route; actual compiled occurrence graph separate',terminal='example_2_27',nodes=dag,retained_foundations=12,new_math_nodes=0))
write(RUN/'proof-obligations-draft-v1.json',dict(required_terminal=dict(name=PRE+'example_2_27',statement_hash=headers['example_2_27']['hash'],state='retained full three-branch equality sourcecontractdraft'),supporting_foundations=[dict(name=PRE+n,statement_hash=headers[n]['hash'],state='necessary retained dependency; not independent source completion') for n in proofs if n!='example_2_27'],owned_definitions=[dict(name=PRE+n,statement_hash=headers[n]['hash'],full_body_sha256=hashlib.sha256(owned[n].encode()).hexdigest()) for n in defs],remaining_legacy_before=2,chapter2_mandatory_total=None,source_package_accepted=False,chapter_complete=False,goal_complete=False))
write(RUN/'00_context.md','TotalGoalACTIVE/unbudgeted/requestedAstra medium. Fresh canonicalmain/originmain6847b678a73db68dee5101d6f05c2453c1405afc clean. SharedGit E:/ABRL/research/.git; allotherworktrees and ignoredlinkedcache/profiles preserved. Current branch codex/research-online-hinge-migration from exactOPENdraftPR173 '+BASE+' after DIRECT clean/localremoteREST/565raw currentMax files matched. Frozen PDF30 reread and actual original pixels viewed. ONEExample2.27/THREEbranches/13retainedproofs2defs/5oldcanaries/0newmath. Readonly diagnostic27b529 guessed nonexisting bandit-formalization skill; actual rg/reload d4a308 read bandit-lean-formalization. Readonly0078fd guessed nonexistent olddirector.md; old contract read but no gate inferred from shell exit. Privateharness currenthash only recorded separately; no content copied. GlobalSGBfixed/task-only lifecycle. No competing Chapter3 writing or olddraft acceptance inheritance.')
write(RUN/'10_upper_director-v1.md','Bounded complete three-branch Example2.27 equality for actual hinge, including endpoints/mixes/z0. Single lower route reuse_existing: audit current13actualproducerproofs/2defs, dependencyreadiness and sourcecontract before bodyre-elaboration. No wrapper/newdeclaration-count progress; allremainingChapter1/2maintext retained REQUIRED.')
write(RUN/'20_architect-v1.md','Actual affine fullsupport at everyquery proved by displacement/inner positivity, then actualtwoaffine properconvexcontinuousfacts and actualBoolmaximum. Apply exact acceptedfullT2.26, classifyactiveindices by negative/zero/positive margin, rewrite ordinarysingleton/two-point hull into fullclosed segment. No assumedsupportformula/maximumoracle/regret consumer; preserve exactterminal.')
write(RUN/'memory-digest-draft-v1.md','Only hinge draft/current totalGoalACTIVE. ONEExample2.27/3branches/13retainedproofs2fulldefs/5wholecanaryproofs. Sourcefinite-real loss alwaysproper; generic S widerimproper. FDonly2explicit statements, no znonzero, zerovector positive-margin constant1. No scalarboundaryz0/2D/newproof claim. Legacy2pending untilrealPR.')
write(RUN/'retrieval-index-draft-v1.md','ORABONA-V10-EX2.27; MLIB-CONVEX-LINALG. Local fullT2.26/affinesupport/actualBoolmax, upstreaminner positivity/convexHull_pair/singleton/segment_eq_image need freshactual#checks. Reuse-existing only; no Optlib compatibility/upstream rebuilding claimed.')
for d in ['tasks','conversion-windows','proof-obligations']:write(Path(d)/(TASK+'.md'),contract)
write(RUN/'leaves/actual-types-v1.lean','import BanditRLProof.OnlineHinge\nimport Tests.OnlineHingeCanary\nset_option pp.universes true\n'+'\n'.join('#check @'+n for n in targets)+'\n'+'\n'.join('#print '+PRE+n for n in defs+list(borrowed)))
write(RUN/'leaves/public-all-axioms-v1.lean','import BanditRLProof.OnlineHinge\nimport Tests.OnlineHingeCanary\n'+'\n'.join('#print axioms '+n for n in targets))
write(RUN/'leaves/pinned-APIs-v1.lean','import BanditRLProof.OnlineHinge\n'+'\n'.join('#check @'+n for n in ['BanditRL.OnlineConvex.theorem_2_26','convexHull_pair','convexHull_singleton','segment_eq_image','inner_self_eq_zero','real_inner_self_nonneg','Finset.sup\'_le_iff','Finset.le_sup\'','EReal.coe_le_coe_iff','EReal.coe_lt_coe_iff','convexExtended_iff_toReal','continuous_coe_real_ereal','EReal.coe_ne_bot','EReal.coe_lt_top']))
template=Path('runs/online-subgradient-max-migration-20261007/leaves/export-public-dependencies-v2.lean').read_text(encoding='utf-8')
template=template.replace('OnlineSubgradientMaxCanary','OnlineHingeCanary').replace('OnlineSubgradientMax','OnlineHinge')
for name,names in [('export-ready-dependencies-v1.lean',[PRE+n for k,n in decls]),('export-public-dependencies-v1.lean',targets)]:
 t=template;start=t.index('def targets : Array Name := #[');end=t.index(']\n',start)+1
 t=t[:start]+'def targets : Array Name := #[\n '+',\n '.join('`'+n for n in names)+']'+t[end:]
 t=t.replace('forty selected retained producer/canary nodes: four definitions/thirtysix proofs; direct type/value occurrence only, not full registry graph','selected actual hinge nodes; direct type/value occurrences only, not full registry graph')
 write(RUN/'leaves'/name,t)
write(RUN/'draft-generated-before-use-v1.json',dict(before_first_use=True,rows=[dict(path=p.as_posix(),sha256=sha(p)) for d in [CONTRACT,RUN/'leaves'] for p in d.rglob('*') if p.is_file()]))
print('Frozen13 retained proofs/2 full owned definitions/5 wholecanary proofs, ONEExample2.27. Source/actual readiness and stabilization remain pending.')
