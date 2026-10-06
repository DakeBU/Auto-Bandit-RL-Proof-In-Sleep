"""Apply nine separately reviewed source qualifications; preserve all original mathematics."""
from pathlib import Path
import hashlib,json,re,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header
run=Path(__file__).parent;task='ONLINE-SUBGRADIENT-DIFFERENTIABILITY-MIGRATION-20261007';route='online-subgradient-differentiability';pre='BanditRL.OnlineConvex.'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'))
def write(p,x,existing=False):
 p=Path(p);assert p.exists() if existing else not p.exists(),p
 p.write_bytes((x.rstrip('\n')+'\n' if isinstance(x,str) else json.dumps(x,ensure_ascii=False,indent=2)+'\n').encode('utf-8'))
r=load(run/'public-body-receipt-v1.json');freeze=load(run/'draft-freeze-v1.json')
assert r['actor']['task']=='/root/source_reviewer' and r['verdict'] in ['accepted','accepted-with-explicit-delta'] and sha(r['report'])==r['report_sha256']
assert not r.get('mathematical_repairs',r.get('required_mathematical_repairs',[]))
reviewed={p['path']:p['sha256'] for p in r['reviewed_files']}
for row in load(run/'public-body-inputs-v1.json')['rows']:assert reviewed[row['path']]==row['sha256'],row['path']
for p,h in reviewed.items():assert sha(p)==h,p
write(run/'body-binding-audit-v1.json',dict(status='passed',raw_rows=len(reviewed),report_sha256=r['report_sha256'],retained_proofs=11,retained_definitions=1,new_production_proofs=0,required_reader_corrections=r.get('required_reader_corrections',[])))
snap={p['path']:p for p in load(run/'historical-raw-supersession-v3.json')['rows']}
for p in ['website/content/readings.json','website/content/highlights.json','website/content/chapters.json']:assert sha(p)==snap[p]['raw_sha256']==sha(snap[p]['snapshot'])
public=Path('BanditRLProof/OnlineSubgradientDifferentiability.lean');original=(run/'original-OnlineSubgradientDifferentiability.lean.txt').read_bytes();assert public.read_bytes()==original
comment='''/-
Orabona v10 Theorem2.22, printed17/PDF29: one source result, eleven retained
proofs and one complete definition, zero new production mathematical nodes.
Convex EReal f finite at x is genuinely ambient locally real differentiable
iff its GLOBAL subdifferential is a singleton. The unique vector is the gradient
of EVERY differentiable real representative agreeing with f near x.
SourceDifferentiableAt expresses that full real germ; mere toReal smoothness
or differentiability within the domain is insufficient. A real singleton
indicator has smooth zero toReal, no true ambient germ, and every global support.
The full terminal assumes neither properness nor domain interior nor closedness:
actual finite-neighborhood contact/global support derives nowhere-bottom;
nonzero boundary normal perturbation forces interior in the reverse direction.
Local convex Lipschitz bounds, nontrivial-filter global inequality limits and
finite-dimensional compactness yield nearby selected-support convergence.
Two actual support inequalities squeeze the derivative residual to little-o.
Selection is proof-internal, not an algorithm or computational support oracle.
Forward contact and the accepted convex first-order theorem produce global
gradient support; derivative-zero local minimum and Riesz prove uniqueness.
All queries remain ambient, including top outside the finite neighborhood.
The eleven proofs use finite-dimensional real inner-product spaces with
derived completeness; zero dimension allowed. The definition's actual type
omits finite dimension. Helper noBottom/interior/NeBot/Lipschitz/continuity
premises are not extra source-terminal hypotheses. No infinite-dimensional
equivalence or arbitrary nonconvex global-support claim is made.
Theorem2.23 and remaining Chapter1/2/whole-book obligations remain required.
-/
'''
assert not re.search(r'\b(sorry|admit|axiom|postulate)\b',comment)
public.write_bytes(comment.encode('utf-8')+original)
write(run/'public-comment-qualification-v1.json',dict(path=public.as_posix(),original_sha256=hashlib.sha256(original).hexdigest(),qualified_sha256=sha(public),delta='leading ordinary ignored source/scope comment only',exact_original_bytes_retained_as_suffix=True,all_proof_bodies_definition_tokens_unchanged=True))
germ='SourceDifferentiableAt means a real differentiable representative h agrees with f throughout an AMBIENT neighborhood of x. It entails actual local finiteness, not merely smoothness of toReal or differentiation within the domain/affine span. The gradient identity holds for EVERY such representative.'
terminal='Theorem2.22 assumes convex real-height epigraph and an actual finite real value at x. Properness/noBottom and ambient interior are DERIVED in its directions; no closedness/lsc/boundedness/Lipschitz/interior oracle is added. Supports test ALL ambient y, including top outside the finite neighborhood.'
scope='The eleven proof declarations use finite-dimensional real inner-product spaces, with completeness derived and dimension0 allowed; ambient space has zero and is nonempty. The complete real-germ definition itself has no finite-dimension binder. No arbitrary infinite-dimensional equivalence is claimed.'
helpers='NoBottom, NeBot, finite positive ball, local Lipschitz and continuity premises belong to particular intermediate interfaces, not the full source terminal. The generic support predicate permits all EReal functions; each theorem direction here derives noBottom before finite-part conversion.'
reverse='A nonzero supporting normal at a domain boundary would give a second support g+d, so a singleton forces ambient interior. Convex local Lipschitzness bounds every nearby support; genuine nonbottom-filter limits and finite-dimensional compactness identify the selected support limit. Two actual global inequalities bound the nonnegative remainder by norm(G(y)-g)*norm(y-x), yielding the Frechet derivative. Proof-internal choice is not an algorithm or computational oracle.'
forward='A real germ supplies finite-neighborhood affine CONTACT, hence global noBottom. Regularity and accepted Theorem2.7 produce actual global gradient support. A local minimum of the supported residual has derivative zero; Riesz injectivity gives uniqueness. Eventual equality of real representatives gives the same gradient.'
counts='ONE printed source Theorem2.22; eleven retained proof declarations and one complete definition are a proof refinement, not eleven printed results. Zero new production mathematics or canonical registry nodes. Actual selected graph21nodes3026direct references includes11producerproofs/1definition/9canaryproofs;20required value pairs; not a full registry graph. Earlier12node1880readiness is separate and exactly retained.'
canaries='Six unchanged old proofs instantiate genuine constrained [0,2] at1, nonzero quadratic gradient2 at1, the reverse equivalence/derivative and boundary0 with supports0/-1. Three NEW TEST-only singleton{1} diagnostics actually compile: toReal is identicallyzero and smooth, the genuine ambient germ fails by regularity and empty interior, and EVERY real vector supports. This real singleton empty-interior fact does not extend to dimension0.20named standard kernel checks/11nativeguards are separate from compilation.'
remaining='This package covers T2.22 equivalence AND gradient identity only. T2.23 and all remaining Chapter1/2 main-text/necessary appendix/source-contract obligations remain REQUIRED. Chapter2 mandatory totalnull/incomplete; Chapters3-16unenumerated; wholeGoalACTIVE. No merge/deploy/main/live update.'
p=Path('website/content/readings.json');d=load(p);x=next(a for a in d['readings'] if a['slug']==route)
x['primary']['sections']='Section2.2.1, Theorem2.22; one source result, eleven retained proofs and one full local-real definition'
x['notation']=[dict(term='Ambient real germ',meaning=germ),dict(term='Finite point and global supports',meaning=terminal),dict(term='Scope and intermediate hypotheses',meaning=scope+' '+helpers)]
card=x['source_theorems'][0];assert len(x['source_theorems'])==1
card.update(math=r'f\text{ locally real differentiable at }x\iff\exists g,\;\partial f(x)=\{g\}',fallback='True ambient local-real differentiability iff singleton global subdifferential; its element is the gradient of every agreeing differentiable real representative.',relationship=germ+' '+scope+' '+counts)
card['contract'].update(model='EReal with both infinities, convex REAL-height epigraph and global support inequality.',assumptions=terminal,parameters='Every f,x with finite f(x); every local differentiable real representative h agreeing in the ambient neighborhood.',guarantee=r'SourceDifferentiableAt f x iff exists g, S(f,x)={g}; for every agreeing differentiable h, S(f,x)={gradient h x}.',regret='No algorithm, regret or measurable support-selection guarantee.')
card['local_status'].update(status='compiled',label='Full retained terminal and diagnostic bodies checked',boundary='Distinct CONTRACT/BODY accepted; actual20named kernelchecks/11guards/9genuinecanaryproofs. CombinedrootTests/harness/reader/siteFINAL/PR are separately recorded; cachedjobs are included. '+remaining)
x['algorithm'].update(title='Produce both directions of the equivalence',kind='proof flow',steps=[dict(title='Produce the singleton from a real germ',detail=forward),dict(title='Force interior from a singleton',detail='Actual nonzero boundary normal would add a distinct global support. No interior input is assumed.'),dict(title='Produce the derivative from global inequalities',detail=reverse)])
x['teaching_route']=list(dict.fromkeys(x['teaching_route']+[pre+'SourceDifferentiableAt',pre+'subgradient_norm_le_lipschitz_ball',pre+'subgradients_locally_bounded',pre+'subgradient_limit_of_continuousAt',pre+'singleton_subgradient_tendsto',pre+'sourceDifferentiableAt_regular',pre+'subgradient_eq_gradient_at_interior',pre+'theorem_2_22_forward']))
assert len(x['teaching_route'])==12
x['proof_bridge'].update(summary='The source-shaped iff and explicit gradient identity are produced by the actual forward and reverse chains.',steps=[dict(title='A genuine real germ supplies contact',detail=forward,math=r'\partial f(x)=\{\nabla h(x)\}',fallback='Every locally agreeing differentiable representative has the same gradient.'),dict(title='A singleton forces ambient interior',detail='Use a nonzero normal of the ORIGINAL domain to construct g+d; equality of the global support set contradicts d nonzero.',math=r'\partial f(x)=\{g\}\Longrightarrow x\in\operatorname{int}(\operatorname{dom}f)',fallback='Domain interior and noBottom are consequences, not main inputs.'),dict(title='Squeeze the residual to a Frechet derivative',detail=reverse,math=r'0\le f(y)-f(x)-\langle g,y-x\rangle\le\|G(y)-g\|\,\|y-x\|',fallback='Support convergence makes the residual little-o of the displacement.')],boundary=helpers+' '+scope+' '+counts+' '+remaining)
x['worked_example'].update(title='A smooth finite-part cast can still fail true differentiability',intro='A proper real singleton indicator exposes why the extended-real germ must retain actual local finiteness.',steps=[dict(title='Check the misleading finite-part cast',detail='The singleton indicator is0 at1 and top elsewhere, so its toReal is identicallyzero. The first new test proves ambient DifferentiableAt of that cast.',math=r'I_{\{1\}}(y).\mathrm{toReal}=0',fallback='Smoothness of this total cast alone discards infinite values.'),dict(title='Exclude the genuine ambient germ',detail='The actual regularity producer would put1 in the ambient interior of its singleton effective domain. That interior is empty in the REAL line, and the second new test derives the contradiction.',math=r'\operatorname{int}_{\mathbb R}\{1\}=\varnothing',fallback='No real neighborhood can agree with the top values off1.'),dict(title='Check global supports and nonzero genuine cases',detail='The third new test proves EVERY real g supports at1. Keep all six old indicator/quadratic/boundary tests, including actual gradient2 for the quadratic at1.',math=r'\partial I_{\{1\}}(1)=\mathbb R',fallback='A singleton domain does not mean a singleton subdifferential.')],takeaway='The full source terminal distinguishes the real germ from a smooth cast and produces the genuine gradient when appropriate.',boundary=canaries+' Source introductory differentiability prose is under the convex theorem hypothesis; arbitrary differentiable nonconvex functions need not have global supports. '+remaining)
write(p,d,True)
p=Path('website/content/highlights.json');d=load(p)
for h in d['highlights']:
 if h.get('chapter')!=route:continue
 h['position']='Orabona v10 Theorem2.22 printed17/PDF29: one source result, necessary shared proof interfaces.'
 h['lean_notes']=scope+' '+helpers+' '+terminal
 h['why']='Source-qualified links reuse the SAME declaration registry; zero new production math nodes. '+counts
 n=h['full_name'].rsplit('.',1)[-1]
 if n=='theorem_2_22':h['proof_idea']=forward+' '+reverse
 elif n=='theorem_2_22_gradient':h['proof_idea']=forward;h['plain']=germ
 elif n=='singleton_subdifferential_hasGradientAt':h['proof_idea']=reverse
 elif n=='singleton_subgradient_tendsto':h['proof_idea']='Positive local ball bounds every actual nearby support; compact closedBall and unique global support limit on a NeBot filter produce convergence without assuming a gs limit.'
 elif n=='singleton_subdifferential_interior':h['proof_idea']='A nonzero supporting normal at the ORIGINAL domain boundary yields a distinct global support g+d and contradicts singleton equality.'
 else:h['proof_idea']='Accepted shared finite-neighborhood affine CONTACT dependency, unchanged; not another printed source theorem.'
write(p,d,True)
p=Path('website/content/chapters.json');d=load(p);x=next(a for a in d['chapters'] if a['slug']==route)
x.update(title='A singleton global support produces the derivative',short_title='Singleton and real germ',status='compiled',summary='Preserve genuine ambient local-real differentiability and derive the complete singleton equivalence with every-representative gradient identity.',completion_definition=counts+' This source package only.',completion_blockers=[remaining],learning_goals=['Keep local real values while differentiating extended-real functions.','Derive domain interior from nonzero normal perturbation and a singleton.','Use actual neighboring supports and compactness to produce a Frechet derivative.','Distinguish a smooth toReal cast from a genuine real germ, preserving required later results.'],open_gaps=[scope+' '+remaining])
write(p,d,True)
for p,k,key in [('website/content/readings.json','readings','slug'),('website/content/chapters.json','chapters','slug'),('website/content/highlights.json','highlights','chapter')]:
 old=load(snap[p]['snapshot']);new=load(p)
 assert [a for a in old[k] if a.get(key)!=route]==[a for a in new[k] if a.get(key)!=route],p
 for extra in set(old)-{k}:assert old[extra]==new[extra]
for n,h in freeze['headers'].items():assert hashlib.sha256(lean_declaration_header(public,n).encode()).hexdigest()==h,n
names=load(run/'public-named-declarations-v1.json')['public_proofs']+load(run/'public-named-declarations-v1.json')['public_definitions']
paths=[public.as_posix(),'website/content/readings.json','website/content/highlights.json','website/content/chapters.json']
c=load('research-wiki/contribution-contracts/online-subgradient-basic-migration-20261006.json')
c.update(id=task,frontier_cell=route,target='Close source Theorem2.22 complete equivalence and every-representative gradient identity; retain11actualproofs/fullrealgermdefinition, zero new productionmathnodes.',affected_files=paths,declarations=names)
c['source']['anchor']='Theorem2.22 printed17/PDF29, one printed result; eleven proof refinements and one full local-real definition; bothiff directions AND gradient identity.'
c['reuse_plan'].update(classification='existing_exact',decision='reuse_existing',searched_existing=['Actual eleven public @types/full definition/frozen headers/body and pinned API retrieval.','Actual21selected compiled nodes3026refs/20producer-canary pairs; old12node1880graph retained.'],reused_declarations=names,new_shared_declarations=[],known_consumers=['Tests.OnlineDifferentiabilityBoundary.singleton_not_sourceDifferentiable','ForwardSubgradientProbe.quadratic_singleton_nonzero','DifferentiabilityProbe.constrained_interval_differentiable'],planned_consumers=['Mandatory laterChapter2 analytic/subgradient proof dependencies'],no_duplicate_wrapper=True,decision_reason='Reuse actual full iff/gradient producer chain; only3new diagnostic TEST proofs, no duplicate source wrappers or perBook library.')
c['semantic_roundtrip'].update(status='accepted',blind_decoder='/root/differentiability_blind',verdict=r['verdict'],remaining_semantic_delta=germ+' '+scope+' '+helpers+' Distinct CONTRACT/BODY accepted; package FINAL pending; requestedAstra/medium/no humanexternal runtimeattestation.')
c['graph_contribution'].update(lean_graph='reuse-existing',focus_targets=names,overview_graph='updated',functor_reason='Source-qualified shared proof reuse; no setting composition/discovery claim.',visual_review=counts+' Preserve all10811oldIDsURLs/0newnodes after applicable sitegates.')
c['progress_updates'].update(teaching_route='updated: preserve old links, show full real-germ definition and exact source iff/gradient boundary with actual producer dependencies.',website_surfaces=paths[1:],results_ledger='no-change-with-reason: additive package overlay follows fullgates/PR; original chapter inventory untouched, Chapter2 totalnull/incomplete.')
c['truth_boundary']=germ+' '+terminal+' '+scope+' '+helpers+' '+counts+' '+canaries+' '+remaining
c['verification'].update(focused_checks=['Fresh11retainedproofs/one full definition/6old+3newactualcanaryproofs/20namedstandard-or-none kernelchecks/11nativeguards/21nodes3026refs.'],owned_test_files=['Tests/OnlineDifferentiabilityBoundaryCanary.lean','Tests.lean'],bandit_check='Fresh sequential root/Tests/fullharness separately required after scope-comment integration.',site_build='Clean local lean-verified site only after current combinedgate.',site_check='Same10811oldIDsURLs/0new canonical nodes; allotherBooksubtrees unchanged.')
write('research-wiki/contribution-contracts/online-subgradient-differentiability-migration-20261007.json',c)
write(run/'reader-integration-v1.json',dict(status='nine reviewed source-reader requirements integrated; finalgates pending',affected_files=paths,selected_route=route,required_reader_corrections_addressed=True,all_other_Book_subtrees_unchanged=True,leading_ordinary_comment_only=True,all_original_math_bytes_contiguous=True,public_module_unchanged_since_current_build=False,public_comment_requires_fresh_Lean_gate=True,retained_proofs=11,retained_definitions=1,new_production_proofs=0,new_test_proofs=3,expected_new_registry_nodes=0,source_numbered_anchors=1,source_package_accepted=False,chapter_complete=False,goal_complete=False))
with Path('MANIFEST.md').open('a',encoding='utf-8',newline='\n') as f:
 f.write('\n- T2.22 source package20261007: full iff plus every-local-real-representative gradient identity,11retainedproofs/1completegermdefinition/0newproductionnodes;6old+3newdiagnosticcanaries/20namedkernelchecks/11nativeguards/actual21selectednodes3026refs. Same sharedregistry10811IDs expected, rootTests/fullharness/siteFINAL/PR independent pending; Chapter2 and wholeGoal incomplete. See runs/online-subgradient-differentiability-migration-20261007.\n')
print('Nine reviewed reader qualifications applied; original math fixed; scope comment needs fresh combinedgates; FINALpending.')
