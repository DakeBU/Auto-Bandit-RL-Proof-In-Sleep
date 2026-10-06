"""Apply distinct-reviewed reader corrections without changing retained mathematics."""
from pathlib import Path
import hashlib,json,re,sys,subprocess
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header
run=Path(__file__).parent;task='ONLINE-SUBGRADIENT-SUM-MIGRATION-20261007';route='online-subgradient-sum';pre='BanditRL.OnlineConvex.'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'))
def write(p,x,existing=False):
 p=Path(p);assert p.exists() if existing else not p.exists(),p
 p.write_bytes((x.rstrip('\n')+'\n' if isinstance(x,str) else json.dumps(x,ensure_ascii=False,indent=2)+'\n').encode('utf-8'))
r=load(run/'public-body-receipt-v1.json');freeze=load(run/'draft-freeze-v1.json')
assert r['actor']['task']=='/root/source_reviewer' and r['verdict'] in ['accepted','accepted-with-explicit-delta'] and sha(r['report'])==r['report_sha256']
assert not r.get('mathematical_repairs',r.get('required_mathematical_repairs',[]))
reviewed={p['path']:p['sha256'] for p in r['reviewed_files']}
for row in load(run/'public-body-inputs-v1.json')['rows']:assert reviewed[row['path']]==row['sha256']==sha(row['path']),row['path']
for p,h in reviewed.items():assert sha(p)==h,p
write(run/'body-binding-audit-v1.json',dict(status='passed',raw_rows=len(reviewed),report_sha256=r['report_sha256'],required_reader_corrections=r.get('required_reader_corrections',[]),new_production_proofs=0))
snap={row['path']:row for row in load(run/'historical-raw-supersession-v2.json')['rows']}
for p in ['website/content/readings.json','website/content/highlights.json','website/content/chapters.json']:assert sha(p)==snap[p]['raw_sha256']==sha(snap[p]['snapshot'])
public=Path('BanditRLProof/OnlineSubgradientSum.lean');original=(run/'original-OnlineSubgradientSum.lean.txt').read_bytes();assert public.read_bytes()==original
comment='''/-
Orabona v10 Theorem 2.23, printed 17-18/PDF 29-30: ONE numbered result,
TWO branches, nine retained proofs and one full witness definition.
Inclusion uses only proper components, every queried x, and actual simultaneous
component vectors. No convexity, closedness, query finiteness or common finite
point is supplied. Empty-index inclusion is an explicit library extension.
Generic SourceSubdifferential extends the proper-function Definition 2.20:
an identically top aggregate admits every vector by the formal inequality.
Disjoint proper component domains yield that aggregate with an EMPTY Minkowski
side. Proper components alone do not imply proper sum. Ordinary EReal addition
agrees with upperAdd here because component properness excludes bottom;
the operations differ for mixed infinities.
Equality has a positive Fin(n+1) family, all components proper/convex/CLOSED,
and an independent z in the LAST domain and all OTHER AMBIENT interiors.
The last point may be a boundary. For a singleton only the qualification's
other-interior condition vanishes; proper/convex/closed premises still remain.
The main proof derives aggregate properness, queried and component finiteness.
The stronger binary helper omits closedness but explicitly takes query-finite
inputs. Its epigraph-product linear image, actual support contact and nonzero
separation give a strictly NEGATIVE height coefficient via interior variation.
Normalization and Riesz construct actual p and g-p. Prefix interior/properness
and recursive equality construct the full vector family with Fin.snoc.
Six vector proofs retain finite-dimensional real inner-product classes;
three scalar proofs have no E; the full M definition has no finite-dimensional
binder. Completeness is derived, zero dimension and zero vectors allowed.
Convexity is REAL-height epigraph convexity; closedness means REAL sublevels,
not necessarily a closed effective domain. No algorithm or selection oracle.
Twenty old canary proofs/three definitions remain unchanged; REAL singleton
empty interior is a real-line example, not a zero-dimensional universal fact.
Adjacent Example 2.24 and remaining Chapter 1/2/book obligations stay required.
-/
'''
assert not re.search(r'\b(sorry|admit|axiom|postulate)\b',comment)
public.write_bytes(comment.encode('utf-8')+original)
write(run/'public-comment-qualification-v1.json',dict(path=public.as_posix(),original_sha256=hashlib.sha256(original).hexdigest(),qualified_sha256=sha(public),delta='ordinary leading source/scope comment only',exact_original_raw_suffix=True,all_proof_bodies_definition_tokens_unchanged=True))
M='SourceSubgradientSum f x means actual simultaneous vectors G(i), each globally supporting the same f(i) at the same x, and their exact finite vector sum equals g. An empty component support makes this witness set empty.'
inc='Inclusion quantifies EVERY x and an arbitrary Fintype family of proper components, with no convexity, closedness, query-finiteness or common finite point. Empty-index inclusion produces the zero support as an explicit library extension, not a printed positive-family equality.'
delta='Printed Definition 2.20 restricts proper functions; generic SourceSubdifferential extends the supporting inequality to ALL EReal functions. With disjoint proper component domains the sum is identically top: its formal support set is ALL vectors and the component Minkowski side is EMPTY. Proper components alone do not make the aggregate proper. No aggregate-proper premise is silently added to unqualified inclusion.'
arith='Ordinary EReal addition differs from top-dominant upperAdd at mixed infinities. Each proper component excludes bottom, so the two agree here. A component finite witness somewhere need not be a common finite point. EffectiveDomain f means f(x)<top; proper components exclude its generic bottom case.'
eq='Equality quantifies EVERY queried x for a positive Fin(n+1) family. ALL components are proper, convex and CLOSED. An independent z is in the LAST domain and every OTHER AMBIENT domain interior; last may be boundary. For a singleton the other-interior condition is vacuous, while all proper/convex/closed hypotheses remain. Do not replace by all interiors, relative interiors, closure or qualification at the queried x.'
scope='Six vector proof declarations retain finite-dimensional real inner-product classes; three scalar EReal proofs have no E. The full witness definition itself has no finite-dimensional binder. Completeness is derived; zero dimension and zero vectors allowed. Convexity uses REAL-height epigraphs; CLOSED means all REAL sublevels closed, not necessarily closed effective domain.'
binary='The stronger binary interface omits closedness and explicitly takes finite query values. Build the linear image of two actual real epigraphs; aggregate support gives contact and noninterior. A nonzero separating L(v,t)=A(v)+ct has c<=0 from upward heights. If c=0, variation at the qualifying interior point forces A=0 and L=0, a contradiction; hence c<0. Normalize and use Riesz to produce actual global p and g-p, treating top branches before toReal.'
induct='The mixed point yields prefix interior and an actual common finite value, so prefix/full sums are proper and prefix convex. Actual aggregate support then forces query finiteness and no-bottom summation forces every component finite. Apply the binary producer, recursively decompose the prefix, and use Fin.snoc to construct all component vectors and their exact sum. Public closedness hypotheses remain and are passed recursively; no decomposition or dual-attainment oracle is assumed.'
counts='ONE printed Theorem 2.23 with TWO conclusion branches; nine retained proofs plus one full definition are refinements, not nine source results or new mathematics. Zero new production proofs, TEST proofs or canonical registry nodes. Actual selected export has33nodes/2844 direct type-value references, including all20canary proofs/3TESTdefinitions;22 required value pairs. Readiness10nodes/1146references is separate and exactly retained; neither is a full registry export. Module import is not a direct T2.22 proof-value edge.'
can='Whole20 old canary proofs/3definitions freshly checked. Full equality constructs nonzero -1 for two quadratics+interval at0, permits last boundary0, gives both sets empty at3, and permits real singleton{0} support7 with empty REAL interior. Inclusion is genuinely invoked for quadratic+constraint support2 and empty-index zero. Concave fixture proves support absence and family vacuity; it does not itself invoke inclusion or prove a named nonconvexity theorem. Real singleton empty interior is not a zero-dimensional universal assertion.'
remaining='This package covers both T2.23 branches only. Example2.24 and all remaining Chapter1/2 main-text, source-contract and necessary appendix obligations stay REQUIRED; Chapter2 mandatorytotal null/incomplete, Chapters3-16 unenumerated, whole Goal ACTIVE. No merge/deploy/main/live update, no external Cor16.50 or Optlib reconstruction claim.'
p=Path('website/content/readings.json');d=load(p);x=next(a for a in d['readings'] if a['slug']==route);oldroute=list(x['teaching_route']);assert len(oldroute)==4
x['primary']['sections']='Section2.2.1, Theorem2.23; ONE numbered result, TWO branches, nine retained proofs and one complete witness definition'
x['notation']=[dict(term='Actual vector witnesses',meaning=M),dict(term='Exact mixed qualification',meaning=eq),dict(term='Proper components and a possibly improper sum',meaning=delta+' '+arith),dict(term='Spaces and conventions',meaning=scope)]
assert len(x['source_theorems'])==2
for card in x['source_theorems']:
 inclusion='inclusion' in card['label']
 card['relationship']=(inc+' '+delta+' '+arith if inclusion else eq+' '+binary+' '+induct)+' '+scope+' '+counts
 card['contract'].update(model='EReal ordinary finite sum and actual witness-defined Minkowski sum; global supports test ALL ambient points. '+scope,assumptions=inc if inclusion else eq,parameters='All component functions and every queried x; equality qualification point z is independent of x.',regret='No algorithm, probability, regret or measurable/computable selection guarantee.')
 card['local_status'].update(status='compiled',label='Exact retained bodies and whole public canary checked',boundary='Current focused3319/whole-canary9091 jobs;29unique kernel checks standard foundations or none, nine native guards. Distinct CONTRACT/BODY accepted. Fresh combined root/Tests/full harness and site/FINAL/PR separately pending; cached jobs included. '+remaining)
x['algorithm'].update(title='Construct actual component supports',kind='proof flow',steps=[dict(title='Sum actual support inequalities',detail=inc+' '+M),dict(title='Force a strictly negative height coefficient',detail=binary),dict(title='Construct the full family',detail=induct)])
x['proof_bridge']['summary']='Actual inclusion and reverse component-vector construction under the exact source mixed qualification.'
x['proof_bridge']['boundary']=delta+' '+arith+' '+scope+' '+counts+' '+remaining
x['proof_bridge']['steps'][1]['detail']=binary
x['proof_bridge']['steps'][3]['detail']=induct
x['worked_example']['steps'][2]['detail']='On the REAL line, indicator{0} is proper, convex and closed; its domain has empty REAL interior. With one component the other-interior condition is vacuous, so the full equality produces genuine support7 at0. The retained regularity hypotheses do not vanish.'
x['worked_example']['boundary']=can+' '+remaining
assert x['teaching_route']==oldroute
write(p,d,True)
p=Path('website/content/highlights.json');d=load(p)
for h in d['highlights']:
 if h.get('chapter')!=route:continue
 h['position']='Orabona v10 Theorem2.23 printed17-18/PDF29-30: ONE numbered result, TWO branches; retained interfaces use the shared registry.'
 h['why']=counts
 n=h['full_name'].rsplit('.',1)[-1]
 h['lean_notes']=scope+' '+(inc+' '+delta if n=='theorem_2_23_inclusion' else eq)
 if n=='theorem_2_23_inclusion':h['proof_idea']='Sum actual global component inequalities and inner-product finite sums. '+M+' '+arith
 elif n=='binary_subgradient_decomposition':h['proof_idea']=binary
 elif n=='theorem_2_23_equality':h['proof_idea']=induct+' '+binary
 elif n=='convex_finset_sum':h['proof_idea']='Induct the actual finite sum, using no-bottom arithmetic to identify upperAdd with ordinary addition. Convex sum may still be improper without a common finite point.'
write(p,d,True)
p=Path('website/content/chapters.json');d=load(p);x=next(a for a in d['chapters'] if a['slug']==route)
x.update(status='compiled',summary='Add arbitrary proper component supports; construct exact decomposition under all closedness premises and the mixed qualification.',completion_definition=counts+' This T2.23 package only.',completion_blockers=[remaining],open_gaps=[delta+' '+scope+' '+remaining])
write(p,d,True)
for p,k,key in [('website/content/readings.json','readings','slug'),('website/content/chapters.json','chapters','slug'),('website/content/highlights.json','highlights','chapter')]:
 old=load(snap[p]['snapshot']);new=load(p)
 assert [a for a in old[k] if a.get(key)!=route]==[a for a in new[k] if a.get(key)!=route],p
 for extra in set(old)-{k}:assert old[extra]==new[extra]
for n,h in freeze['headers'].items():assert hashlib.sha256(lean_declaration_header(public,n).encode()).hexdigest()==h,n
named=load(run/'public-named-declarations-v1.json');names=named['public_proofs']+named['public_definitions'];paths=[public.as_posix(),'website/content/readings.json','website/content/highlights.json','website/content/chapters.json']
c=load('research-wiki/contribution-contracts/online-subgradient-basic-migration-20261006.json')
c.update(id=task,frontier_cell=route,target='T2.23 both source branches: nine retained actual proofs/one complete M definition, zero new math/TEST/registry nodes; exact source and generic convention audit.',affected_files=paths,declarations=names)
c['source']['anchor']='ONE Theorem2.23 printed17-18/PDF29-30; TWO mandatory branches, nine retained proof refinements and one complete vector-witness definition.'
c['reuse_plan'].update(classification='reuse',decision='reuse_existing',searched_existing=['Actual nine public @types/full M/frozen headers/bodies and pinned APIs; selected33nodes2844refs/22valuepairs, old10nodes1146refs exact.'],reused_declarations=names,new_shared_declarations=[],known_consumers=['SumEqualityProbe.actual_three_component_decomposition','SumEqualityProbe.singleton_family_empty_interior','SumRuleProbe.quadratic_plus_constraint_support'],planned_consumers=['Required later Chapter2 subgradient/linearization and source-matched reuse.'],decision_reason='Reuse full actual separation/induction chain; no duplicate wrapper, TEST or per-Book library.')
c['semantic_roundtrip'].update(status='accepted',blind_decoder='/root/differentiability_blind',verdict=r['verdict'],remaining_semantic_delta=delta+' '+arith+' '+scope+' '+eq+' Distinct CONTRACT/BODY accepted; package FINAL pending, three automated actors/requested Astra medium/no humanexternal/runtime attestation.')
c['graph_contribution'].update(lean_graph='reuse-only',focus_targets=names,visual_review=counts+' Preserve all10811 old IDs/URLs and original four curated links; all ten canonical module links remain.')
c['progress_updates'].update(teaching_route='updated: original four curated links retained, full M/ten canonical names and exact source boundary visible.',website_surfaces=paths[1:],results_ledger='no-change-with-reason: additive scoped package overlay follows full gates/PR; historical chapter inventory unchanged, Chapter2total null.')
c['truth_boundary']=' '.join([M,inc,delta,arith,eq,scope,binary,induct,counts,can,remaining])
c['verification'].update(focused_checks=['Fresh nine retained proofs/full M/whole20canary proofs3defs/29named standard-or-none kernel checks/nine native guards/33nodes2844refs.'],owned_test_files=[],bandit_check='Fresh sequential root/Tests/full harness required after source-comment integration.',site_build='Clean local lean-verified build only after current combined Lean gate.',site_check='All10811oldIDsURLs/zero new canonical nodes; original four curated links/allten canonical module links; allother Book subtrees unchanged.')
write('research-wiki/contribution-contracts/online-subgradient-sum-migration-20261007.json',c)
write(run/'reader-integration-v1.json',dict(status='eleven reader qualifications integrated; final gates pending',affected_files=paths,selected_route=route,original_four_routes_retained=oldroute,all_other_Book_subtrees_unchanged=True,original_raw_math_suffix=True,public_comment_requires_fresh_Lean_gate=True,retained_proofs=9,retained_definitions=1,new_production_proofs=0,new_test_proofs=0,expected_new_registry_nodes=0,source_numbered_anchors=1,source_branches=2,source_package_accepted=False,chapter_complete=False,goal_complete=False))
with Path('MANIFEST.md').open('a',encoding='utf-8',newline='\n') as f:f.write('\n- T2.23 source package20261007: ONE source anchor/TWO branches,9retainedproofs/full M/0newmath or TESTs; whole20canaryproofs3defs/29kernelchecks/9guards/33selectednodes2844refs. Exact closed/mixed-qualification and improper-aggregate conventions visible. Shared10811registry IDs expected; combined gates/siteFINAL/PR independently pending, Chapter2/book incomplete. See runs/online-subgradient-sum-migration-20261007.\n')
for n,h in freeze['headers'].items():
 subprocess.run([sys.executable,str(run/'run-command.py'),'safe-integrated-v1-'+n,sys.executable,'-X','utf8','tools/bandit.py','safe-verify','--fence',str(run/'native-public-fences'/(n+'.json')),'--lean-file',public.as_posix(),'--lean-file','Tests/OnlineSubgradientSumCanary.lean'],check=True)
for group in ['fixed_shared_files','whole_old_canary']:
 for p,h in freeze[group].items():assert sha(p)==h,p
write(run/'integrated-public-guard-audit-v1.json',dict(status='passed',guards=9,original_raw_math_suffix=True,all_headers_fixed=True,full_definition_fixed=True,whole_canary_and_shared_files_fixed=True,guard_is_not_compilation=True))
print('Eleven reviewed reader corrections integrated; original mathematics fixed; fresh combined gates/FINAL pending.')
