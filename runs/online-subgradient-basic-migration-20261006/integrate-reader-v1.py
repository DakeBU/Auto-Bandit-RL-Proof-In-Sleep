"""Apply separately reviewed subgradient source qualifications without changing mathematics."""
from pathlib import Path
import hashlib,json,re,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header,_strip_lean_comments
run=Path(__file__).parent;task='ONLINE-SUBGRADIENT-BASIC-MIGRATION-20261006';route='online-subgradient-basic'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();load=lambda p:json.loads(Path(p).read_text(encoding='utf8'))
def write(p,x,existing=False):
 p=Path(p);assert p.exists() if existing else not p.exists(),p
 with p.open('w',encoding='utf8',newline='\n') as f:
  if isinstance(x,str):f.write(x.rstrip('\n')+'\n')
  else:json.dump(x,f,ensure_ascii=False,indent=2);f.write('\n')
r=load(run/'public-body-receipt-v1.json');freeze=load(run/'draft-freeze-v1.json')
assert r['actor']['task']=='/root/source_reviewer' and r['verdict'] in ['accepted','accepted-with-explicit-delta'] and sha(r['report'])==r['report_sha256']
assert not r.get('mathematical_repairs',r.get('required_mathematical_repairs',[]))
reviewed={row['path']:row['sha256'] for row in r['reviewed_files']}
for row in load(run/'public-body-inputs-v1.json')['rows']:assert reviewed[row['path']]==row['sha256'],row['path']
for p,h in reviewed.items():assert sha(p)==h,p
write(run/'body-binding-audit-v1.json',dict(status='passed',raw_rows=len(reviewed),report_sha256=r['report_sha256'],retained_proofs=2,retained_definitions=1,new_proofs=0,required_reader_corrections=r.get('required_reader_corrections',[])))
snap={row['path']:row for row in load(run/'historical-raw-supersession-v1.json')['rows']}
for p in ['website/content/readings.json','website/content/highlights.json','website/content/chapters.json']:assert sha(p)==snap[p]['raw_sha256']==sha(snap[p]['snapshot'])
public=Path('BanditRLProof/OnlineSubgradientBasic.lean');original=(run/'original-OnlineSubgradientBasic.lean.txt').read_bytes();assert public.read_bytes()==original
comment='''/-
Orabona v10 printed16-17/PDF28-29: Definition2.20, the required adjacent
outside-domain/dom-subdifferential inclusion observation, and Theorem2.21.
Two retained proofs, one complete definition; zero new math code/nodes.
The printed definition explicitly restricts to proper functions. The generic
SourceSubdifferential predicate accepts all EReal functions, a wider library
scope faithful on proper functions. At bottom points and for identically top
functions every vector supports; outside-domain emptiness needs properness.
EffectiveDomain excludes top but includes bottom generically; SourceProper
excludes bottom and supplies a genuine finite global witness. The point-domain
proof uses that witness/support, drops source convexity (stronger theorem),
and exactly gives dom subdifferential inclusion and outside emptiness via
witness unpacking. No converse or support-existence producer is claimed.
Theorem2.21 uses globally real f, Convex V, and existing GLOBAL supports at
EVERY point of V, tested at ALL ambient y. This is the printed hypothesis;
ConvexOn is produced by nonnegative weighted supports and inner cancellation,
including weights0/1. No merely finite-on-V extended-real extension is claimed.
Actual arbitrary real inner-product scope generalizes finite Euclidean source;
no CompleteSpace/FiniteDimensional premises. Ambient E has zero/nonempty;
V may be empty/full/unbounded. Two independent leaves share the definition,
not a mutual theorem dependency chain. Three scoped nodes/320 direct references
are not full/canary graph export. Whole3canaries/6named kernel dependency
checks/2nativeguards are distinct from combined acceptance gates.
Initial context source-properness prose was corrected before stabilization;
original draft history remains preserved. Interior existence and the stronger
relative-interior footnote, Theorems2.22/2.23, Chapter2 and the persistent
Chapters1-16 Goal remain mandatory/incomplete.
-/
'''
assert not re.search(r'\b(sorry|admit|axiom|postulate)\b',comment)
public.write_bytes(comment.encode()+original)
write(run/'public-comment-qualification-v1.json',dict(path=public.as_posix(),original_sha256=hashlib.sha256(original).hexdigest(),qualified_sha256=sha(public),delta='leading ordinary ignored source/scope comment only',exact_original_bytes_retained_as_suffix=True))
proper='Definition2.20 is printed for PROPER f. Actual complete SourceSubdifferential is a wider predicate on all EReal functions, faithful when restricted to proper functions. Convexity is not a definition premise; no unrestricted source equivalence.'
generic='Generic bottom points and identically-top functions admit all vectors as supports. effectiveDomain means f(x)<top and includes bottom generically; SourceProper excludes bottom and supplies an actual finite point. Actual inner-product E has zero and is nonempty; V may be empty/full/unbounded.'
domain='Actual subgradient_point_finite requires SourceProper and global support, but drops convexity from the adjacent source observation: a stronger theorem. A finite global witness rules out f(x)=top. Universal x,g membership->domain exactly yields {x|S(f,x).Nonempty} subset effectiveDomain and empty support outside domain by unpacking g/contradiction. No converse or existence producer.'
real='Theorem2.21 uses globally REAL f, Convex V and forall x in V exists g forall ambient y supporting inequality. Support existence is the printed hypothesis, not a produced general existence theorem or desired convexity input. No merely finite-on-V EReal extension.'
scope='Source finite Euclidean scope specializes arbitrary real-inner-product Lean scope, a stronger generalization with no CompleteSpace/FiniteDimensional premise. Ambient E nonempty via zero; empty V allowed. Weights a,b>=0,a+b=1 include endpoints0/1.'
counts='Two numbered anchors plus one REQUIRED adjacent unnumbered result group; two retained proofs/one complete definition/zero new math code,nodes. Two independently ready leaves shareS, no mutual proof value edges. Actual3scopednodes320direct type/value references, not full/canary export.'
canary='Whole unchanged3genuine canary proofs: global quadratic2x support for every realx, actual Theorem2.21 produces square convexity on univ, and everyg ruled out at2 outside canonical real[0,1] indicator with actual properness produced via shared indicator theorem. All6named checks include complete definition;2nativeguards are separate from compilation.'
remaining='Source properconvex interior existence and relative-interior footnote, Theorems2.22/2.23 and later Chapter2 main-text/appendix/legacy matching remain REQUIRED separately, including already compiled bodies. Not Chapter2 completion; Chapter1 migration/Chapter2mandatorytotalnull/incomplete/Chapters3-16mandatoryunenumerated/wholeGoalACTIVE. No merge/deploy/live update.'
p=Path('website/content/readings.json');d=load(p);x=next(row for row in d['readings'] if row['slug']==route)
x['primary']['sections']='Section2.2.1, Definition2.20, required adjacent outside-domain/dom-subdifferential inclusion group, Theorem2.21; two numbered anchors, two retained proofs/one definition'
for row,value in zip(x['notation'],[proper+' Global supports test ALL ambient y.',generic,real+' '+scope]):row['meaning']=value
for i,card in enumerate(x['source_theorems']):
 card['relationship']=proper+' '+scope+' '+counts
 card['local_status']['label']='Retained subgradient bodies, freshly checked'
 card['local_status']['boundary']='Distinct CONTRACT/BODY, actual6named kernel dependency checks/2nativeguards and whole3canaries; combinedrootTests/fullharness/site/finalreader/PR acceptance separate. '+remaining
 card['contract']['regret']='Foundational support/domain/convexity conclusions only; no algorithm or regret guarantee.'
 if i==0:
  card['contract'].update(model=proper+' '+generic,assumptions='Actual SourceProper f and g global support at x; no convexity/closedness/differentiability. Source proper+convex observation has convexity dropped in stronger actual theorem.',parameters=domain,guarantee='Universal support-point domain membership, equivalently dom subdifferential subset domf and empty support outside domf for proper f.')
 else:card['contract'].update(model=real,assumptions=real,parameters=scope+' Supports remain global even when conclusion is only on V.',guarantee='ConvexOn real V f, containing ConvexV and the weighted Jensen inequality, including zero weights.')
x['proof_bridge']['summary']='Two independently ready proofs share the full support predicate; teaching order is not a mutual theorem dependency chain.'
x['proof_bridge']['steps'][0]['detail']=domain
x['proof_bridge']['steps'][1]['detail']=real+' Choose g at z=a*x+b*y inV and test both endpoints.'
x['proof_bridge']['steps'][2]['detail']='Multiply inequalities by nonnegative a,b, including0/1. Actual inner_sub_right/real_inner_smul_right and a+b=1 cancel weighted displacements; produce ConvexOn, without assuming desired function convexity.'
x['proof_bridge']['boundary']=proper+' '+generic+' '+counts+' '+remaining
x['worked_example']['steps'][0]['detail']='For EVERY realx, actual slope2x globally supports y^2 via nonnegative square residual; a real nonconstant producer, no supplied desired convexity.'
x['worked_example']['steps'][1]['detail']='Apply actual public Theorem2.21 to that support producer on real univ; square convexity is derived.'
x['worked_example']['steps'][2]['detail']='Shared canonical zero-on[0,1]/top-outside indicator is actually proved proper via the accepted indicator iff and point0. Public point-domain theorem/effectiveDomain identity exclude EVERYg at2.'
x['worked_example']['boundary']=canary+' Generic bottom/top all-vector cases are semantic boundary observations, not additional claimed canary tests. '+remaining
for row,value in zip(x['algorithm']['steps'],[domain,real+' Choose a support at the convex mixture using ConvexV.',scope+' Weighted lower bounds cancel actual inner displacements to produce function convexity.']):row['detail']=value
write(p,d,True)
p=Path('website/content/highlights.json');d=load(p)
for x in d['highlights']:
 if x.get('chapter')!=route:continue
 n=x['full_name'].rsplit('.',1)[-1];x['position']='Orabona v10 printed16-17/PDF28-29;2numberedanchors+required adjacent unnumbered domain group/2retainedproof1definition/0newnodes.'
 x['lean_notes']=(proper+' '+generic+' '+domain if n=='subgradient_point_finite' else real+' '+scope)
 x['why']='Source-qualified reuse in SAME shared Lean/Book registry; no new proof-count gain or Chapter2 completion.'
 x['proof_idea']=domain if n=='subgradient_point_finite' else 'Support at convex mixture; global tests at both endpoints; nonnegative weights incl0/1 cancel actual inner displacements. '+real
write(p,d,True)
p=Path('website/content/chapters.json');d=load(p);x=next(row for row in d['chapters'] if row['slug']==route)
x['summary']='Proper-source specialization of the global support predicate, finite-witness domain inclusion and real-valued convex restrictions, with explicit source deltas.'
x['completion_definition']=counts+' not Chapter2 completion.'
x['completion_blockers']=[remaining]
x['learning_goals']=['Separate source proper restriction from generic all-EReal predicate and bottom/top degeneracy.','Derive finite support points from a real witness and recover quantified domain inclusion/outside emptiness.','Read globallyREAL/globalambient supports and legitimate existence hypothesis in Theorem2.21.','Cancel weighted supports incl0/1; distinguish independent proofs from teaching order and keep remaining interior rules mandatory.']
x['open_gaps']=[remaining]
write(p,d,True)
for p,k,key in [('website/content/readings.json','readings','slug'),('website/content/chapters.json','chapters','slug'),('website/content/highlights.json','highlights','chapter')]:
 old=load(snap[p]['snapshot']);new=load(p);assert [row for row in old[k] if row.get(key)!=route]==[row for row in new[k] if row.get(key)!=route],p
 for extra in set(old)-{k}:assert old[extra]==new[extra]
tokens=lambda s:re.sub(r'\s+',' ',_strip_lean_comments(s)).strip()
assert public.read_bytes().endswith(original) and tokens(public.read_text(encoding='utf8'))==tokens(original.decode())
for n,h in freeze['headers'].items():assert hashlib.sha256(lean_declaration_header(public,n).encode()).hexdigest()==h
for p,h in dict(freeze['canary'],**freeze['root_Tests']).items():assert sha(p)==h
paths=[public.as_posix(),'website/content/readings.json','website/content/highlights.json','website/content/chapters.json'];named=load(run/'public-named-declarations-v1.json');names=named['public_proofs']+named['public_definitions']
c=load('research-wiki/contribution-contracts/online-closed-proper-migration-20261006.json')
c.update(id=task,frontier_cell=route,target='Definition2.20/required domain observation/T2.21:2retainedproof1full definition/0newmathcode; sourceproperness/genericpredicate/quantifier/domainconversion/scope/canary/count qualifications; mathematics fixed.',affected_files=paths,declarations=names)
c['source']['anchor']='Definition2.20+required adjacent unnumbered outside-domain/domsubdifferential inclusion group+Theorem2.21, printed16-17/PDF28-29.'
c['reuse_plan']=dict(classification='reuse',decision='reuse_existing',searched_existing=['Actual2frozenheaders/full support definition/6@types/scoped3nodes320edges and pinned inner/EReal/ConvexOn APIs.'],reused_declarations=names,new_shared_declarations=[],known_consumers=['Tests.OnlineSubgradientBasicCanary'],planned_consumers=['Required subsequent Chapter2 interior/singleton/sum/OSD source matching.'],no_duplicate_wrapper=True,decision_reason='Exact existing support/domain/realconvexity bodies; explicit source specialization/deltas;0newmathcode/nodes.')
c['semantic_roundtrip'].update(status='accepted',verdict=r['verdict'],remaining_semantic_delta=proper+' '+domain+' '+real+' '+scope+' Distinct CONTRACT/BODY accepted; final package pending. Three automated actors requestedAstra medium, nohumanexternal/runtimeattestation.')
c['graph_contribution'].update(lean_graph='reuse-only',focus_targets=names,functor_reason='Source-qualified shared registry reuse; no separately certified setting functor/discovery.',visual_review=counts+'10809oldIDsURLs/0newexpected; sitepending.')
c['progress_updates'].update(teaching_route='updated: Same2selectedlinks/highlights; separately reviewed proper-source/genericpredicate/domainconversion/globalREALsupport/generalizedscope/canary/count boundaries.',website_surfaces=paths[1:])
c['truth_boundary']=proper+' '+domain+' '+real+' '+scope+' '+counts+' '+canary+' RootTests/fullharness/site/finalreader/PRpending. '+remaining
c['verification'].update(focused_checks=['Actual2proofs1complete definition/whole3canaries/6standard3-or-none named kernel dependency checks/no sorryAx/2nativeguards; allmathtokens/canary/rootTests fixed.'],owned_test_files=[],bandit_check='Fresh sequentialroot/Tests/fullharness pending.',site_build='Clean lean-verified local build only after current combinedLeangate.',site_check='Same3canonicalnodes/all10809IDsURLs/0newexpected/sourcequalifiedreader pending.')
write('research-wiki/contribution-contracts/online-subgradient-basic-migration-20261006.json',c)
write(run/'reader-integration-v1.json',dict(status='integrated-package-pending',affected_files=paths,selected_route=route,required_reader_corrections_addressed=True,all_other_Book_subtrees_unchanged=True,all_headers_proof_definition_tokens_canary_root_Tests_preserved=True,retained_proofs=2,retained_definitions=1,new_proofs=0,new_registry_nodes=0,source_terminal_accepted=False,chapter_complete=False,goal_complete=False))
with Path('MANIFEST.md').open('a',encoding='utf8',newline='\n') as f:f.write('\n- Subgradient basic migration20261006: Definition2.20/required domain observation/T2.21;2retainedproof1complete definition/0newmathcode,nodes. Explicit printedproperness/genericallEReal specialization/finitewitness/domainconversion/globallyREALsupport/arbitraryinnerproduct/independentleaves/whole3canaries6checks2guards; combined/finalreader/PRpending, Chapter2/Bookincomplete. See runs/online-subgradient-basic-migration-20261006.\n')
print('Eight reviewed source qualifications applied; mathematicalbytes retained, other Book subtrees unchanged.')
