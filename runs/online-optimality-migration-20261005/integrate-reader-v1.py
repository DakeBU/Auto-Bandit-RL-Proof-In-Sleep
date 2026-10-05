"""Apply separate body-review-authorized qualifications in the existing optimality subtree."""
from pathlib import Path
import json,hashlib,re,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header,_strip_lean_comments
run=Path(__file__).parent;task='ONLINE-OPTIMALITY-MIGRATION-20261005'
load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'))
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def write(p,x,existing=False):
 p=Path(p);assert p.exists() if existing else not p.exists(),p
 with p.open('w',encoding='utf-8',newline='\n') as f:
  if isinstance(x,str):f.write(x.rstrip('\n')+'\n')
  else:json.dump(x,f,ensure_ascii=False,indent=2);f.write('\n')
r=load(run/'public-body-receipt-v1.json');freeze=load(run/'draft-freeze-v1.json')
assert r['actor']['task']=='/root/source_reviewer' and r['verdict'] in ['accepted','accepted-with-explicit-delta']
assert not r.get('mathematical_repairs',r.get('required_mathematical_repairs',[])) and sha(r['report'])==r['report_sha256']
reviewed={row['path']:row['sha256'] for row in r['reviewed_files']}
for row in load(run/'public-body-inputs-v1.json')['rows']:assert reviewed[row['path']]==row['sha256']
for p,h in reviewed.items():assert sha(p)==h,p
write(run/'body-binding-audit-v1.json',dict(status='passed',raw_rows=len(reviewed),report_sha256=r['report_sha256'],retained_proofs=4,new_proofs=0,required_reader_corrections=r.get('required_reader_corrections',[])))
snap={row['path']:row for row in load(run/'historical-raw-supersession-v1.json')['rows']}
for p in ['website/content/readings.json','website/content/highlights.json','website/content/chapters.json']:assert sha(p)==snap[p]['raw_sha256']==sha(snap[p]['snapshot'])
p=Path('website/content/readings.json');d=load(p);x=next(row for row in d['readings'] if row['slug']=='online-optimality')
x['notation'][0]['meaning']='Value comparison f(x)<=f(y) for every y in V; IsMinOn does not supply membership, and x in V is an explicit hypothesis.'
x['notation'][1]['meaning']='Canonical F(z)=(f(z)).toReal. Both infinities are excluded on the supplied open U, so embedded F=f on U and locally near feasible x. No global equality/finite/noBottom/convex F outside U.'
x['notation'][2]['meaning']='The displacement y-x for every y in V; actual gradient of F at x pairs nonnegatively at a constrained minimum. Gradient-zero equivalence additionally requires ambient interior V.'
card=x['source_theorems'][0];card['label']='Theorem2.8 and following unnumbered interior consequence'
card['plain']='Every feasible directional inner product characterizes the given constrained minimum. The following mandatory unnumbered source consequence adds ambient interior V for gradient-zero equivalence; boundary gradients may be nonzero.'
card['relationship']='Shared theorem_2_8 weakens source neighborhood convexity to ConvexOn V F, yielding a stronger theorem, not a stronger premise or equivalence of assumptions. Source neighborhood convexity restricts to V; the public canary constructs ConvexOn U then restricts it. Actual U need not be convex. minOn_real_iff_gradient and minOn_finitePart_iff are generalized real and finite-order library helpers, not printed theorems. interior_min_iff_gradient_zero represents the mandatory following unnumbered main-text consequence.'
card['contract']['model']='Complete real inner-product spaces explicitly generalize source Euclidean spaces; EReal f and canonical F(z)=(f(z)).toReal, finite and differentiable on supplied open U containing V.'
card['contract']['assumptions']='Nonempty convex V, explicit x in V; arbitrary open U contains V; f excludes both infinities on U, so embedded F=f there and locally near x; DifferentiableOn F U; ConvexOn V F. No convex U or global noBottom/finite/convex F premise outside U. Ambient interior V is additional for gradient-zero equivalence; the differentiability premise is retained.'
card['contract']['guarantee']='Original EReal IsMinOn f V x iff every feasible inner(gradient F x,y-x)>=0; with ambient interior V, iff gradient F x=0. No optimizer existence, uniqueness, closedness, boundedness or zero minimum-value claim.'
card['local_status']['boundary']='Theorem2.8, its mandatory following unnumbered consequence and two explicitly classified library helpers only; Chapter2 and the whole book remain incomplete, including later source and legacy migrations/Jensen mapped separately.'
x['algorithm']['steps'][0]['detail']='The everywhere-real helper assumes ConvexOn V, x membership and an ambient derivative at x. Actual minimum derivatives on convex feasible segments are nonnegative; no open set or EReal bridge is needed by this helper.'
x['algorithm']['steps'][1]['detail']='The supporting bound proves sufficiency. The separate finite-order bridge compares canonical real and EReal minima using x membership and finite values only on V; it needs no convexity, openness or derivative.'
x['algorithm']['steps'][2]['detail']='Ambient interior V makes a constrained minimum local in the whole space. Actual differentiability on open U is retained, so Fermat/gradient-zero has derivative meaning despite the total fderiv fallback.'
assert len(x['notation'])==3 and len(x['teaching_route'])==4
write(p,d,True)
p=Path('website/content/highlights.json');d=load(p)
for x in d['highlights']:
 if x.get('chapter')!='online-optimality':continue
 n=x['full_name'].rsplit('.',1)[-1]
 if n=='minOn_real_iff_gradient':
  x['position']='Generalized everywhere-real library helper for Theorem2.8, Orabona v10 printedp11/PDF23; not another printed theorem.'
  x['plain']='For everywhere-real f, ConvexOn V, explicit x membership and an ambient derivative at x, the minimum iff every feasible gradient direction is nonnegative.'
  x['lean_notes']='ConvexOn includes convex V. This helper has no open set, finite-part bridge or differentiability-at-all-points premise. IsMinOn only compares values; membership is separate. Boundary gradient need not vanish.'
 elif n=='minOn_finitePart_iff':
  x['position']='Finite-order library bridge for Theorem2.8, Orabona v10 printedp11/PDF23; not a printed theorem.'
  x['plain']='Explicit x membership and exclusion of both infinities at every point of V make original EReal and canonical real minimum comparisons equivalent.'
  x['lean_notes']='Only finite values on V are required; either infinity outside V is allowed. No convexity, open neighborhood, differentiability or topology of V. Shared complete-inner-product context is retained but unnecessary for this order fact; no neighborhood equality is asserted by this helper.'
 elif n=='theorem_2_8':
  x['plain']='Given nonempty convex V and x in V, finite differentiability on arbitrary open U containing V and ConvexOn V for canonical F characterize the minimum by all feasible gradient directions.'
  x['lean_notes']='Convexity on V is a weaker premise yielding a stronger theorem than source neighborhood convexity, not equivalent assumptions. Actual U need not be convex. F(z)=(f(z)).toReal embeds as f on finite U and locally near x; no global noBottom/finite/convex F outside U. No existence/uniqueness/closedness/boundedness claim.'
 else:
  assert n=='interior_min_iff_gradient_zero'
  x['position']='Mandatory unnumbered interior consequence following Theorem2.8, Orabona v10 printedp11/PDF23.'
  x['plain']='At an ambient-interior feasible point, under the finite/open/differentiable/convex-on-V premises, being a minimum is equivalent to gradient F x=0.'
  x['lean_notes']='Ambient interior, not relative interior; no boundary-zero-gradient claim. Same canonical F/finite U/local equality as theorem_2_8; differentiability retained despite total fderiv fallback. Zero gradient is a vector condition, not zero loss or uniqueness.'
 x['intuition']=x['plain']
write(p,d,True)
p=Path('website/content/chapters.json');d=load(p);x=next(row for row in d['chapters'] if row['slug']=='online-optimality')
x['summary']='Theorem2.8 and its mandatory unnumbered ambient-interior zero-gradient consequence, with explicit convex-on-V generalization and canonical finite-neighborhood derivative; boundary minima can have nonzero gradients.'
x['completion_definition']='Theorem2.8, following mandatory unnumbered interior-gradient-zero consequence and two library helpers. Four retained unchanged proofs, zero new proof code or registry nodes. This is not completion of Chapter 2.'
write(p,d,True)
for p,k,key in [('website/content/readings.json','readings','slug'),('website/content/chapters.json','chapters','slug'),('website/content/highlights.json','highlights','chapter')]:
 old=load(snap[p]['snapshot']);new=load(p)
 assert [row for row in old[k] if row.get(key)!='online-optimality']==[row for row in new[k] if row.get(key)!='online-optimality']
 for extra in set(old)-{k}:assert old[extra]==new[extra]
public=Path('BanditRLProof/OnlineConvexOptimality.lean');tokens=lambda s:re.sub(r'\s+',' ',_strip_lean_comments(s)).strip()
assert tokens(public.read_text(encoding='utf-8'))==tokens((run/'original-OnlineConvexOptimality.lean.txt').read_text(encoding='utf-8'))
for n,h in freeze['headers'].items():assert hashlib.sha256(lean_declaration_header(public,n).encode()).hexdigest()==h
for p,h in freeze['canary'].items():assert sha(p)==h
paths=[public.as_posix(),'website/content/readings.json','website/content/highlights.json','website/content/chapters.json'];names=['BanditRL.OnlineConvex.'+n for n in freeze['headers']]
c=load('research-wiki/contribution-contracts/online-first-order-migration-20261005.json')
c.update(id=task,frontier_cell='online-optimality',target='Distinctly revalidate retained Theorem2.8/mandatory interiorzero consequence/two library helpers and qualify only their existing Book reader without changing proof code.',affected_files=paths,declarations=names)
c['source']['anchor']='Theorem2.8 and following mandatory unnumbered interior-gradientzero consequence, printed11/PDF23; weaker convexity only on V explicit, two library helpers not printed results.'
c['reuse_plan']=dict(classification='reuse',decision='reuse_existing',searched_existing=['Actual4public declarations/native types, pinned tangentcone/derivative/IsMinOn/EReal APIs and fresh compiled shared-root4node510edge scopedgraph.'],reused_declarations=names,new_shared_declarations=[],known_consumers=['Tests.OnlineConvexOptimalityCanary'],planned_consumers=['Remaining Chapter2 first-order/subgradient/source chain'],no_duplicate_wrapper=True,decision_reason='Four unchanged proofs/zero definitions/new proof code/nodes; shared project and source-compatible convexity restriction reused.')
c['semantic_roundtrip'].update(status='accepted',verdict=r['verdict'],remaining_semantic_delta='Distinct source-contract/body review; complete Hilbert generality/canonical finite-neighborhood derivative/weaker ConvexOn V premise stronger theorem explicit. Final corrected reader/package review pending; no human/external/runtime attestation.')
c['graph_contribution'].update(lean_graph='reuse-only',focus_targets=names,functor_reason='Retained convex optimality foundations; no cross-setting functor claim.',visual_review='Fresh actual compiled scoped4node510edge graph; corrected reader/registry/site gates pending.')
c['progress_updates'].update(teaching_route='updated: same online-optimality route/4highlights/4links; helper assumptions/source-weakening/interior/canonical derivative qualifications corrected.',website_surfaces=paths[1:])
c['truth_boundary']='Four retained proofs/zero definitions/new proof code/registry nodes. Source terminal finite/differentiable canonical F on arbitrary open U containing nonempty convex V; weaker convexity only on V explicit, no convexU/global noBottom/finite/convexF outsideU. Real helper no open/EReal bridge; finite bridge finiteV only/no convexity/topology/derivative. IsMinOn membership separate; zero-gradient iff extra ambient interior, retained actual derivative. No existence/uniqueness/closedness/boundedness claim. This is not completion of Chapter 2 or Chapters1-16; all remaining source/legacy obligations retained and stacked PR/local compilation do not update main/live.'
c['verification'].update(focused_checks=['Fresh actual module/canary/focused build;13 named standard3-or-none axiom audits;4 native guards; unchanged4headers/proof tokens/canary bytes.'],bandit_check='Fresh combined root/Tests/full harness pending.',site_build='Clean lean-verified build only after fresh applicable combined gate.',site_check='Same4canonicalnodes/oldIDsURLs/source-qualified reader checks pending.')
write('research-wiki/contribution-contracts/online-optimality-migration-20261005.json',c)
write(run/'reader-integration-v1.json',dict(status='integrated-package-pending',affected_files=paths,selected_route='online-optimality',required_reader_corrections_addressed=True,
 all_other_Book_subtrees_unchanged=True,all_headers_code_canary_preserved=True,new_proofs=0,new_registry_nodes=0,chapter_complete=False,goal_complete=False))
print('Required optimality reader qualifications integrated; otherBooksubtrees/allcode/headers/canary preserved.')
