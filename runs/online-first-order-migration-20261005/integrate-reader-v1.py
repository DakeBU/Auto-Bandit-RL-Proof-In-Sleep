"""Integrate distinctly reviewed first-order semantics only in its existing Book subtree."""
from pathlib import Path
import hashlib,json,re,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header,_strip_lean_comments
run=Path(__file__).parent;task='ONLINE-FIRST-ORDER-MIGRATION-20261005'
load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'))
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def write(p,x,existing=False):
    p=Path(p);assert p.exists() if existing else not p.exists(),p
    with p.open('w',encoding='utf-8',newline='\n') as f:
        if isinstance(x,str):f.write(x.rstrip('\n')+'\n')
        else:json.dump(x,f,ensure_ascii=False,indent=2);f.write('\n')
r=load(run/'public-body-receipt-v1.json');freeze=load(run/'draft-freeze-v1.json')
assert r['actor']['task']=='/root/source_reviewer' and r['verdict'] in ['accepted','accepted-with-explicit-delta']
assert not r.get('mathematical_repairs',r.get('required_mathematical_repairs',[]))
assert sha(r['report'])==r['report_sha256']
reviewed={row['path']:row['sha256'] for row in r['reviewed_files']}
for row in load(run/'public-body-inputs-v1.json')['rows']:assert reviewed[row['path']]==row['sha256']
for p,h in reviewed.items():assert sha(p)==h,p
write(run/'body-binding-audit-v1.json',dict(status='passed',raw_rows=len(reviewed),report_sha256=r['report_sha256'],
    retained_proofs=3,new_proofs=0,required_reader_corrections=r.get('required_reader_corrections',[])))
snap={row['path']:row for row in load(run/'historical-raw-supersession-v1.json')['rows']}
for p in ['website/content/readings.json','website/content/highlights.json','website/content/chapters.json']:
    assert sha(p)==snap[p]['raw_sha256']==sha(snap[p]['snapshot'])
p=Path('website/content/readings.json');d=load(p);x=next(row for row in d['readings'] if row['slug']=='online-first-order')
x['notation'][0]['meaning']='Canonical F(z)=(f(z)).toReal is everywhere real-valued; its embedding equals f locally near the ambient-interior point x, under global noBottom. The gradient is of this F at x.'
x['notation'][1]['meaning']='Ambient interior of {z | f(z)<positive infinity}; global noBottom makes values finite on that neighborhood. Relative interior is not substituted.'
card=x['source_theorems'][0]
card['plain']='Under global noBottom, convexity, ambient-interior membership and differentiability of canonical F at x, the comparator is every y, including positive infinity outside the domain.'
card['relationship']='Exact shared extended-real endpoint theorem_2_7; finitePart_eventually is a local representation helper and convex_gradient_lower_bound a generalized everywhere-real ConvexOn helper, not additional printed theorems. Historical OnlineGradientDescent.first_order uses stronger RegularLoss: convexity and differentiability on a convex open neighborhood containing V. Separately, OnlineGradientDescentSource.source_to_feasible derives feasible-set convexity and ambient derivatives from the source arbitrary-open differentiability neighborhood; its first_order reuses the real helper. Neither connection is an equivalence between these regularity predicates.'
card['contract']['assumptions']='Global noBottom and convex real-height epigraph; x in ambient interior of effectiveDomain; DifferentiableAt of canonical F(z)=(f(z)).toReal at x. finitePart_eventually proves local embedding identity near x; no global identity with f or global convexity of F is asserted.'
card['contract']['guarantee']='f(x)+embedded inner(gradient F x,y-x) <= f(y) for every y; outside-domain f(y)=positive infinity remains in the conclusion. No bounded/closed domain or global differentiability hypothesis.'
card['local_status']['boundary']='Theorem2.7 and two explicitly classified library helpers only; Chapter2 and the whole book remain incomplete. Later source and legacy migration obligations, including Jensen mapped separately, are still required.'
x['algorithm']['steps'][0]['detail']='Global noBottom and ambient interior supply a neighborhood identity between f and the embedding of canonical F(z)=(f(z)).toReal. This identity is local.'
x['algorithm']['steps'][1]['detail']='The generalized real helper assumes everywhere-real f, ConvexOn V, x/y in V and an ambient derivative at x. It uses a convex affine-line secant; V need not be open and that helper does not use the extended-real representation lemma.'
assert len(x['notation'])==3 and len(x['teaching_route'])==3
write(p,d,True)
p=Path('website/content/highlights.json');d=load(p)
for x in d['highlights']:
    if x.get('chapter')!='online-first-order':continue
    name=x['full_name'].rsplit('.',1)[-1]
    if name=='finitePart_eventually':
        x['position']='Library local representation helper for Theorem2.7, Orabona v10 printedp11/PDF23; not a separate printed theorem.'
        x['plain']='Global exclusion of negative infinity and ambient-interior membership prove that canonical toReal embeds back to f locally near x.'
        x['lean_notes']='No convexity or differentiability premise is used. General domain f<top can include bottom, so global noBottom is explicit. Local identity only; top may occur away from x. Ambient, not relative, interior.'
    elif name=='convex_gradient_lower_bound':
        x['position']='Generalized everywhere-real library helper supporting Theorem2.7, Orabona v10 printedp11/PDF23; not another printed theorem.'
        x['plain']='For everywhere-real f, ConvexOn V, x/y in V and an ambient derivative at x give the supporting bound at y.'
        x['lean_notes']='ConvexOn includes convex V. V need not be open, closed or bounded; no extended-real local representation lemma is needed by this real helper. Differentiability is ambient at x only, and y must belong to V.'
    else:
        assert name=='theorem_2_7'
        x['plain']='Global noBottom, convexity, ambient-interior x and differentiability of canonical F(z)=(f(z)).toReal at x give the bound for every y, including positive infinity outside the domain.'
        x['lean_notes']='The neighborhood lemma proves local embedded F=f near x; neither global equality with f nor global convexity of F is claimed. Domain comparators use the finite ConvexOn bridge; outside-domain f(y)=top is proved. Complete real inner-product spaces generalize the source Euclidean setting.'
    x['intuition']=x['plain']
write(p,d,True)
p=Path('website/content/chapters.json');d=load(p);x=next(row for row in d['chapters'] if row['slug']=='online-first-order')
x['summary']='Theorem2.7 for all comparators, with global noBottom, ambient-interior x, canonical local finite representation and two explicitly classified library helpers.'
x['completion_definition']='Orabona Theorem2.7 and two retained library helpers: local finite representation and generalized everywhere-real supporting bound. Three unchanged proofs, zero new proof code or registry nodes. This is not completion of Chapter 2.'
x['learning_goals'][0]='Interpret the gradient of canonical F(z)=(f(z)).toReal using a proved local embedding identity under global noBottom and ambient-interior membership.'
write(p,d,True)
for p,key,selector in [('website/content/readings.json','readings','slug'),('website/content/chapters.json','chapters','slug'),('website/content/highlights.json','highlights','chapter')]:
    old=load(snap[p]['snapshot']);new=load(p)
    assert [x for x in old[key] if x.get(selector)!='online-first-order']==[x for x in new[key] if x.get(selector)!='online-first-order']
    for k in set(old)-{key}:assert old[k]==new[k]
public=Path('BanditRLProof/OnlineConvexFirstOrder.lean')
token=lambda s:re.sub(r'\s+',' ',_strip_lean_comments(s)).strip()
assert token(public.read_text(encoding='utf-8'))==token((run/'original-OnlineConvexFirstOrder.lean.txt').read_text(encoding='utf-8'))
for n,h in freeze['headers'].items():assert hashlib.sha256(lean_declaration_header(public,n).encode()).hexdigest()==h
for p,h in freeze['canary'].items():assert sha(p)==h
paths=[public.as_posix(),'website/content/readings.json','website/content/highlights.json','website/content/chapters.json']
names=['BanditRL.OnlineConvex.'+n for n in freeze['headers']]
c=load('research-wiki/contribution-contracts/online-convex-migration-20261005.json')
c.update(id=task,frontier_cell='online-first-order',target='Distinctly revalidate retained Theorem2.7/local representation/real helper and correct first-order readers without changing proof code.',affected_files=paths,declarations=names)
c['source']['anchor']='Theorem2.7 printed11/PDF23; local representation and generalized real ConvexOn bounds are library helpers. Canonical finite-part derivative locally justified; all-y/top retained.'
c['reuse_plan']=dict(classification='reuse',decision='reuse_existing',searched_existing=['Actual3 public declarations/scoped types, pinned gradient/ConvexOn/EReal APIs and fresh compiled shared-root3node416edge scope.'],reused_declarations=names,new_shared_declarations=[],known_consumers=['Tests.OnlineConvexFirstOrderCanary','BanditRL.OnlineGradientDescentSource.first_order'],planned_consumers=['Remaining Chapter2 first-order/optimality/subgradient source chain'],no_duplicate_wrapper=True,decision_reason='Three unchanged proofs/no definitions/new nodes; real helper already used by source-compatible OGD adapter in the same library.')
c['semantic_roundtrip'].update(status='accepted',verdict=r['verdict'],remaining_semantic_delta='Distinct source-contract/body review; complete inner-product-space generality and canonical local derivative interpretation explicit. Final corrected reader/package review pending; no human/external/runtime model attestation.')
c['graph_contribution'].update(lean_graph='reuse-only',focus_targets=names,functor_reason='Retained supporting-gradient foundations; no cross-setting functor claim.',visual_review='Fresh actual compiled scoped3node416edge graph; corrected reader/registry/site gates pending.')
c['progress_updates'].update(teaching_route='updated: same online-first-order route/3highlights/3links; only source assumptions/helper classification/OGD regularity qualification corrected.',website_surfaces=paths[1:])
c['truth_boundary']='Three retained proofs/zero definitions, new proof code or registry nodes. Source terminal retains global noBottom, convex real epigraph, ambient interior, derivative of canonical F and every y including top outside. Local helper uses no convexity/derivative; real helper uses everywhere-real f/ConvexOn V/x,y membership/ambient derivative without open V or local EReal bridge. Historical RegularLoss OGD stronger; separate source-compatible adapter explicit. This is not completion of Chapter 2 or Chapters1-16. Legacy migrations and source enumeration remain required; stacked PR/local compilation do not update main/live.'
c['verification'].update(focused_checks=['Fresh actual module/canary/focused build;12 named standard3-or-none axiom audits;3 native guards; unchanged headers/code tokens/canary bytes.'],bandit_check='Fresh combined root/Tests/full harness still pending as integrated gate.',site_build='Clean lean-verified build only after fresh applicable combined Lean/harness gate.',site_check='Same3 canonical nodes/old IDsURLs/source-qualified reader checks pending.')
write('research-wiki/contribution-contracts/online-first-order-migration-20261005.json',c)
write(run/'reader-integration-v1.json',dict(status='integrated-package-pending',affected_files=paths,selected_route='online-first-order',
    required_reader_corrections_addressed=True,all_other_Book_subtrees_unchanged=True,all_headers_code_canary_preserved=True,new_proofs=0,new_registry_nodes=0,chapter_complete=False,goal_complete=False))
print('Required first-order reader qualifications integrated; all other Book subtrees/code/header/canary unchanged.')
