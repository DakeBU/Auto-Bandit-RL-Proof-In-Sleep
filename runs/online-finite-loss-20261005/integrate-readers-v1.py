"""Publish two exact source-qualified endpoints in the existing shared Book route."""
from pathlib import Path
import json,hashlib
run=Path(__file__).parent
def load(p):return json.loads(Path(p).read_text(encoding='utf-8'))
def save(p,x):
    with Path(p).open('w',encoding='utf-8',newline='\n') as f:json.dump(x,f,ensure_ascii=False,indent=2);f.write('\n')
snap={r['path']:r for r in load(run/'historical-raw-supersession-v1.json')['rows']}
for p in ['website/content/readings.json','website/content/highlights.json','website/content/chapters.json']:
    assert hashlib.sha256(Path(p).read_bytes()).hexdigest()==snap[p]['raw_sha256'],p
boundary='Two new compiled-local finite-loss/domain proofs close only the explicitly frozen unnumbered consequence and its separately hypothesized domain helper; not completion of Chapter 2 or Chapters1-16. Remaining main-text source/migration audit is mandatory. No merge or live publication is implied.'
notes='The source printed9-10/PDF21-22 gives a necessary condition: finite constrained loss requires x in V. The iff is an explicit library refinement adding finite original f(x). Arbitrary carriers generalize Rd for this algebra. Ordinary bottom-dominant EReal addition is retained. Finite-real witness existence excludes both infinities; below-top effectiveDomain includes bottom. No noBottom premise on finite_add_indicator_iff; global noBottom is essential on effectiveDomain_add_indicator. Convexity/topology/nonempty V are unnecessary here. '+boundary
p='website/content/readings.json';x=load(p);r=next(r for r in x['readings'] if r['slug']=='online-convex')
card=next(s for s in r['source_theorems'] if s['label']=='Constraint indicators and adding constraints')
card['local_status']['boundary']='Named indicator/domain/convexity endpoints and the separately source-frozen finite-loss iff/domain-intersection helper have shared implementations. Membership alone does not ensure finite f. Four closure constructions retain separate migration acceptance. Chapter2 and whole-book acceptance remain incomplete.'
r['teaching_route']+=['BanditRL.OnlineConvex.finite_add_indicator_iff','BanditRL.OnlineConvex.effectiveDomain_add_indicator']
r['source_theorems'].append(dict(label='Finite constrained loss: unnumbered main-text consequence',pages='printed pp.9-10',pdf_page=22,url='https://arxiv.org/pdf/1912.13213v10',
 math=r'(\exists r\in\mathbb R:\ f(x)+\iota_V(x)=r)\iff (x\in V\ \land\ \exists s\in\mathbb R:\ f(x)=s)',
 fallback='Orabona states that finite loss after adding the constraint indicator requires prediction inside V. The shared proof refines this necessity to an exact iff: the point is feasible and the original loss is finite.',
 plain='Feasibility alone is insufficient when f(x) is infinite. Finite means equality to an embedded real number, rather than the below-top effective-domain predicate.',
 relationship=notes,
 contract=dict(model='Pointwise extended-real losses on Rd in the source; arbitrary carrier E in the shared algebraic proof.',
 assumptions='Finite iff: none on f or V. Separate effective-domain intersection equality: global f(x) != -infinity. Neither proof needs convexity, topology or nonempty V.',
 parameters='Every loss f, feasible set V and point x; either infinity and empty V are included.',
 regret='Deterministic constraint algebra for algorithm predictions and comparators, not a regret guarantee.',
 guarantee='Exact finite-real witness iff; separately, dom(f+indicator V)=dom(f) intersect V under global noBottom.'),
 local_status=dict(status='compiled',label='Finite constrained loss and domain',boundary=boundary)))
save(p,x)
p='website/content/chapters.json';x=load(p);r=next(r for r in x['chapters'] if r['slug']=='online-convex')
r['module_globs'].append('BanditRLProof/OnlineConstraintFiniteLoss.lean')
r['completion_definition']=r['completion_definition'].replace('The separate finite-loss/domain-intersection consequence remains required.','The separate finite-real criterion and noBottom domain-intersection helper have two new shared proofs, with exact source-refinement boundaries.')
r['completion_blockers']=[s for s in r['completion_blockers'] if not s.startswith('Finite constrained loss iff')]
r['completion_blockers'].append('Broader source/migration and exact Chapter2 mandatory enumeration remain pending; this bounded finite-loss package does not close the chapter.')
r['learning_goals'].append('Distinguish finite constrained loss from the below-top domain; keep noBottom on the separate domain identity.')
save(p,x)
p='website/content/highlights.json';x=load(p)
new=[dict(full_name='BanditRL.OnlineConvex.finite_add_indicator_iff',title='Finite loss requires feasibility and finite original loss',chapter='online-convex',featured=False,teaching_order=7,
 plain='The constrained value is finite exactly when the point is feasible and its original loss is finite.',
 math=r'\((\exists r\in\mathbb R:\ f(x)+\iota_V(x)=r)\iff x\in V\land(\exists s\in\mathbb R:\ f(x)=s)\)',
 intuition='At feasible points the indicator adds zero. Outside V, adding positive infinity never yields a finite real, including the negative-infinity case.',
 why='Close the unnumbered main-text finite-loss obligation used for both the prediction and comparator.',position='Orabona v10 Section2.1.1, printed9-10/PDF21-22; explicit iff refinement of the source necessary condition.',
 proof_idea='Split on x in V. Inside, f(x)+0=f(x). Outside, split f(x) into bottom, finite and top: the sums are bottom, top and top, and none equals an embedded real.',
 lean_notes=notes,dependencies=['BanditRL.OnlineConvex.extendedIndicator']),
 dict(full_name='BanditRL.OnlineConvex.effectiveDomain_add_indicator',title='Effective domain of a constrained loss',chapter='online-convex',featured=False,teaching_order=8,
 plain='Under global noBottom, the constrained effective domain is the original effective domain intersected with V.',
 math=r'\(\operatorname{dom}(f+\iota_V)=\operatorname{dom}f\cap V,\quad \forall x:\ f(x)\ne-\infty\)',
 intuition='Below top becomes a finite-value test only when bottom is excluded. Without that premise, bottom outside V leaks into the domain.',
 why='Support the constraint algebra with the exact shared effective-domain definition, while exposing its stronger hypothesis.',position='Separate algebraic helper associated with Orabona v10 printed9-10/PDF21-22; not a printed numbered theorem.',
 proof_idea='At x in V, adding zero preserves f(x)<top. Outside V, noBottom makes f(x)+top=top. Thus membership is exactly the intersection. The public constant-bottom/empty-V canary refutes dropping noBottom.',
 lean_notes=notes,dependencies=['BanditRL.OnlineConvex.effectiveDomain','BanditRL.OnlineConvex.extendedIndicator'])]
assert not set(r['full_name'] for r in new)&set(r['full_name'] for r in x['highlights'])
x['highlights']+=new;save(p,x)
for p,k,key in [('website/content/readings.json','readings','slug'),('website/content/chapters.json','chapters','slug'),('website/content/highlights.json','highlights','chapter')]:
    old=load(snap[p]['snapshot']);newx=load(p)
    assert [r for r in old[k] if r.get(key)!='online-convex']==[r for r in newx[k] if r.get(key)!='online-convex']
    for extra in set(old)-{k}:assert old[extra]==newx[extra]
save(run/'reader-integration-v1.json',dict(status='scoped-reader-data-written',two_new_shared_endpoints=True,
    only_online_convex_subtree_changed=True,prior_all_other_Book_subtrees_unchanged=True,site_build_pending=True,chapter_complete=False,goal_complete=False))
print('Only online-convex subtree updated; two new source-qualified highlights; no generated site edited.')
