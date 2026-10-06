from common import *
r=bind_review('public-body-receipt-v1.json','public-body-inputs-v1.json','body-binding-audit-v1.json');f=fixed()
snap={row['path']:row for row in load(RUN/'historical-raw-supersession-v1.json')['rows']}
original=Path(snap[PUBLIC.as_posix()]['snapshot']).read_bytes();assert PUBLIC.read_bytes()==original
comment='''/-
Orabona v10 Example 2.24 printed18/PDF30: ONE body example, THREE cases,
four retained scalar proof refinements, zero new mathematical declarations.
The fixed function y -> |y| is finite and proper everywhere on REAL.
The generic shared supporting predicate accepts wider EReal inputs, but this
source specialization has no improper-function or infinity arithmetic issue.
Every slope is tested at EVERY ambient real y. Necessity and sufficiency give
exact sets: {1} at positive x, FULL CLOSED [-1,1] at zero, {-1} at negative x.
At zero tests +/-1 force both bounds; sign-correct multiplication proves all
interval slopes globally support. Nonzero tests0,2*x and x!=0 give unique
slopes, with y<=|y| and -y<=|y| proving global sufficiency.
All four actual signatures are scalar real, without E/finite-dimensional
binders or added convexity, differentiability, domain or support assumptions.
Full all-x terminal directly invokes all three equalities, including zero.
Whole three old canary proofs retain endpoints, 1/2, exclusion2, no singleton,
and genuine invocation of the full source terminal at2,-2,0.
Borrowed SourceSubdifferential is shared context, not a new owned definition.
No multidimensional norm, algorithm, regret or selection procedure is claimed.
Next Example2.25 and all remaining Chapter1/2/book obligations stay required.
-/
'''
assert not re.search(r'\b(sorry|admit|axiom|postulate)\b',comment)
PUBLIC.write_bytes(comment.encode('utf-8')+original)
write(RUN/'public-comment-qualification-v1.json',dict(path=PUBLIC.as_posix(),original_sha256=hashlib.sha256(original).hexdigest(),qualified_sha256=sha(PUBLIC),exact_original_raw_suffix=True,delta='ordinary leading source/scope comment only; all old mathematical bytes retained'))
b=load(RUN/'public-actual-bindings-v1.json');g=load(RUN/'compiled-dependencies-v1.json')
scope='ONE printed Example2.24, THREE cases, four retained proof refinements and zero production definitions/new mathematical or TEST declarations. All four actual signatures specialize to scalar ℝ; no E/finite-dimensional/completeness binder or added convexity/differentiability/domain/support premise.'
delta='The shared global SourceSubdifferential predicate permits arbitrary EReal functions, wider than the printed proper-function definition. Here y↦|y| is finite and proper at EVERY real y, and its real EReal embedding preserves addition and order. The complete support definition is borrowed shared context, not a new owned declaration.'
zero='At zero, tests y=1,-1 give -1≤g≤1. Conversely, any g in the FULL CLOSED interval globally supports: multiply the upper bound when y≥0 and the lower bound with reversed order when y<0. Both endpoints and every interior slope remain; choosing only0 or asserting existence is weaker.'
nonzero='At nonzero x, actual tests y=0 and y=2x give x(g-1)=0 for positive x or x(g+1)=0 for negative x. The strict sign guarantees x≠0 for cancellation. The inequalities y≤|y| and -y≤|y| prove sufficiency at EVERY real y.'
can='Whole three existing canary proofs were freshly checked: endpoints -1/1, fractional1/2 and exclusion2 at zero; impossibility of ANY singleton answer; full all-query source terminal instantiated at2,-2,0. Zero new TEST declarations.'
evidence='Current exact retained bodies/whole canary compile; seven unique named kernel checks use standard foundations or none, four frozen-header guards pass. Selected compiled graph has seven proof nodes/zero definitions/'+str(g['direct_references'])+' direct type/value occurrences, including actual source-to-branches and canary-to-source edges. Four-node/'+str(load(RUN/'ready-dependencies-v1.json')['direct_references'])+' readiness is separate and retained exactly; neither is a full registry graph export.'
remaining='Only scalar Example2.24. Example2.25 normal cones and all remaining Chapter1/2 main-text/source-contract/necessary appendix obligations stay REQUIRED. Chapter2 mandatorytotal is null/incomplete; Chapters3–16 unenumerated and whole Goal ACTIVE. No multidimensional norm, algorithm/probability/regret/selection guarantee, merge/deploy/main/live update.'
p=Path('website/content/readings.json');d=load(p);x=next(a for a in d['readings'] if a['slug']==ROUTE);oldroute=list(x['teaching_route']);assert len(oldroute)==4 and len(x['notation'])==3
x['primary']['sections']='Section2.2.1, Example2.24, printed18/PDF30; ONE example and THREE exhaustive sign cases'
x['notation'][0]['meaning']+=' '+scope
x['notation'][1]['meaning']+=' '+zero
x['notation'][2]['meaning']+=' '+delta
assert len(x['source_theorems'])==1
card=x['source_theorems'][0];card['relationship']=scope+' '+delta+' '+can
card['contract'].update(model='Scalar real absolute value and global support at every real test point. '+delta,assumptions='None for the allx terminal. Positive/negative leaves have only their strict sign hypothesis; zero leaf has no supplied slope/support premise.',parameters='Every real query x and every real candidate slope g; the support definition quantifies every ambient real y.',guarantee='Complete three-case set equality, including the full CLOSED [-1,1] at zero.',regret='No algorithm/probability/feedback/regret or measurable/computable selection guarantee.')
card['local_status'].update(status='compiled',label='Exact retained source terminal and whole canary checked',boundary=evidence+' Distinct CONTRACT/BODY source reviews accepted; current combined rootTests/fullharness/site/FINAL/PR remain separate gates. '+remaining)
x['algorithm']['steps'][0]['detail']=nonzero+' '+zero
x['algorithm']['steps'][1]['detail']='Prove both directions with every global test y. '+zero+' '+nonzero
x['algorithm']['steps'][2]['detail']='The exact allx terminal dispatches the three proved equalities, deriving x<0 in the final else. No support inequality is assumed as a consumer premise.'
x['proof_bridge']['steps'][0]['detail']=nonzero
x['proof_bridge']['steps'][1]['detail']=zero
x['proof_bridge']['boundary']=delta+' '+scope+' '+evidence+' '+remaining
x['worked_example']['intro']=can
x['worked_example']['boundary']=remaining
assert x['teaching_route']==oldroute and len(x['notation'])==3
write(p,d,True)
p=Path('website/content/highlights.json');d=load(p)
for h in d['highlights']:
 if h.get('chapter')!=ROUTE:continue
 h['position']='Orabona v10 Example2.24, printed18/PDF30; ONE body example, three sign cases, shared canonical declaration registry.'
 h['why']=scope;h['lean_notes']=delta+' '+scope+' '+remaining
 n=h['full_name'].rsplit('.',1)[-1]
 h['proof_idea']=zero if n=='abs_subgradient_zero' else (nonzero if n in ['abs_subgradient_positive','abs_subgradient_negative'] else 'Dispatch all three exact sign equalities; zero has the full interval, final else derives negativity. '+zero+' '+nonzero)
write(p,d,True)
p=Path('website/content/chapters.json');d=load(p);x=next(a for a in d['chapters'] if a['slug']==ROUTE)
x.update(status='compiled',summary='Characterize every global real support slope; retain the full closed zero interval.',completion_definition=scope+' '+evidence,completion_blockers=[remaining],open_gaps=[remaining])
write(p,d,True)
for p,k,key in [('website/content/readings.json','readings','slug'),('website/content/chapters.json','chapters','slug'),('website/content/highlights.json','highlights','chapter')]:
 old=load(snap[p]['snapshot']);new=load(p)
 assert [a for a in old[k] if a.get(key)!=ROUTE]==[a for a in new[k] if a.get(key)!=ROUTE],p
 for extra in set(old)-{k}:assert old[extra]==new[extra]
paths=[PUBLIC.as_posix(),'website/content/readings.json','website/content/highlights.json','website/content/chapters.json'];names=load(RUN/'public-named-declarations-v1.json')['public_proofs']
c=load('research-wiki/contribution-contracts/online-subgradient-sum-migration-20261007.json')
c.update(id=TASK,frontier_cell=ROUTE,target='Example2.24 allrealquery/full threecase set equality; four retained scalar proof refinements, no new mathematical or TEST declarations.',affected_files=paths,declarations=names)
c['source']['anchor']='Example2.24 printed18/PDF30, ONE body example and THREE mandatory sign cases'
c['reuse_plan'].update(classification='reuse',decision='reuse_existing',searched_existing=['Actual four public @types/full borrowedS/exact retained body/whole threecanary proofs; pinned eleven scalar abs/EReal/order APIs; native local search and compiled selected graph.'],reused_declarations=names+[PRE+'SourceSubdifferential'],new_shared_declarations=[],known_consumers=load(RUN/'public-named-declarations-v1.json')['whole_canary_proofs'],planned_consumers=['Required later Chapter2 subgradient/linearization source-matched use.'],decision_reason='Reuse complete global support producers and full allx terminal, no duplicate wrappers or perBook library.')
c['semantic_roundtrip'].update(status='accepted',blind_decoder='/root/differentiability_blind',source_reviewer='/root/source_reviewer',verdict=r['verdict'],remaining_semantic_delta=delta+' '+scope+' Distinct CONTRACT/BODY accepted; current package FINAL pending. Three distinct automated actors/requested Astra medium/honest prior history/no humanexternal/runtime model attestation.')
c['graph_contribution'].update(lean_graph='reuse-only',overview_graph='updated',functor_hypergraph='none-found-with-reason',focus_targets=names,visual_review='Preserve all10811 existing shared IDs/URLs and original four curated route links; four canonical module links, zero new mathematical nodes; actual firstviewport inspection follows clean applicable Lean gate.')
c['progress_updates'].update(teaching_route='updated: exact full zero interval/sign cancellation/allambient support/source-vs-genericS/three original notation entries/four originallinks.',website_surfaces=paths[1:],results_ledger='no-change-with-reason: additive scoped package overlay follows full gates/realPR; historical inventory and Chapter2 incomplete boundary preserved.')
c['truth_boundary']=' '.join([scope,delta,zero,nonzero,can,evidence,remaining])
c['verification'].update(focused_checks=[evidence],owned_test_files=[],bandit_check='Current postcomment sequential root/Tests/full harness still required.',site_build='Clean local leanverified build only after current applicable combined gate.',site_check='All10811oldIDsURLs/four canonical links and four curatedlinks/three notation entries; allotherBooksubtrees preserved.',independent_review='Three distinct required automated semantic actors/requested Astra medium; no humanexternal review or attested runtime model.')
manifest=Path('research-wiki/contribution-contracts/online-subgradient-absolute-migration-20261007.json');write(manifest,c)
write(RUN/'reader-integration-v1.json',dict(route=ROUTE,affected_files=paths,original_four_routes_retained=oldroute,exact_three_notation_entries=True,all_other_Book_subtrees_unchanged=True,retained_proofs=4,new_mathproofs=0,new_TESTs=0,body_review_report_sha256=r['report_sha256'],required_reader_corrections=r.get('required_reader_corrections',[]),publication=manifest.as_posix(),source_package_accepted=False,chapter_complete=False,goal_complete=False))
fixed(True)
for n,h in f['headers'].items():
 native('integrated-safe-'+n+'-v1','safe-verify','--fence',RUN/'native-public-fences'/(n+'.json'),'--lean-file',PUBLIC,'--lean-file',CANARY)
write(RUN/'integrated-public-guard-audit-v1.json',dict(status='passed',native_guards=4,all_original_module_raw_bytes_retained=True,headers_unchanged=True,whole_canary_shareddeps_roots_pins_fixed=True,borrowedS_unchanged=True))
print('Distinct BODY bound; leading comment only/four exact source links/original3notation4routes; all math bytes fixed. Postcomment project gates pending.')
