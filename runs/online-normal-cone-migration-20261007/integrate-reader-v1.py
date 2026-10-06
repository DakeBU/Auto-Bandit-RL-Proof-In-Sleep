from common import *
f=fixed();r=bind_review('public-body-receipt-v2.json','public-body-inputs-v2.json','body-binding-audit-v2.json')
for row in load(RUN/'prior-contract-binding-v2.json')['rows']:assert sha(row['resolved'])==row['sha256']
snap={row['path']:row for row in load(RUN/'historical-raw-supersession-v2.json')['rows']};original=Path(snap[PUBLIC.as_posix()]['snapshot']).read_bytes();assert PUBLIC.read_bytes()==original
comment='''/-
Orabona v10 Example2.25 printed18/PDF30: ONE body example, THREE exact
normal-cone equalities and ONE complete retained owned definition.
Zero new mathematical or TEST declarations. The full feasible definition
requires x in V and every feasible displacement inner product nonpositive;
it has intrinsic real inner-product context, no finite-dimensional,
nonempty or convexity premise. All THREE theorem signatures explicitly
retain finite-dimensional real inner-product space; first TWO retain
nonempty convex V. No general closed or bounded V, relative interior,
positive dimension or extra completeness premise is introduced.
Generic shared support accepts wider EReal inputs than printed proper
functions. Nonempty V makes the zero/top constraint indicator proper.
Empty V is excluded: generic support of all-top differs from empty normals.
Actual support/properness derives query feasibility and outside emptiness.
Actual ambient interior ball and a positive displacement along nonzero g
force a contradiction; zero satisfies the full feasible inequalities.
Actual normalized nonzero g, Cauchy equality and zero squared difference
produce every closed-unit-ball boundary normal's nonnegative radial form;
zero uses scalar0 and converse covers ALL real scalars at least0.
Whole FOUR old canary proofs and TWO real2D basis definitions unchanged.
The singleton canary proves full support/7, not empty interior itself.
Two-dimensional canary includes outward2e0 and zero, excludes e1 and -e0.
Borrowed support/indicator/proper/domain APIs are shared, not owned/new.
ONE owned definition plus three retained proof refinements is reuse, not
new mathematical growth or a separate coordinate isometry certificate.
Next Theorem2.26 and all remaining Chapter1/2/appendix work required;
Chapter2 and persistent Chapters1-16 Goal remain incomplete.
-/
'''
assert comment.count('/-')==comment.count('-/')==1 and not re.search(r'\b(sorry|admit|axiom|postulate)\b',comment)
PUBLIC.write_bytes(comment.encode()+original)
write(RUN/'public-comment-qualification-v1.json',dict(path=PUBLIC.as_posix(),original_sha256=hashlib.sha256(original).hexdigest(),qualified_sha256=sha(PUBLIC),exact_original_raw_suffix=True,delta='ordinary leading source/scope comment only; full owned definition/every original mathematical byte retained'))
b=load(RUN/'public-actual-bindings-v1.json');g=load(RUN/'compiled-dependencies-v1.json')
scope='ONE printed Example2.25, THREE mandatory set equalities, THREE retained proofs and ONE full retained owned normal definition. Zero new mathematical, TEST or registry nodes. Full owned SourceNormalCone has intrinsic real inner-product classes but NO FD/nonempty/convexity premise; it explicitly includes x∈V. All THREE theorem signatures retain FD; first TWO nonempty convexV. No general closed/bounded/full-dimensionalV/CompleteSpace/positive-dimension premise.'
delta='Finite-dimensional real inner-product presentation includes the source Euclidean instances; no separately certified coordinate isometry or functor. Shared global SourceSubdifferential admits arbitrary improper EReal functions, wider than the source proper-function definition. Nonempty V makes its zero/top indicator proper. Empty V would yield every vector for generic alltop support but empty feasible normals; this theorem excludes it. Borrowed S/indicator/proper/domain APIs are shared context, not owned or new definitions.'
indicator='Nonempty V produces actual indicator properness. The shared support-domain theorem forces queried x∈V. At every feasible y, the global support inequality reduces to inner(g,y-x)≤0; outside y its upper value is top. Conversely actual feasible normality gives global support at EVERY ambient y. Exact equality holds for EVERY query and candidate vector, including outside-query emptiness.'
interior='AMBIENT interior supplies an actual metric ball around x inside V. If g≠0, choose a=r/(2‖g‖)>0 so actual y=x+ag lies in that ball; normality gives a‖g‖²≤0, contradicting positivity. Zero satisfies all inequalities and x is feasible. Ambient interior is not relative interior; no conclusion of zero normals is supplied at a thin set with empty ambient interior.'
ray='The set is the CLOSED unit ball ‖y‖≤1, query ‖x‖=1. Zero gives α=0. For g≠0 test actual y=g/‖g‖; normality and Cauchy imply inner(g,x)=‖g‖. The squared difference ‖g-‖g‖x‖²=0 produces g=‖g‖x and α=‖g‖≥0. Conversely EVERY real α≥0 satisfies ALL feasible-y inequalities by Cauchy. Whole ray equality includes zero and both directions; radiality is produced, not assumed. In zero dimension no norm1 query exists, so this boundary result is vacuous without adding d>0.'
canary='Whole FOUR unchanged existing canary proofs plus TWO noncomputable TEST basis definitions e0/e1 were freshly checked. Interval[0,1]: -1 accepted/+1 excluded at0, outside2 supportempty, interior½ support{0}. Singleton0 supportuniv and7 are proved; that canary does NOT itself prove empty ambient interior. Actual real EuclideanSpace(Fin2) unitquery e0: outward2e0/zero accepted, transversee1/inward-e0 excluded. No new tests or scalar-only substitution.'
evidence='Current exact retained public bodies and whole canary checked; TEN unique named kernel checks cover sevenproofs/ownedN/twoTESTdefs with standard foundations or none, FOUR frozen-header guards. Selected TEN compiled nodes (seven proofs/three definitions), '+str(g['direct_references'])+' direct type/value occurrences and '+str(len(g['required_value_pairs']))+' required actualproducer-canary pairs. Separate readiness FOUR nodes/'+str(load(RUN/'ready-dependencies-v1.json')['direct_references'])+' references/eightpairs retained exactly; neither is full registry graph export. Teaching route links are curated, not exhaustive proof-term dependencies.'
remaining='Only Example2.25 three source claims and its necessary definition. T2.26 and all remaining Chapter1/2 main-text/source-contract/necessary appendix obligations remain REQUIRED; nineOTHERChapter1main-relative contract gaps not waived. Chapter2mandatorytotal null/incomplete; Chapters3–16unenumerated; totalGoal ACTIVE. No algorithm/regret/probability/feedback/measurable or executable selection guarantee, merge/deploy/main/live or worktree retirement.'
def save_json(p,d,key,selector):
 old=load(snap[p]['snapshot']);assert [x for x in old[key] if not selector(x)]==[x for x in d[key] if not selector(x)],p
 for extra in set(old)-{key}:assert old[extra]==d[extra]
 Path(p).write_bytes((json.dumps(d,ensure_ascii=False,indent=2)+'\n').encode())
p='website/content/readings.json';d=load(p);x=next(a for a in d['readings'] if a['slug']==ROUTE);oldroute=list(x['teaching_route']);assert len(oldroute)==3 and len(x['notation'])==3
x['primary']['sections']='Section2.2.1, Example2.25 printed18/PDF30; ONE example, THREE mandatory equalities and ONE necessary normal definition'
x['notation'][0]['meaning']='N_V(x) explicitly contains exactly g with x∈V AND inner(g,y-x)≤0 for EVERY y∈V. Its definition has no FD/nonempty/convexity assumption; outsideV or emptyV normals are empty. '+scope
x['notation'][1]['meaning']='Zero in V and positive infinity outside V, the existing shared EReal constraint indicator. '+delta
x['notation'][2]['meaning']='Interior is AMBIENT. Closed unit ball norm≤1, boundary normx=1 and FULL real α≥0 ray includes0. No relative-interior/full-dimensional assumption; zeroD norm1 impossible. '+canary
assert len(x['source_theorems'])==3
for i,card in enumerate(x['source_theorems']):
 card['relationship']=scope+' '+delta+' '+canary
 card['contract'].update(model='Finite-dimensional real inner-product Euclidean source instance. '+delta,regret='No algorithm/regret/probability/feedback/computable or measurable vector selection claim.')
 card['local_status'].update(status='compiled',label='Exact retained source producer and whole canary checked',boundary=evidence+' Distinct CONTRACT/BODYv2 accepted; combined rootTests/fullharness/site/FINAL/PR remain separate. '+remaining)
 if i==0:card['contract'].update(assumptions='Explicit FD/nonemptyconvexV; every ambientquery x including outsideV. No query-feasibility, generalclosed/boundedV premise.',parameters='Every candidate g, EVERY ambient support test y and EVERY feasible normal test y.',guarantee='Complete indicator subdifferential equals full feasible normal set, both directions/allqueries incloutsideempty.')
 elif i==1:card['contract'].update(assumptions='Explicit FD/nonemptyconvexV, x in actual AMBIENT interiorV. No relative-interior or closedV replacement.',parameters='Every eligible interiorquery x and every candidate g.',guarantee='Entire normal set equals singletonzero, including actual membership of0.')
 else:card['contract'].update(assumptions='Explicit FD and normx=1, CLOSEDunitballnormy≤1. No assumed direction/multiplier or positive dimension.',parameters='Every unit queryx/every candidateg/realα≥0 including0; EVERY feasibley.',guarantee='FULL nonnegative radial-ray equality, produced and proved in both directions. Zero-dimensional case has no unitquery.')
x['algorithm']['steps'][0]['detail']=indicator;x['algorithm']['steps'][1]['detail']=interior;x['algorithm']['steps'][2]['detail']=ray
x['proof_bridge']['steps'][0]['detail']=indicator;x['proof_bridge']['steps'][1]['detail']=interior;x['proof_bridge']['steps'][2]['detail']=ray
x['proof_bridge']['boundary']=scope+' '+delta+' '+evidence+' '+remaining
x['worked_example']['intro']=canary;x['worked_example']['steps'][1]['detail']='For V={0} in ℝ the actual canary proves every real slope is a support, including7. The separate elementary fact that this singleton has empty ambient interior explains why the interior theorem is inapplicable; the canary does not itself prove that topological fact.'
x['worked_example']['boundary']=remaining
assert x['teaching_route']==oldroute and len(x['notation'])==3
save_json(p,d,'readings',lambda a:a.get('slug')==ROUTE)
p='website/content/highlights.json';d=load(p)
for h in d['highlights']:
 if h.get('chapter')!=ROUTE:continue
 n=h['full_name'].rsplit('.',1)[-1];h['position']='Orabona v10 Example2.25 printed18/PDF30; ONE example/THREE claims/ONE retained necessary definition in shared registry.';h['why']=scope
 if n=='SourceNormalCone':
  h['intuition']='Feasibility of the query is part of the full defining predicate; every feasible displacement is tested.'
  h['proof_idea']='This is a retained Set definition, not a proved characterization: x∈V AND ∀y∈V inner(g,y−x)≤0. It has no FD/nonempty/convexity premise.'
  h['lean_notes']='Definition scoped to any real inner-product E and anyV/x, no FD/nonempty/convexity binder. Full owned body retained; empty/outsideNempty by feasibility. THREE neighboring theorem premises are separate. '+delta+' '+remaining
 else:
  h['proof_idea']=indicator if n=='indicator_subdifferential_eq_normalCone' else (interior if n=='normalCone_interior_eq_zero' else ray)
  h['lean_notes']=scope+' '+delta+' '+canary+' '+remaining
save_json(p,d,'highlights',lambda a:a.get('chapter')==ROUTE)
p='website/content/chapters.json';d=load(p);x=next(a for a in d['chapters'] if a['slug']==ROUTE)
x.update(status='compiled',summary='Characterize full feasible normals, ambient interior zero and the entire nonnegative unit-ball boundary ray.',completion_definition=scope+' '+evidence,completion_blockers=[remaining],open_gaps=[remaining])
save_json(p,d,'chapters',lambda a:a.get('slug')==ROUTE)
paths=[PUBLIC.as_posix(),'website/content/readings.json','website/content/highlights.json','website/content/chapters.json'];names=[PRE+n for n in f['headers']]
c=load('research-wiki/contribution-contracts/online-subgradient-absolute-migration-20261007.json')
c.update(id=TASK,frontier_cell=ROUTE,target='Example2.25 complete allquery indicator support/ambientinteriorzero/fullclosed-unitballray; three retained proofs/one full owneddefinition, no newmath or TESTs.',affected_files=paths,declarations=names)
c['source']['anchor']='Example2.25 printed18/PDF30 ONE example THREE mathematicalclaims and ONE necessary fullnormaldefinition'
c['reuse_plan'].update(classification='reuse',decision='reuse_existing',searched_existing=['Actual fourpublic @types/fullownedN/borrowedS-indicator-proper-domain/exactretainedbody/whole4canaryproof2TESTdefs; pinned15 actualAPIs/localnative retrieval/current4node818refs and10node1581refs/15valuepairs.'],reused_declarations=names+[PRE+'SourceSubdifferential',PRE+'extendedIndicator',PRE+'sourceProper_indicator_iff',PRE+'subgradient_point_finite'],new_shared_declarations=[],known_consumers=load(RUN/'public-named-declarations-v1.json')['whole_canary_proofs'],planned_consumers=['Required later Chapter2 source-matched optimization/constraint uses.'],decision_reason='Reuse existing full normal definition and actual set-equality producers, no duplicate wrappers/perBook library.')
c['semantic_roundtrip'].update(status='accepted',formalizer='/root',blind_decoder='/root/neutral_geometry_decoder',source_reviewer='/root/source_reviewer',verdict=r['verdict'],remaining_semantic_delta=scope+' '+delta+' DistinctCONTRACT/BODYv2 accepted; currentFINAL stillpending. BODYv1 rejected staleappend-log resolution index only, exact snapshots preserved/v2 corrected. Three distinct required automatedactors/requested Astra medium/no humanexternal/runtimeattestation.')
c['graph_contribution'].update(lean_graph='reuse-only',overview_graph='updated',functor_hypergraph='none-found-with-reason',focus_targets=names,visual_review='Preserve all10811old sharedIDsURLs/fourcanonicalnodes includingdefinition/threeoriginalcuratedroutes/three notationentries; actual viewport/formula inspection follows applicable combinedLean gate.')
c['progress_updates'].update(teaching_route='updated: fullownedNactualsignature/proper-indicator/outsideempty/ambientinterior/fullnonnegative unitballray/whole2Dcanary actual scope.',website_surfaces=paths[1:],results_ledger='no-change-with-reason: additive scoped acceptance/actualPR overlays followfull gates; Chapter2incomplete/historicalinventory preserved.')
c['truth_boundary']=' '.join([scope,delta,indicator,interior,ray,canary,evidence,remaining])
c['verification'].update(focused_checks=[evidence],owned_test_files=[],bandit_check='Current postcomment sequential root/Tests/fullharness stillrequired.',site_build='Clean local leanverified build only after currentapplicablecombinedgate.',site_check='All10811oldIDsURLs/four canonical links incldefinition/threecuratedroutes/three notation entries/allotherBooksubtrees.',independent_review='Distinctformalizer/newrestrictedneutraldecoder/stagedsource reviewer requestedAstra medium; nohuman/external or modelruntimeattestation.')
manifest=Path('research-wiki/contribution-contracts/online-normal-cone-migration-20261007.json');write(manifest,c)
write(RUN/'reader-integration-v1.json',dict(route=ROUTE,affected_files=paths,original_three_routes_retained=oldroute,exact_three_notation_entries=True,all_other_Book_subtrees_unchanged=True,retained_proofs=3,retained_definitions=1,new_mathproofs=0,new_definitions=0,new_TESTs=0,body_review_report_sha256=r['report_sha256'],required_reader_corrections=r.get('required_reader_corrections',[]),all_nine_contract_reader_requirements_explicitly_addressed=True,publication=manifest.as_posix(),source_package_accepted=False,chapter_complete=False,goal_complete=False))
fixed(True)
for n,h in f['headers'].items():native('integrated-safe-'+n+'-v1','safe-verify','--fence',RUN/'native-public-fences'/(n+'.json'),'--lean-file',PUBLIC,'--lean-file',CANARY)
write(RUN/'integrated-public-guard-audit-v1.json',dict(status='passed',native_guards=4,all_original_module_raw_bytes_retained=True,full_ownedN_borrowedS_indicator_proper_fixed=True,headers_unchanged=True,whole_canary_shareddeps_roots_pins_fixed=True))
print('BODYv2 bound, four canonical original declarations/three curatedlinks/three notation entries; alloldmathematical bytes retained. Combined project gates pending.')
