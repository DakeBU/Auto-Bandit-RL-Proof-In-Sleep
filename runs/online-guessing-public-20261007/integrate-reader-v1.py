"""Refresh only canonical evidence within the shared already-six-card route."""
from common_v1 import *
fixed();r=load(RUN/'public-body-receipt-v1.json')
assert r['actor']['task']=='/root/source_reviewer' and r['verdict'] in ['accepted','accepted-with-explicit-delta'] and sha(r['report'])==r['report_sha256']
for k in ['required_repairs','required_mathematical_repairs','required_metadata_repairs']:assert not r.get(k,[]),k
reviewed={x['path']:x['sha256'] for x in r['reviewed_files']}
for x in load(RUN/'body-review-inputs-v1.json')['rows']:assert reviewed[x['path']]==x['sha256']==sha(x['path'])
b=load(RUN/'body-bindings-v1.json')
scope='Existing canonical Example2.32 chain: twelve public proofs and one loss definition, with the whole27canary proofs/6definitions/one abbreviation. Current source/public reuse audit; ZERO new mathematical proofs, definitions or source-terminal closures.'
evidence=f'Current focused {b["focused_jobs"]} jobs include cached jobs; all47 named kernel checks, twelve unchanged full statement guards and25 prespecified direct proof-value pairs pass ({b["direct_references"]} direct references). CONTRACT/BODY reviewed by distinct required automated actors. Current combined/reader/FINAL gates are separate.'
boundary='The complete global supporting inequality tests every real comparison point, including outside [0,1]; ties retain the entire closed[-1,1] without imposing a zero choice. Actual canonical current-function/current-point choice and nearest projection produce the strict-past trajectory. Externally selected initialization/rates remain parameters; no randomized law, finite-query execution or parameter-independence certificate. Feasible initialization and played labels/comparators, positive prescribed horizon and same eta=1/sqrt(T) path for all comparators remain explicit. Constant one is derived from D=G=1 and equation2.1. The additional eventual signed-average upper condition concerns separately tuned horizons, not signed convergence to zero, absolute Big-O or one anytime path.'
boundary+=' Finite absolute losses produce properness and nonempty global supports; the all-support norm bound applies to arbitrary real labels/queries. The canonical selected-norm declaration retains its feasible-query x in [0,1] premise. Clamp/prefix identities allow arbitrary real rates or infeasible initial points and do not imply performance there. Source-unused played-label feasibility stays in the finite theorem. T=0 is excluded from finite tuning; eventual zero-horizon exceptions are harmless. The shared sharp fixed bound retains its negative terminal distance before the coarse sqrt(T) specialization.'
remaining='Linearization/optimal-step/unit-analysis current migration, remaining Chapter1/2 maintext, nine OTHER Chapter1 origin/main contributor gaps and necessary appendix obligations remain REQUIRED. Chapter2 mandatory total is incomplete; Chapters3-16 remain unenumerated. Whole Goal ACTIVE; no chapter/book completion, merge/deploy or main/live update.'
history='Generic arbitrary played-legal finite-history support-family specialization is already separately accepted/delivered in OPEN unmerged PR182. Its four proofs/two cards and historical delivery-time evidence are preserved; they are neither missing nor counted again. Current canonical reuse adds no new registry nodes. Stacked on exact OPEN unmerged PR182 b37ad575a232532f1d5dbf68f2036e7e41944382.'
def formulas(obj):
 if isinstance(obj,dict):return [v for k,v in obj.items() if k=='math']+sum([formulas(v) for k,v in obj.items() if k!='math'],[])
 if isinstance(obj,list):return sum([formulas(v) for v in obj],[])
 return []
def save(p,d,key,pred):
 old=load(p);assert [x for x in old[key] if not pred(x)]==[x for x in d[key] if not pred(x)]
 assert {k:v for k,v in old.items() if k!=key}=={k:v for k,v in d.items() if k!=key}
 Path(p).write_bytes((json.dumps(d,ensure_ascii=False,indent=2)+'\n').encode('utf-8'))
p='website/content/readings.json';d=load(p);x=next(a for a in d['readings'] if a['slug']==ROUTE)
assert [len(x[k]) for k in ['notation','teaching_route','source_theorems']]==[3,4,6] and len(x['proof_bridge']['steps'])==5
original_formulas=formulas(x);original_policy_cards=json.dumps(x['source_theorems'][4:],sort_keys=True,ensure_ascii=False);original_curated=x['teaching_route'][:]
for card in x['source_theorems'][:4]:
 card['contract']['parameters']='Source round1 is Lean0. The fixed noncomputable canonical selector receives the current whole loss and current point; the true shared recursion outputs before reveal and clamps the actual update. The source permits any legal support; its history-policy family is separately delivered in PR182. '+boundary
 card['local_status']=dict(status='compiled',label='Existing canonical chain: current focused source/body audit',boundary=scope+' '+evidence+' '+boundary+' '+history+' '+remaining)
for key in ['proof_bridge','worked_example']:
 x[key]['boundary']=x[key]['boundary'].replace('Canonical Example2.32 current publication migration, ','')+' '+scope+' '+history+' '+remaining
assert formulas(x)==original_formulas and json.dumps(x['source_theorems'][4:],sort_keys=True,ensure_ascii=False)==original_policy_cards and x['teaching_route']==original_curated
save(p,d,'readings',lambda a:a.get('slug')==ROUTE)
p='website/content/highlights.json';d=load(p);xs=[a for a in d['highlights'] if a.get('chapter')==ROUTE];assert len(xs)==16
oldpolicy=[a.copy() for a in xs if a['full_name'].startswith('BanditRL.OnlineGuessingSubgradientPolicy.')];assert len(oldpolicy)==4
for a in xs:
 if a['full_name'].startswith(PRE):a['lean_notes']=a['lean_notes'].split(' Historical canonical evidence; current publication migration pending.')[0]+' '+scope+' '+evidence+' '+boundary+' '+history+' '+remaining
assert [a for a in xs if a['full_name'].startswith('BanditRL.OnlineGuessingSubgradientPolicy.')]==oldpolicy
save(p,d,'highlights',lambda a:a.get('chapter')==ROUTE)
p='website/content/chapters.json';d=load(p);x=next(a for a in d['chapters'] if a['slug']==ROUTE)
assert x['module_globs']==[PUBLIC.as_posix(),'BanditRLProof/OnlineGuessingSubgradientPolicy.lean']
x['summary']='Full global shifted support sets, actual canonical-choice recurrence and separately delivered played-legal finite-history policy family, with same-run all-comparator sqrt(T) regret.'
x['completion_definition']=scope+' The twelve declarations comprise shared algebraic/causal helpers, one finite guarantee and an explicit one-sided refinement of one printed Example2.32. '+history
x['completion_blockers']=[remaining,'Current canonical package combined/reader/FINAL/native acceptance and stacked draft delivery are separately verified stages; local compilation is not merge/live publication.']
x['open_gaps']=[boundary,remaining]
save(p,d,'chapters',lambda a:a.get('slug')==ROUTE)
names=[PRE+n for n in load(CONTRACT/'headers-v1.json')]
c=load('research-wiki/contribution-contracts/ONLINE-GUESSING-OSD-20261004.json')
c.update(id=TASK,target=scope,affected_files=['website/content/readings.json','website/content/highlights.json','website/content/chapters.json'],declarations=names)
c['reuse_plan'].update(classification='reuse',decision='reuse_existing',searched_existing=['Actual project/mathlib declaration rg search; complete neutral twelve types and kernel full closedProp identities under exact aliases; unchanged actual production/canary API audits.'],reused_declarations=names,new_shared_declarations=[],planned_consumers=['Separately frozen remaining linearization/optimal-step/unit-analysis and Chapter1/2/appendix obligations.'],decision_reason='Reuse exactly existing canonical absolute-loss/support/projection/causal OSD bodies. No duplicate loss, wrapper, per-book project or proof tree; generic policy terminal already separately delivered PR182.')
c['semantic_roundtrip'].update(status='accepted',formalizer='/root',blind_decoder='/root/osd_blind',source_reviewer='/root/source_reviewer',verdict=r['verdict'],remaining_semantic_delta=boundary+' '+history+' Current CONTRACT/BODY accepted; FINAL pending. Required distinct automated actors; requested Astra/medium, no human/external/runtime attestation.')
c['graph_contribution'].update(lean_graph='reuse-only',overview_graph='updated',functor_hypergraph='none-found-with-reason',functor_reason='Existing scalar absolute-loss specialization on same shared true OSD recurrence; no new independently proved transport.',focus_targets=names,visual_review='Actual selected47 nodes39proofs8definitions including one abbreviation; twelve exact native hashes in one shared10821 registry, ZERO new nodes. Six preserved cards/16notes/four curated links; actual pixels separate.')
c['progress_updates'].update(teaching_route='updated: canonical current source/public reuse evidence; generic policy family remains separately delivered PR182',results_ledger='no-change-with-reason: additive own accepted source overlay after FINAL, old inventory snapshot immutable; zero new mathematical closures',roadmap='no-change-with-reason: whole Goal active, remaining linearization/optimal-step/unitanalysis/Chapter1/2/appendices required;3-16 unenumerated',website_surfaces=c['affected_files'])
c['truth_boundary']=scope+' '+evidence+' '+boundary+' '+history+' '+remaining
c['verification'].update(focused_checks=[evidence],bandit_check='Actual current root/Tests/full harness required after these scoped reader changes.',site_build='Actual clean local Lean-verified site only after current applicable combined gate.',site_check='Same10821 shared IDs/URLs/12native hashes, sixcards16notesfourcuratedlinks and actualpixels required.',independent_review='Distinct reused blind decoder and source CONTRACT/BODY accepted; FINAL pending. No human/external/runtime attestation.',owned_test_files=[],owned_test_root_files=[])
write('research-wiki/contribution-contracts/online-guessing-public-20261007.json',c)
write(RUN/'reader-integration-v1.json',dict(route=ROUTE,new_proofs=0,new_definitions=0,new_registry_nodes=0,all_other_Book_subtrees_unchanged=True,all_formula_strings_unchanged=True,PR182_policy_four_notes_two_cards_unchanged=True,curated_names_unchanged=True,source_cards=6,library_notes=16,curated_links=4,notation_entries=3,proofbridge_steps=5,source_package_accepted=False,chapter_complete=False,goal_complete=False))
fixed(True);print('Only canonical12 notes/four oldcards/current canonical prose refreshed; newpolicy4notes2cards/formulas/otherBooks preserved. Combined/FINAL pending.')
