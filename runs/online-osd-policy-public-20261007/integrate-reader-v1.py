"""Scoped current source mapping after distinct BODY; immutable proof reuse only."""
from common_v1 import *
fixed();passed('prepare-body-evidence-v1-01')
r=load(RUN/'public-body-receipt-v1.json')
assert r['actor']['task']=='/root/source_reviewer' and r['verdict'] in ['accepted','accepted-with-explicit-delta']
assert sha(r['report'])==r['report_sha256']
for k in ['required_mathematical_repairs','mathematical_repairs','required_metadata_repairs']:assert not r.get(k,[]),k
reviewed={x['path']:x['sha256'] for x in r['reviewed_files']}
for x in load(RUN/'public-body-inputs-v1.json')['rows']:assert reviewed[x['path']]==x['sha256']==sha(x['path']),x['path']
b=load(RUN/'public-actual-bindings-v1.json');g=load(RUN/'compiled-dependencies-v1.json')
scope='Existing finite-history projected OSD policy chain, current source/public reuse audit:21 public proofs/7 definitions/2 abbreviations; zero new mathematical proofs or definitions.'
evidence=f'Current focused {b["focused_jobs"]} jobs include cached jobs; all122 named kernel checks and21 frozen statement guards pass. Actual selected122 production/canary nodes:95 proofs,27 definitions including9 abbreviations, {g["direct_references"]} direct references and32 required value pairs. Current combined/reader/FINAL gates are separate.'
remaining='Example2.32, linearization, unit analysis, remaining Chapter1/2 maintext, nine OTHERChapter1 main-relative contribution gaps and necessary appendices remain REQUIRED. Chapter2 mandatory total is incomplete; Chapters3-16 remain unenumerated. Whole Goal ACTIVE; no chapter/book completion, merge/deploy or main/live update.'
history='Historical PR149 already accepted this chain; current migration creates no new source obligation closure. Exact stacked PR179 base remains OPEN draft and unmerged.'
reader_boundary='Fixed exogenous deterministic p sees finite whole-loss/output history and current whole loss; only played legality is required. Prefix compares the same p/x1. Noncomputable whole-function choices/projection do not establish randomized laws, external-parameter independence, an executable oracle or anytime tuning. Source round1 is Lean0; output(T) is source x_(T+1). '+history+' '+remaining
def save(p,d,key,pred):
 old=load(p);assert [x for x in old[key] if not pred(x)]==[x for x in d[key] if not pred(x)]
 assert {k:v for k,v in old.items() if k!=key}=={k:v for k,v in d.items() if k!=key}
 Path(p).write_bytes((json.dumps(d,ensure_ascii=False,indent=2)+'\n').encode('utf-8'))
p='website/content/readings.json';d=load(p);x=next(a for a in d['readings'] if a['slug']==ROUTE)
assert [len(x[k]) for k in ['notation','teaching_route','source_theorems']]==[3,4,4] and len(x['proof_bridge']['steps'])==4
before_formulas=[]
def formulas(obj):
 if isinstance(obj,dict):
  for k,v in obj.items():
   if k=='math':before_formulas.append(v)
   else:formulas(v)
 elif isinstance(obj,list):
  for v in obj:formulas(v)
formulas(x);original_formulas=before_formulas[:]
card=x['source_theorems'][0]
card['pages']='Lemma2.31 printed19/PDF31; Algorithm2.2 printed20/PDF32'
card['contract']['parameters']='Fixed p, loss sequence f and initialization x1; arbitrary current t, positive eta(t), actual selected gt and actual next nearest projection. Only u must be feasible in this single-step statement; no initial/current feasibility hypothesis.'
card['contract']['regret']='Single finite real loss difference f_t(X_t)-f_t(u), multiplied by the current eta(t); no horizon sum in this lemma.'
for card in x['source_theorems']:
 card['local_status']=dict(status='compiled',label='Existing policy chain: current focused audit',boundary=scope+' '+evidence+' '+reader_boundary)
x['proof_bridge']['boundary']=reader_boundary
x['worked_example']['boundary']=reader_boundary
before_formulas=[];formulas(x);assert before_formulas==original_formulas
save(p,d,'readings',lambda a:a.get('slug')==ROUTE)
p='website/content/highlights.json';d=load(p);xs=[a for a in d['highlights'] if a.get('chapter')==ROUTE];assert len(xs)==21
for a in xs:a['lean_notes']+=' '+scope+' '+evidence+' '+history+' '+remaining
save(p,d,'highlights',lambda a:a.get('chapter')==ROUTE)
p='website/content/chapters.json';d=load(p);x=next(a for a in d['chapters'] if a['slug']==ROUTE);assert x['module_globs']==[PUBLIC.as_posix()]
x.update(completion_definition=scope+' Genuine finite-history recursion, same-path sharp fixed/variable/tuned/coarse terminals and exact canonical bridges. Four source performance cards;21 library notes are not21 printed book theorems.',completion_blockers=[remaining,history],open_gaps=['Randomized adaptive laws/measurability remain separate from fixed-policy prefix equality.','Whole-function noncomputable selection/projection does not establish an executable finite-query oracle.','External initialization/policy/rate independence and anytime tuning are not certified.',remaining])
save(p,d,'chapters',lambda a:a.get('slug')==ROUTE)
names=[PRE+n for n in load(CONTRACT/'headers-v1.json')]
c=load('research-wiki/contribution-contracts/ONLINE-OSD-PUBLIC-20261007.json')
c.update(id=TASK,frontier_cell=ROUTE,target=scope,affected_files=['website/content/readings.json','website/content/highlights.json','website/content/chapters.json'],declarations=names)
c['source']['anchor']='Definition2.18/2.20 printed16/PDF28; Lemma2.31 printed19/PDF31; Algorithm2.2 printed20/PDF32; explicit Theorem2.13/eq2.1 subgradient transfer printed19 and coarse fixed formula printed21/PDF33.'
c['reuse_plan'].update(classification='reuse',decision='reuse_existing',searched_existing=['Actual21 complete public types/11 shared API checks, scoped native index and retrieval, nine neutral dependency types AND values and21 closed compiled type comparisons under their explicit map.'],reused_declarations=names,new_shared_declarations=[],known_consumers=['OSDPolicyProbe.history_changes_actual_support','OSDPolicyProbe.offPath_actual_fixed','OSDPolicyProbe.offPath_tuned_all_comparators','OSDPolicyProbe.harmonic_actual_variable','OSDPolicyProbe.invalid_future_causal','OSDPolicyProbe.zero_horizon_actual_fixed'],planned_consumers=['Remaining source Example2.32 and linearization/unit-analysis packages, separately frozen and gated.'],decision_reason='Reuse the accepted actual finite-history producer; no duplicate wrappers, proofs or per-book project.')
c['semantic_roundtrip'].update(status='accepted',formalizer='/root',blind_decoder='/root/osd_blind',source_reviewer='/root/source_reviewer',verdict=r['verdict'],remaining_semantic_delta=reader_boundary+' Current CONTRACT/BODY accepted; FINAL pending. Distinct required automated actors; requested Astra/medium, no human/external/runtime attestation.')
c['graph_contribution'].update(lean_graph='reuse-only',overview_graph='updated',functor_hypergraph='none-found-with-reason',functor_reason='Existing finite-history support-policy producer interface and canonical bridges; no separately proved new transport.',focus_targets=names,visual_review='Actual122 selected existing nodes,95 proofs/27 definitions including9 abbreviations. Same shared registry must retain all10817 IDsURLs, zero new nodes; four genuine source performance cards/21 library notes/four curated links.',edge_semantics='formal-solid; overlays-dashed')
c['progress_updates'].update(teaching_route='updated: current source/public evidence for existing finite-history OSD, zero new proofs',results_ledger='no-change-with-reason: additive own acceptance overlay after FINAL; frozen maintext inventory unchanged',roadmap='no-change-with-reason: whole Goal ACTIVE; remaining Example2.32/linearization/unitanalysis/maintext/appendix work required',website_surfaces=c['affected_files'])
c['truth_boundary']=scope+' '+evidence+' '+reader_boundary
c['verification'].update(focused_checks=[evidence],bandit_check='Current combined root/Tests/full harness required after these reader changes.',site_build='Current clean local Lean-verified site only after real combined gates.',site_check='All10817 shared IDsURLs/21 native hashes; four source cards/21 highlights/four curated links, actual pixels required.',independent_review='Distinct neutral decoder and source CONTRACT/BODY accepted; FINAL pending. No independent human/runtime attestation.',owned_test_files=[],owned_test_root_files=[])
write('research-wiki/contribution-contracts/online-osd-policy-public-20261007.json',c)
write(RUN/'reader-integration-v1.json',dict(route=ROUTE,retained_public_proofs=21,retained_public_definitions=7,retained_public_abbreviations=2,retained_canary_proofs=74,retained_canary_definitions=11,retained_canary_abbreviations=7,new_proofs=0,new_definitions=0,new_registry_nodes=0,source_cards=4,library_notes=21,curated_links=4,notation_entries=3,proofbridge_steps=4,one_step_single_difference_metadata_repair=True,formula_strings_all_unchanged=True,all_other_Book_subtrees_unchanged=True,source_package_accepted=False,chapter_complete=False,goal_complete=False))
event('candidate',dict(existing_terminal=PRE+'regret_tuned',BODY_review=(RUN/'public-body-receipt-v1.json').as_posix(),new_proofs=0,combined_site_FINAL_pending=True))
fixed(True);print('Only existing policy route refreshed; single-step wording repaired, formulas/targets unchanged; combined/FINAL pending.')
