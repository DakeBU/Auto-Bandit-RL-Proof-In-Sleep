"""Refresh the existing route after current distinct BODY, keeping shared proofs frozen."""
from common_v2 import *
fixed();r=load(RUN/'public-body-receipt-v2.json')
assert r['actor']['task']=='/root/source_reviewer' and r['verdict'] in ['accepted','accepted-with-explicit-delta'] and sha(r['report'])==r['report_sha256']
for k in ['required_mathematical_repairs','mathematical_repairs','required_metadata_repairs']:assert not r.get(k,[]),k
reviewed={x['path']:x['sha256'] for x in r['reviewed_files']}
for x in load(RUN/'public-body-inputs-v2.json')['rows']:assert reviewed[x['path']]==x['sha256']==sha(x['path']),x['path']
b=load(RUN/'public-actual-bindings-v1.json');g=load(RUN/'compiled-dependencies-v1.json')
scope='Existing canonical projected OSD producer chain, source-facing reuse audit;15 public proofs/5 definitions/1 abbreviation, ZERO new proofs or definitions.'
evidence=f'Current focused {b["focused_jobs"]} jobs include cached jobs;53 named standard-kernel audits and15 unchanged native guards pass. Actual selected53 production/canary nodes (39 proofs,14 definitions including2 abbreviations), {g["direct_references"]} direct references and24 required value pairs. These are existing proofs, not new theorem-count productivity. Current combined/reader/FINAL gates are separate.'
remaining='One permitted noncomputable current-function/point choice only; generic deterministic legal finite-history support-policy family remains separately REQUIRED, as do Example2.32, linearization, unit analysis, remaining Chapter1/2 maintext, nine OTHERChapter1 main-relative contributor gaps and necessary appendices. Chapter2 mandatory total incomplete; chapters3-16 unenumerated. Whole Goal ACTIVE, no Chapter2/book completion or merge/deploy/main/live update.'
repair='Original raw-header truncation, missing renderer module, rejected neutral FD context and failed independently named recursion comparison retained. Full raw/native15 headers unchanged; neutral context2,6 compiled dependency type/value comparisons and15 complete target types under an audited dependency renaming, distinct CONTRACT2/BODY2 reviews pass. No retroactive claim that these proofs were authored after this draft.'
historical='Historical PR147 accepted canonical chain remains an unmerged package with its own receipts. Current exact PR178 stacked base is unmerged; this migration does not claim main acceptance.'
tex=[]
def normalize(node,path):
 if isinstance(node,dict):
  for k,v in node.items():
   if k=='math' and isinstance(v,str) and '\\\\' in v:
    node[k]=v.replace('\\\\','\\');tex.append(dict(path=path+'.math',before=v,after=node[k],change='TeX escaping only, same formula'))
   else:normalize(v,path+'.'+k)
 elif isinstance(node,list):
  for i,v in enumerate(node):normalize(v,path+'.'+str(i))
def save(p,d,key,pred):
 old=load(p);assert [x for x in old[key] if not pred(x)]==[x for x in d[key] if not pred(x)]
 assert {k:v for k,v in old.items() if k!=key}=={k:v for k,v in d.items() if k!=key}
 Path(p).write_bytes((json.dumps(d,ensure_ascii=False,indent=2)+'\n').encode())
p='website/content/readings.json';d=load(p);x=next(a for a in d['readings'] if a['slug']==ROUTE)
assert len(x['source_theorems'])==6 and len(x['notation'])==3 and len(x['teaching_route'])==4 and len(x['proof_bridge']['steps'])==4
normalize(x,'readings.online-osd')
for card in x['source_theorems']:
 card['local_status']=dict(status='compiled',label='Existing canonical OSD: current focused audit',boundary=' '.join([scope,evidence,repair,historical,remaining]))
x['source_theorems'][0]['contract']['parameters']='Arbitrary ambient current x and any actual global g at x; only comparator u must belong to V. Same supplied g enters the actual nearest projection. No chosen algorithm trajectory is an input to the standalone lemma.'
x['proof_bridge']['boundary']=' '.join([scope,evidence,repair,historical,remaining])
x['worked_example']['boundary']=remaining
save(p,d,'readings',lambda a:a.get('slug')==ROUTE)
p='website/content/highlights.json';d=load(p);xs=[a for a in d['highlights'] if a.get('chapter')==ROUTE];assert len(xs)==15
for x in xs:
 normalize(x,'highlights.'+x['full_name']);x['lean_notes']+=' '+scope+' '+evidence+' '+repair+' '+remaining
save(p,d,'highlights',lambda a:a.get('chapter')==ROUTE)
p='website/content/chapters.json';d=load(p);x=next(a for a in d['chapters'] if a['slug']==ROUTE)
assert x['module_globs']==[PUBLIC.as_posix()]
x.update(completion_definition=scope+' Exact arbitrary-current Lemma2.31, one canonical Algorithm2.2 recurrence and same-run fixed/variable residual, tuned and coarse bounds; structural helpers are not fifteen printed theorems.',completion_blockers=[remaining,historical],open_gaps=[remaining,'Whole-function noncomputable selection is not an executable finite-query oracle or a randomized/measurable law.','Initial point/schedule are exogenous; no future-independent initialization or anytime guarantee.'])
save(p,d,'chapters',lambda a:a.get('slug')==ROUTE)
write(RUN/'reader-TeX-escaping-repair-v1.json',dict(rows=tex,changes_only_on_owned_route=True,source_formulas_unchanged=True,actual_pixels_and_source_reviewer_FINAL_pending=True))
names=[PRE+n for n in load(CONTRACT/'headers-v2.json')]
c=load('research-wiki/contribution-contracts/online-convex-uncountability-20261007.json')
c.update(id=TASK,frontier_cell=ROUTE,target=scope,affected_files=['website/content/readings.json','website/content/highlights.json','website/content/chapters.json'],declarations=names)
c['source']['anchor']='Definition2.20 printed16/PDF28; Lemma2.31 printed19/PDF31, Algorithm2.2 printed20/PDF32, printed19 Theorem2.13/eq2.1 transfer and printed21/PDF33 coarse fixed formula; v10 21June2026'
c['reuse_plan'].update(classification='reuse',decision='reuse_existing',searched_existing=['Actual all15 complete public types and8 shared API checks, scoped native index/retrieval/weapon searches, six neutral dependency values and15 compiled type comparisons under explicit renaming.'],reused_declarations=names,new_shared_declarations=[],known_consumers=['OSDOutsideProbe.arbitrary_current_and_actual_clipping','OSDAlgorithmProbe.fixed_bound_with_terminal','OSDAlgorithmProbe.variable_bound_with_terminal','OSDAlgorithmProbe.tuned_all_comparators','OSDAlgorithmProbe.future_inputs_do_not_change_output'],planned_consumers=['Generic finite-history policy package (separate mandatory gate)'],decision_reason='Existing real support/projection producer chain matches this canonical instantiation. Keep full proof bytes instead of new duplicate wrappers. No new declaration-count productivity.')
c['semantic_roundtrip'].update(status='accepted',formalizer='/root',blind_decoder='/root/osd_blind',source_reviewer='/root/source_reviewer',verdict=r['verdict'],remaining_semantic_delta='Canonical choice only, generic policy REQUIRED. '+remaining+' Distinct required automated actors requested Astra medium; no human/external/runtime attestation. Current CONTRACT/BODY accepted, FINAL pending.')
c['graph_contribution'].update(lean_graph='reuse',overview_graph='updated',functor_hypergraph='none-found-with-reason',functor_reason='Existing projected-support recursion instantiation; no separately proved new cross-setting functor.',focus_targets=names,visual_review='Selected53 actual existing nodes,39 proofs/14definitions including2abbr; full registry must preserve all10817 canonical IDs/URLs, with zero added nodes. Six current source cards,15 highlights/four curated links, three notes/four bridge steps; source qualified same shared Book graph.')
c['progress_updates'].update(teaching_route='updated current evidence for existing canonical chain, no new proofs or chapter completion',results_ledger='additive own accepted overlay after remaining gates only',roadmap='total Goal ACTIVE; generic policy/Example2.32/linearization/unitanalysis/remaining chapters REQUIRED',website_surfaces=c['affected_files'])
c['truth_boundary']=' '.join([scope,evidence,repair,historical,remaining])
c['verification'].update(focused_checks=[evidence],owned_test_files=[],owned_test_root_files=[],bandit_check='Fresh combined root/Tests/full harness required, existing public/canary sources frozen.',site_build='Current clean local Lean-verified build only after actual combined gates.',site_check='All10817 existing shared IDsURLs and15 unchanged native statement hashes preserved; zero new nodes. Six cards,15 highlight/four curated links,3 notes/4 bridge steps.',independent_review='Distinct neutral2 decoder, source CONTRACT2/BODY2, separate metadata repairs; FINAL pending. No independent human/runtime attestation.')
write('research-wiki/contribution-contracts/online-osd-public-20261007.json',c)
write(RUN/'reader-integration-v1.json',dict(route=ROUTE,retained_public_proofs=15,retained_public_definitions=5,retained_public_abbreviations=1,retained_canary_proofs=24,retained_canary_definitions=7,retained_canary_abbreviations=1,new_public_proofs=0,new_definitions=0,new_canary_proofs=0,new_registry_nodes=0,source_cards=6,highlight_links=15,curated_links=4,notation_entries=3,proofbridge_steps=4,all_other_Book_subtrees_unchanged=True,root_Tests_public_canary_old_contracts_unchanged=True,source_package_accepted=False,chapter_complete=False,goal_complete=False))
event('candidate',dict(existing_terminal=PRE+'regret_tuned',BODY_review=(RUN/'public-body-receipt-v2.json').as_posix(),new_proofs=0,combined_and_site_gates_pending=True))
fixed(True);print('Existing canonical chain reader/source mapping refreshed; zero new proofs/registry nodes, combined/FINAL pending.')
