from common_v1 import *
fixed(proving=True)
body=load(RUN/'public-body-receipt-v1.json');bindings=load(RUN/'body-bindings-v1.json')
assert body['actor']['task']=='/root/source_reviewer' and body['verdict'] in ['accepted','accepted-with-explicit-delta'] and sha(body['report'])==body['report_sha256']
for k in ['required_repairs','required_mathematical_repairs','required_metadata_repairs']:assert not body.get(k,[]),k
assert body['required_reader_corrections']==load(RUN/'source-contract-receipt-v1.json')['required_reader_corrections']
reviewed={x['path']:x['sha256'] for x in body['reviewed_files']}
for x in load(RUN/'body-review-inputs-v1.json')['rows']:assert reviewed[x['path']]==x['sha256']==sha(x['path']),x['path']
assert sha(PUBLIC)==bindings['public_sha256'] and sha(CANARY)==bindings['canary_sha256']
Path('Tests.lean').write_bytes(Path('Tests.lean').read_bytes()+b'\nimport Tests.OnlineLearningFTLSharpCanary\n')
scope='Two new unnumbered source bounds in the proof of Theorem 1.3 (printed p.5 / PDF p.17); the existing logarithmic theorem and five prior proofs are retained. Six named tests validate boundaries and causality; they are not six additional book results.'
model='Deterministic scalar squared-loss guessing. The predictor uses exactly the targets already observed: first prediction 1/2, then their empirical mean. Empty-prefix mean0 is bookkeeping and differs from the first prediction.'
initial_assumptions='Only the first target belongs to [0,1]. Future targets are unrestricted.'
refined_assumptions='Positive horizon T; every target in its finite prefix belongs to [0,1]. There is no probability or global future-boundedness premise.'
index='Source rounds1..T are Lean indices0..T-1. The tail range(T-1) has real denominators t+2>0 and is empty at T=1.'
comparison='The final empirical mean is proved feasible and globally minimizing, so its loss is the source best-fixed minimum over [0,1]. Prefix leaders are produced for Be-the-Leader; hindsight leaders are auxiliary, while predictions use the strict past.'
tests='The initial loss difference equals1/4 at targets0 and1, and0 at1/2. Target2 gives9/4 and lies outside the theorem domain. For targets0,1 the actual two-round regret is3/4 while the displayed bound is9/4. Changing the current unseen target leaves the prefix prediction unchanged.'
remaining='Chapter 1 remains open: general initial predictions, a recursive mean/count implementation, W/V action-domain mapping, and the logarithmic lower-bound/source-claim audit are required. Its16 reviewed source items are not a known proof-leaf total. Chapter2 is incomplete; Chapters3–16 remain unenumerated, with necessary appendices required. The whole Goal is active.'
gates=f'Current focused builds,15 named kernel/axiom checks,13 exact proposition identities/full fences and9 prespecified VALUE dependencies passed ({bindings["direct_references"]} selected direct references). Distinct decoder/CONTRACT/BODY reviews passed with stated deltas; combined/reader/FINAL/publication gates remain separate. Reused automated actors disclose prior history; no independent human/external/runtime-model attestation.'
boundary='Compiled local proof package; chapter acceptance and main integration remain separate. The arbitrary-initial FTL family and a minimax lower bound are not established by these two bounds.'
allboundary=' '.join([scope,model,initial_assumptions,refined_assumptions,index,comparison,tests,remaining,gates,'Exact stacked OPEN unmerged PR187 base '+BASE+'; no merge/deploy/main/live/retirement. Main-relative Chapter1 gaps remain unwaived until actual check.'])
newnames=list(load(CONTRACT/'new-public-headers-v1.json'))

def save(p,d,key,pred):
 old=load(p);assert [x for x in old[key] if not pred(x)]==[x for x in d[key] if not pred(x)]
 assert {k:v for k,v in old.items() if k!=key}=={k:v for k,v in d.items() if k!=key}
 Path(p).write_bytes((json.dumps(d,ensure_ascii=False,indent=2)+'\n').encode('utf-8'))

p='website/content/readings.json';d=load(p);x=next(a for a in d['readings'] if a['slug']==ROUTE);before=json.loads(json.dumps(x))
assert len(x['source_theorems'])==4
x['source_theorems'][1]['contract']=dict(model=model,assumptions=refined_assumptions,parameters=index,regret='Cumulative squared loss minus the same final empirical-mean minimizer loss.',guarantee='The existing4+4logT theorem is retained. The proof now separately exposes its initial1/4 estimate and exact later harmonic tail.')
x['source_theorems'][1]['local_status']=dict(status='compiled',label='Existing FTL chain, two proof bounds exposed',boundary=boundary)
for n,label,math,assumptions,proof in [
 (newnames[0],'Theorem 1.3 proof: initial1/4 stability',r'(x_1-y_1)^2-(x_1^*-y_1)^2\le\tfrac14',initial_assumptions,'After observing the first target, its hindsight mean is that target, so the second squared loss is zero. The interval bounds imply y1(1-y1)>=0, which bounds the initial squared error by1/4.'),
 (newnames[1],'Theorem 1.3 proof: exact finite-horizon tail',r'R_T\le\tfrac14+4\sum_{t=2}^{T}\frac1t',refined_assumptions,'Be-the-Leader compares the produced prefix minimizers with the final mean. Subtract these losses from the actual prediction losses, split off the first round, and add its1/4 estimate to the existing4/t bounds for later rounds.')]:
 x['source_theorems'].append(dict(label=label,pages='printed p.5 (unnumbered proof bound)',pdf_page=17,url='https://arxiv.org/pdf/1912.13213v10',math=math,fallback=proof,plain=proof,relationship='Source interface: '+PRE+n,contract=dict(model=model,assumptions=assumptions,parameters=index,regret='Actual initial stability loss difference.' if n==newnames[0] else 'Actual predictor loss minus the produced best-fixed mean loss.',guarantee=proof+' '+comparison+' '+tests),local_status=dict(status='compiled',label='New source-bound proof compiled locally',boundary=boundary)))
assert x['source_theorems'][0]==before['source_theorems'][0] and x['source_theorems'][2:4]==before['source_theorems'][2:]
assert {k:v for k,v in x.items() if k!='source_theorems'}=={k:v for k,v in before.items() if k!='source_theorems'}
save(p,d,'readings',lambda a:a.get('slug')==ROUTE)
p='website/content/highlights.json';d=load(p);oldnote=next(a for a in d['highlights'] if a['full_name']==PRE+'theorem_1_3')
oldnote['lean_notes']=refined_assumptions+' '+model+' '+comparison+' '+index+' '+boundary
oldnote['proof_idea']='Produce prefix empirical-mean minimizers, apply Be-the-Leader, derive stability from the actual mean update, and sum. The retained theorem bounds the harmonic sum by1+logT; two separate proof statements now retain the first-round quarter.'
oldnote['why']='This guarantee concerns the actual causal past-mean predictor. It preserves the source logarithmic upper bound; lower bounds and broader initialization are separate obligations.'
for j,n in enumerate(newnames):
 card=x['source_theorems'][4+j]
 d['highlights'].append(dict(full_name=PRE+n,title=card['label'],chapter=ROUTE,featured=False,teaching_order=5+j,plain=card['plain'],math='\\('+card['math']+'\\)',intuition=card['plain'],why='Expose the exact unnumbered estimate used in the source proof, with its original assumptions.',position='Orabona v10 Chapter1, Theorem1.3 proof, printed p.5 / PDF p.17.',proof_idea=card['plain'],lean_notes=card['contract']['assumptions']+' '+model+' '+index+' '+comparison+' '+tests+' '+boundary,dependencies=[PRE+'meanPredict',PRE+'empiricalMean'] if j==0 else [PRE+'meanPredict_initial_stability',PRE+'meanPredict_stability',PRE+'lemma_1_2',PRE+'empiricalMean_mem',PRE+'empiricalMean_minimizes']))
save(p,d,'highlights',lambda a:a.get('full_name') in [PRE+'theorem_1_3',*[PRE+n for n in newnames]])
p='website/content/chapters.json';d=load(p);x=next(a for a in d['chapters'] if a['slug']==ROUTE)
x['completion_blockers']=[remaining,'Eight other Chapter1 main-relative contributor gaps, including Foundations, remain mandatory unless separately resolved by the actual gate. This FTL package does not accept the chapter.']
x['open_gaps']=[remaining,'Two source bounds are locally compiled; combined acceptance, PR delivery and main integration have separate evidence.']
save(p,d,'chapters',lambda a:a.get('slug')==ROUTE)
c=load('research-wiki/contribution-contracts/online-foundations-public-20261007.json')
c.update(id=TASK,route='online-learning/chapter-1',frontier_cell=ROUTE,target=scope,affected_files=[PUBLIC.as_posix(),'website/content/readings.json','website/content/highlights.json','website/content/chapters.json'],declarations=[PRE+n for n in [*load(CONTRACT/'existing-proof-headers-v1.json'),*newnames]])
c['source'].update(anchor='Theorem1.3 printed4/PDF16; two unnumbered proof bounds printed5/PDF17; source harmonic step printed6/PDF18')
c['reuse_plan'].update(classification='missing',decision='new_shared',searched_existing=['Actual pinned FTL/mean/Be-the-Leader declarations, Mathlib Finset.sum_range_succ and harmonic APIs, exact types and compiled VALUE references.'],reused_declarations=[PRE+n for n in load(CONTRACT/'existing-proof-headers-v1.json')]+[PRE+'meanPredict',PRE+'lemma_1_2',PRE+'empiricalMean_mem',PRE+'empiricalMean_minimizes'],new_shared_declarations=[PRE+n for n in newnames],known_consumers=[PRE+newnames[1],TEST+'endpoint_values',TEST+'one_round_refined',TEST+'two_round_refined'],planned_consumers=[],no_duplicate_wrapper=True,decision_reason='Missing genuine maintext proof estimates extend the existing shared causal FTL module; no duplicate library or generic wrapper.')
c['semantic_roundtrip'].update(status='accepted',formalizer='/root',blind_decoder='/root/osd_blind',source_reviewer='/root/source_reviewer',verdict=body['verdict'],remaining_semantic_delta='Source scalar1-based game maps to0-based Lean; best-fixed minimum represented by produced feasible mean. Existing auxiliary consumer generalized; two new endpoints produce hypotheses from true predictor/targets. CONTRACT/BODY accepted; FINALpending; actor history disclosed/no human/external/runtime attestation.')
c['graph_contribution'].update(lean_graph='new-node',overview_graph='updated',focus_targets=[PRE+n for n in newnames],functor_hypergraph='none-found-with-reason',functor_reason='Two refinements inside the same scalar guessing game, no cross-setting functor.',visual_review='Actual15 compiled selected nodes,13proofs2defs/9prespecified VALUE; preserve10821 registry IDsURLs plus exactly2new production proofnodes; current HTML/pixels pending.',edge_semantics='formal-solid; overlays-dashed')
c['progress_updates'].update(teaching_route='Preserve four existing route links; update bounded FTL note/card and add two precise proof-source cards/notes.',results_ledger='Accepted16-item source enumeration with open required subobligations/proof totalnull; old inventory immutable.',roadmap='Chapter1/2 incomplete,3–16unenumerated/appendicesrequired/GoalACTIVE; globalSGB immutable.',website_surfaces=['website/content/readings.json','website/content/highlights.json','website/content/chapters.json'],inherited_source_caption='Two new source bounds; six validation proofs are not additional source results.')
c['truth_boundary']=allboundary
c['verification'].update(focused_checks=[gates],bandit_check='Current combined root/Tests/fullharness required.',site_build='Clean current applicable Leanverified site required after combined gate.',site_check='Same10821 IDsURLs+2proofnodes and hashes; existing cards/notes/formulas/links preserved; current source/full reader pixels required.',independent_review='Required distinct reused neutraldecoder/CONTRACT/BODY accepted; FINALpending; no human/external/runtime attestation.',owned_test_files=[CANARY.as_posix()],owned_test_root_files=['Tests.lean'],contributor_scope='Actual changed production surfaces: owning FTL and threeJSONs. Test file/root separately owned and fully gated. Main-relative eight other Chapter1 gaps remain unwaived.')
write('research-wiki/contribution-contracts/online-ftl-sharp-20261007.json',c)
write(RUN/'reader-integration-v1.json',dict(status='Scoped reader integrated after actual BODY acceptance',old_FTL_card_and_note_updated=True,new_source_cards=2,new_public_notes=2,other_cards_notes_math_Books_unchanged=True,four_existing_curated_links_unchanged=True,one_Tests_import=True,new_public_math=2,new_named_validation_proofs=6,new_registry_nodes_expected=2,chapter_complete=False,goal_complete=False,source_package_accepted=False,combined_reader_FINAL_native_PR='pending'))
fixed(proving=True,integrated=True)
