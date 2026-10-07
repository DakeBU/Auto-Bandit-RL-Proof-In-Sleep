"""Apply only current evidence prose within the existing same-registry route."""
from common_v2 import *
fixed();r=load(RUN/'public-body-receipt-v2.json');assert r['actor']['task']=='/root/source_reviewer' and r['verdict'] in ['accepted','accepted-with-explicit-delta'] and sha(r['report'])==r['report_sha256']
for k in ['required_repairs','required_mathematical_repairs','required_metadata_repairs']:assert not r.get(k,[]),k
for receipt,inputs in [('source-contract-receipt-v2.json','source-contract-inputs-v2.json'),('public-body-receipt-v2.json','body-review-inputs-v2.json')]:
 reviewed={x['path']:x['sha256'] for x in load(RUN/receipt)['reviewed_files']}
 for x in load(RUN/inputs)['rows']:assert reviewed[x['path']]==x['sha256']==sha(x['path'])
correction=load(RUN/'reader-escaping-correction-receipt-v4.json');assert correction['verdict']=='accepted' and correction['original_R1_R8_preserved'] and not correction['required_reader_escaping_changes'] and not correction['pixel_success_certified']
assert correction['report_sha256']==sha(correction['report']);assert load(RUN/'reader-escaping-verification-v4.json')['no_reader_or_Lean_changes']
b=load(RUN/'body-bindings-v2.json')
scope='Current revalidation of one unnumbered Section2.3 reduction (printed22/PDF34): existing18 proofs/9definitions/3abbreviations and whole25canary proofs/8definitions/2abbreviations. ZERO new mathematics, definitions, source-terminal closures or registry nodes.'
evidence=f'Current focused{b["focused_jobs"]} jobs include caches;65named standard-only kernel checks,eighteen unchanged full native guards and28prespecified actual proof-value pairs pass ({b["direct_references"]} direct references). Distinct required automated neutral decoder/source CONTRACT/BODY accepted; current combined/reader/FINAL/PR gates are separate.'
boundary='Fixed exogenous deterministic A receives strict-past vectors. Actual Nat.rec/Fin.snoc appends current selected support after output; reconstructed history equals ALL played outputs. Both regrets use SAME A and actual generated sequence. Proper EReal means no bottom anywhere and an ambient finite witness; GLOBAL supporting inequalities compare all ambient points, producing finite played/comparator values before toReal. Played-only LegalFeedback suffices for the ambient core; Feasible A is required by full-source/canonical OCO adapters, with optional off-path OracleLaw only sufficient. The actual canonical noncomputable chooser produces legality; no assigned tie or assumed performance. Universal hB quantifies over ALL vector sequences and feasible comparators at fixedT for SAME A; it is an INPUT to transport, not a performance producer for arbitrary learners. B and u enter evaluation only. Prefix comparisons keep A,p common and require equal strict-past WHOLE losses. First source round1 is Lean0 with x0=A0(empty);T0 is an empty algebraic extension. No boundedness, gradient/rate prescription, universal optimality, randomized/measurable/independent parameter-law or finite-query executable guarantee.'
remaining='Optimal-step/unit-analysis current revalidation, remaining Chapter1/2 maintext, nine OTHERChapter1 origin/main contribution contracts and necessary appendices remain REQUIRED. Chapter2 mandatory total is incomplete; Chapters3-16 remain unenumerated; total Goal ACTIVE/unbudgeted. No chapter/book completion, merge/deploy/main/live update or checkout retirement.'
history='Historical accepted PR150 originally delivered these unchanged declarations. Current package stacks on OPEN unmerged PR183 exact '+BASE+'; no historical proof or closure is counted again. Original truncated v1 draft extractor metadata, auxiliary filename failure and mistaken extra R9-format finding are retained; complete v2/v3 probes and separate correction-v4 resolve them. All actual formula strings were already correctly decoded and remain unchanged; current pixels remain independently required.'
def formulas(obj):
 if isinstance(obj,dict):return [v for k,v in obj.items() if k=='math']+sum([formulas(v) for k,v in obj.items() if k!='math'],[])
 if isinstance(obj,list):return sum([formulas(v) for v in obj],[])
 return []
def save(p,d,key,pred):
 old=load(p);assert [x for x in old[key] if not pred(x)]==[x for x in d[key] if not pred(x)]
 assert {k:v for k,v in old.items() if k!=key}=={k:v for k,v in d.items() if k!=key}
 Path(p).write_bytes((json.dumps(d,ensure_ascii=False,indent=2)+'\n').encode('utf-8'))
p='website/content/readings.json';d=load(p);x=next(a for a in d['readings'] if a['slug']==ROUTE)
assert [len(x[k]) for k in ['notation','teaching_route','source_theorems']]==[3,4,1] and len(x['proof_bridge']['steps'])==4
original=formulas(x);curated=x['teaching_route'][:]
card=x['source_theorems'][0];card['contract']['parameters']=boundary
card['contract']['guarantee']='Actual convex regret <= same learner/generated feedback linear regret for every feasible comparator. A universal OLO bound supplies transport for that same A; source does not assert universal optimality or a guarantee for arbitrary learners.'
card['local_status']=dict(status='compiled',label='Existing same-trajectory reduction: current source/body evidence',boundary=scope+' '+evidence+' '+boundary+' '+history+' '+remaining)
for key in ['proof_bridge','worked_example']:x[key]['boundary']=scope+' '+boundary+' '+history+' '+remaining
assert formulas(x)==original and x['teaching_route']==curated
save(p,d,'readings',lambda a:a.get('slug')==ROUTE)
p='website/content/highlights.json';d=load(p);xs=[a for a in d['highlights'] if a.get('chapter')==ROUTE];assert len(xs)==18 and all(a['full_name'].startswith(PRE) for a in xs)
oldmath=formulas(xs)
for a in xs:a['lean_notes']=a['lean_notes']+' '+scope+' '+evidence+' '+boundary+' '+remaining
assert formulas(xs)==oldmath;save(p,d,'highlights',lambda a:a.get('chapter')==ROUTE)
p='website/content/chapters.json';d=load(p);x=next(a for a in d['chapters'] if a['slug']==ROUTE);assert x['module_globs']==[PUBLIC.as_posix()]
x['summary']='One causal learner and its actual support-feedback trajectory, convex-to-linear comparison and transport of a separately proved universal OLO bound.'
x['completion_definition']=scope+' Structural identities and transport/producers refine the single unnumbered source reduction. '+history
x['completion_blockers']=[remaining,'Current combined/reader/FINAL/native acceptance and exact-base stacked draft delivery are separate gates; local compilation is not merge/live.']
x['open_gaps']=[boundary,remaining];save(p,d,'chapters',lambda a:a.get('slug')==ROUTE)
names=[PRE+n for n in load(CONTRACT/'headers-v2.json')];c=load('research-wiki/contribution-contracts/ONLINE-LINEARIZATION-20261004.json')
c.update(id=TASK,target=scope,affected_files=['website/content/readings.json','website/content/highlights.json','website/content/chapters.json'],declarations=names)
c['reuse_plan'].update(classification='reuse',decision='reuse_existing',searched_existing=['Actual local/mathlib declaration rg searches and all18 full closed proposition identities under supplied complete neutral aliases.'],reused_declarations=names,new_shared_declarations=[],planned_consumers=['Remaining Chapter1/2 exact-source gate; future OLO algorithms may instantiate this same shared reducer after sequential chapter gates.'],decision_reason='Reuse exact existing causal history/support/same-run comparison/transport/canonical producer. No duplicate wrapper, new loss, per-book project or new proof tree; zero new mathematics.')
c['semantic_roundtrip'].update(status='accepted',formalizer='/root',blind_decoder='/root/osd_blind',source_reviewer='/root/source_reviewer',verdict=r['verdict'],remaining_semantic_delta=boundary+' '+history+' CONTRACT/BODY accepted, current FINAL pending; distinct reused automated roles, requested Astra/medium, no runtime/human/external attestation.')
c['graph_contribution'].update(lean_graph='reuse-only',overview_graph='updated',functor_hypergraph='none-found-with-reason',functor_reason='Existing source linear-regret reduction reused on the same shared Lean graph; no separately certified categorical functor.',focus_targets=names,visual_review='Actual compiled TEST selected65nodes43proofs22defs including5abbr/2925directrefs/28prespecifiedVALUEpairs. Same10821registry IDsURLs/18nativehashes/currentonecard/eighteennotes/fourcuratedlinks/pixels separate.')
c['progress_updates'].update(teaching_route='updated: current source-qualified same-run linearization reuse evidence on shared registry',results_ledger='no-change-with-reason: old inventory immutable; additive current accepted overlay after FINAL, zero new mathematics',roadmap='no-change-with-reason: totalGoalACTIVE/Chapter1/2 required/nullChapter2/3-16unenumerated;SGB preserved',website_surfaces=c['affected_files'])
c['truth_boundary']=scope+' '+evidence+' '+boundary+' '+history+' '+remaining
c['verification'].update(focused_checks=[evidence],bandit_check='Actual current combined root/Tests/full harness required after scoped reader prose changes.',site_build='Clean local Lean-verified snapshot only after applicable actual combined gate.',site_check='Same10821IDsURLs/18nativehashes/onecard18notes4curatedlinks and actualsource/algorithm/bridge/example formula pixels required.',independent_review='Distinct reused neutral decoder/source CONTRACT/BODY and separate correction-v4 accepted; FINAL pending. No human/external/runtime attestation.',owned_test_files=[],owned_test_root_files=[])
write('research-wiki/contribution-contracts/online-linearization-public-20261007.json',c)
manifest=Path('MANIFEST.md');assert TASK not in manifest.read_text(encoding='utf-8');manifest.write_bytes(manifest.read_bytes()+('\n- '+TASK+': Existing Section2.3 same-run causal linearization current source/public reuse; zero new mathematics. Evidence '+RUN.relative_to(ROOT).as_posix()+'; combined/FINAL/PR pending, Chapter1/2 and wholeGoal incomplete.\n').encode('utf-8'))
write(RUN/'reader-integration-v2.json',dict(route=ROUTE,new_proofs=0,new_definitions=0,new_registry_nodes=0,new_source_math_closures=0,all_other_Books_unchanged=True,ALL_formula_strings_unchanged=True,curated_names_unchanged=True,source_cards=1,library_notes=18,curated_links=4,notation_entries=3,proofbridge_steps=4,worked_example_steps=4,R9_format_withdrawn_only_by_separate_correction=True,source_package_accepted=False,chapter_complete=False,goal_complete=False))
fixed(True);print('Current same-run source/body evidence integrated only in existing1card/18notes/4links route; ALL math strings/otherBooks unchanged. Combined/FINAL pending.')
