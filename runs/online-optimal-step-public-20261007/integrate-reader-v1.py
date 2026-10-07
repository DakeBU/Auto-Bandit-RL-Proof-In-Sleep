"""Authorized current reader prose only after distinct CONTRACT/BODY acceptance."""
from common_v1 import *
fixed();r=load(RUN/'public-body-receipt-v1.json');assert r['actor']['task']=='/root/source_reviewer' and r['verdict'] in ['accepted','accepted-with-explicit-delta'] and sha(r['report'])==r['report_sha256']
for k in ['required_repairs','required_mathematical_repairs','required_metadata_repairs']:assert not r.get(k,[]),k
for receipt,inputs in [('source-contract-receipt-v1.json','source-contract-inputs-v1.json'),('public-body-receipt-v1.json','body-review-inputs-v1.json')]:
 reviewed={x['path']:x['sha256'] for x in load(RUN/receipt)['reviewed_files']}
 for x in load(RUN/inputs)['rows']:assert reviewed[x['path']]==x['sha256']==sha(x['path'])
b=load(RUN/'body-bindings-v1.json')
scope='Current revalidation of TWO unnumbered printed15/PDF27 scalar calculations: existing11 public proofs/2definitions and whole23canary proofs/4definitions/1abbreviation. ZERO new mathematics, definitions, source closures or registry nodes.'
evidence=f'Actual focused{b["focused_jobs"]} jobs including caches;41named standard-only kernel checks,11unchanged full native/raw guards and27prespecified proof VALUE pairs ({b["direct_references"]} direct references) pass. Distinct required automated neutral decoder/CONTRACT/BODY accepted; current combined/reader/FINAL/native/PR remain separate gates.'
boundary='Total real definitions: F(A,B,eta)=A/(2 eta)+eta B/2 and S(A,B)=sqrt A/sqrt B. Admissible optimizers have eta>0. Gap/lowerbound allow A,B>=0; attained universal minimum and equality iff eta=S(A,B) require A,B>0. ALL positive competing eta use SAME FIXED A,B; the numerical example alone is not universal optimization. Distance R>0 means A=R^2 and energy B>0; supplied D,G>0 and natural T>=1 give A=D^2,B=G^2T,source L=Lean G. T1 is valid. A=0<B admits strictly improving eta/2 for every positive eta; B=0<A admits2eta; A=B=0 is a constant-zero algebraic extension. Totalized sqrt/division at eta0 or T0 does not make an admissible positive optimizer. No signed-coefficient optimizer.'
warning='The source explicitly warns future gradients depend on eta itself and comparator distance is unavailable. These fixed-coefficient minima do not construct a future-informed learner or optimize actual regret across rerun trajectories. Only the COARSER two-term expression is minimized; the original sharp OGD bound retains the negative terminal-distance residual. Actual OGD/OSD regret still requires its separate feasible domain/initial point/loss/gradient-or-global-support/diameter/gradient/horizon hypotheses. The same-loss real projected OGD energy canary is a finite dependence witness, not a Chapter5 impossibility/lower-bound, anytime or minimax certificate.'
history='Historical accepted PR151 delivered these same unchanged declarations; current package stacks on OPEN unmerged PR184 exact '+BASE+'. No historical proof or source closure is counted twice. Original CONTRACT/BODY reader raw snapshots stay immutable; FINAL separately reviews current reader bytes. All decoded math strings remain unchanged; current pixels are independently required.'
remaining='Unit-analysis current migration, remaining Chapter1/2 maintext, nine OTHER Chapter1 origin/main contributor gaps and necessary appendices REQUIRED. Chapter2 mandatory total null/incomplete; Chapters3-16 unenumerated; total Goal ACTIVE/unbudgeted. No chapter/book completion, merge/deploy/main/live update or checkout retirement.'
def formulas(o):
 if isinstance(o,dict):return [v for k,v in o.items() if k=='math']+sum([formulas(v) for k,v in o.items() if k!='math'],[])
 if isinstance(o,list):return sum([formulas(v) for v in o],[])
 return []
def save(p,d,key,pred):
 old=load(p);assert [x for x in old[key] if not pred(x)]==[x for x in d[key] if not pred(x)] and {k:v for k,v in old.items() if k!=key}=={k:v for k,v in d.items() if k!=key}
 Path(p).write_bytes((json.dumps(d,ensure_ascii=False,indent=2)+'\n').encode('utf-8'))
p='website/content/readings.json';d=load(p);x=next(a for a in d['readings'] if a['slug']==ROUTE)
assert [len(x[k]) for k in ['notation','teaching_route','source_theorems']]==[3,4,2] and len(x['proof_bridge']['steps'])==4 and len(x['worked_example']['steps'])==5
original=formulas(x);curated=x['teaching_route'][:]
x['notation'][0]['meaning']='Complete total real scalar definitions: F(A,B,eta)=A/(2 eta)+eta B/2; S(A,B)=sqrt A/sqrt B. SAME A,B are fixed through every positive-eta comparison; unrestricted function definitions do not extend optimizer hypotheses.'
x['notation'][2]['meaning']=boundary
for card in x['source_theorems']:card['local_status']=dict(status='compiled',label='Existing scalar producer: current source/body evidence',boundary=scope+' '+evidence+' '+boundary+' '+warning+' '+history+' '+remaining)
x['source_theorems'][0]['contract']['parameters']=boundary+' '+warning
x['source_theorems'][1]['contract']['parameters']='Scalar theorem has no domain or learner input. '+warning
for key in ['proof_bridge','worked_example']:x[key]['boundary']=scope+' '+boundary+' '+warning+' '+history+' '+remaining
x['worked_example']['takeaway']='The universal scalar minimum holds SAME coefficients fixed. The actual same-loss projected OGD canary proves that two chosen steps have different realized energy; it does not prove the Chapter5 impossibility or lower-bound claim.'
assert formulas(x)==original and x['teaching_route']==curated;save(p,d,'readings',lambda a:a.get('slug')==ROUTE)
p='website/content/highlights.json';d=load(p);xs=[a for a in d['highlights'] if a.get('chapter')==ROUTE];assert len(xs)==11 and all(a['full_name'].startswith(PRE) for a in xs);oldmath=formulas(xs)
for a in xs:a['lean_notes']=a['lean_notes']+' '+scope+' '+evidence+' Scalar fixed-coefficient producer, not future-informed online or across-rerun regret optimization. Original positivity/degenerate hypotheses remain in the exact displayed statement. '+remaining
assert formulas(xs)==oldmath;save(p,d,'highlights',lambda a:a.get('chapter')==ROUTE)
p='website/content/chapters.json';d=load(p);x=next(a for a in d['chapters'] if a['slug']==ROUTE);assert x['module_globs']==[PUBLIC.as_posix()]
x['summary']='Fixed-coefficient attained scalar minima, unique positive optimizer, zero boundaries and actual same-loss OGD energy dependence.'
x['completion_definition']=scope+' '+history
x['completion_blockers']=[remaining,'Current combined/reader/FINAL/native acceptance and exact-base stacked draft delivery remain separate gates.']
x['open_gaps']=[warning,remaining];save(p,d,'chapters',lambda a:a.get('slug')==ROUTE)
names=[PRE+n for n in load(CONTRACT/'headers-v1.json')];c=load('research-wiki/contribution-contracts/ONLINE-OPTIMAL-STEP-20261004.json')
c.update(id=TASK,target=scope,affected_files=['website/content/readings.json','website/content/highlights.json','website/content/chapters.json'],declarations=names)
c['reuse_plan'].update(classification='reuse',decision='reuse_existing',searched_existing=['Actual pinned local/mathlib declaration search; all11closed neutral Props/fullactualtype-rfl identities.'],reused_declarations=names,new_shared_declarations=[],planned_consumers=['Remaining Chapter1/2 exact-source gate; sequential future adaptive/parameter-free algorithms may use scalar comparisons with their own information conditions.'],decision_reason='Exact existing scalar producers and degenerate boundaries reused; no duplicate wrapper/per-book proof tree/toolchain upgrade; zero new mathematics.')
c['semantic_roundtrip'].update(status='accepted',formalizer='/root',blind_decoder='/root/osd_blind',source_reviewer='/root/source_reviewer',verdict=r['verdict'],remaining_semantic_delta=boundary+' '+warning+' CONTRACT/BODY accepted; FINAL pending. Distinct reused automated roles requested Astra/medium; no human/external/runtime attestation.')
c['graph_contribution'].update(lean_graph='reuse-only',overview_graph='updated',functor_hypergraph='none-found-with-reason',functor_reason='Scalar source mapping on shared existing registry; no separately certified categorical functor.',focus_targets=names,visual_review='Actual compiled TEST41nodes34proof7defs incl1abbr;27prespecified VALUE pairs. Same10821IDsURLs/11nativehashes/current2cards11notes4links/pixels required separately.')
c['progress_updates'].update(teaching_route='updated: current exact-source scalar reuse evidence on shared registry',results_ledger='no-change-with-reason: original source inventory immutable; additive accepted overlay after FINAL, zero new mathematics',roadmap='no-change-with-reason: GoalACTIVE/Chapter1/2 required/nullChapter2/3-16unenumerated;globalSGB retained',website_surfaces=c['affected_files'])
c['truth_boundary']=scope+' '+evidence+' '+boundary+' '+warning+' '+history+' '+remaining
c['verification'].update(focused_checks=[evidence],bandit_check='Actual combined root/Tests/full harness required after current scoped reader change.',site_build='Clean local Lean-verified snapshot only after applicable actual combined gate.',site_check='Same10821IDsURLs/11nativehashes/2cards11notes4links and actual source/algorithm/bridge/example pixels required.',independent_review='Distinct required reused neutral decoder/CONTRACT/BODY accepted; FINAL pending. No human/external/runtime attestation.',owned_test_files=[],owned_test_root_files=[])
write('research-wiki/contribution-contracts/online-optimal-step-public-20261007.json',c)
# new-task already appended the native OWN manifest row; do not append/replace it again.
manifest=Path('MANIFEST.md').read_text(encoding='utf-8');assert TASK in manifest
write(RUN/'reader-integration-v1.json',dict(route=ROUTE,new_proofs=0,new_definitions=0,new_registry_nodes=0,new_source_math_closures=0,all_other_Books_unchanged=True,ALL_formula_strings_unchanged=True,curated_names_unchanged=True,native_MANIFEST_OWNrow_retained=True,source_cards=2,library_notes=11,curated_links=4,notation_entries=3,proofbridge_steps=4,worked_example_steps=5,source_package_accepted=False,chapter_complete=False,goal_complete=False))
fixed(True);print('Current evidence prose integrated only in2cards/11notes/4links; ALL math/otherBooks unchanged. Combined/FINAL pending.')
