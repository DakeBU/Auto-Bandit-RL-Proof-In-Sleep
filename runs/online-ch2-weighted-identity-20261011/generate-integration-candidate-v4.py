"""Create-only ignored candidate generator; deliberately has NO canonical apply operation."""
from pathlib import Path
import argparse,copy,difflib,hashlib,json
ROOT=Path(__file__).resolve().parents[2]
HERE=Path(__file__).resolve().parent
PLAN=HERE/'proposed-rows-diffplan-v2.json'
PLAN_SHA='9d4bd2001d171866bf52ed3ea796389af32b3249883f56961caf20dd91d3f3e8'
def sha(b):return hashlib.sha256(b).hexdigest()
def raw(p):return p.read_bytes()
def dump(v):return (json.dumps(v,indent=2,ensure_ascii=False)+'\n').encode('utf-8')
def put(p,b):
 p.parent.mkdir(parents=True,exist_ok=True)
 with p.open('xb') as f:f.write(b)
def append(b,s):return b+(b'' if not b or b.endswith(b'\n') else b'\n')+s.encode('utf-8')
def readiness(packet):
 # This check never writes canonical files. A later distinct reviewed applier is required.
 q=json.loads(raw(packet));required=['accepted_canary_body_receipt','accepted_canary_source_receipt','canary_module','canary_contracts','production_body_receipt']
 for k in required:
  v=q[k];p=ROOT/v['path'];assert p.is_file(),k;assert sha(raw(p))==v['sha256'],k
 body=json.loads(raw(ROOT/q['accepted_canary_body_receipt']['path']))
 source=json.loads(raw(ROOT/q['accepted_canary_source_receipt']['path']))
 assert body.get('semantic_verdict',body.get('verdict')) in ['accepted','accepted-with-explicit-delta'], 'actual accepted canary BODY verdict absent'
 assert source.get('semantic_verdict',source.get('verdict')) in ['accepted','accepted-with-explicit-delta'],'actual accepted canary source verdict absent'
 assert q['canary_theorem_count']==5 and q['canary_definition_count']==10
 assert q['canary_module']['sha256'] in json.dumps(body),'BODY receipt does not bind module hash'
 assert q['canary_contracts']['sha256'] in json.dumps(source),'source receipt does not bind five-contract packet hash'
 assert q.get('distinct_integration_review_accepted') is True
 raise SystemExit('Evidence presence checks passed, but canonical apply is intentionally unavailable; separate reviewed applier and actual gate policy required.')
a=argparse.ArgumentParser();a.add_argument('--draft',action='store_true');a.add_argument('--check-readiness',type=Path);args=a.parse_args()
if args.check_readiness:readiness(args.check_readiness)
assert args.draft,'Only --draft or --check-readiness is supported; no apply operation.'
assert sha(raw(PLAN))==PLAN_SHA
plan=json.loads(raw(PLAN));OUT=HERE/'integration-candidate-v4';assert not OUT.exists(),'create-only candidate directory already exists'
inputs={f:raw(ROOT/f) for f in plan['input_raw_sha256']}
for f,b in inputs.items():assert sha(b)==plan['input_raw_sha256'][f],f
# Pin additional current root/schema inputs; never read or copy accepted proof bodies.
for f in ['BanditRLProof.lean','Tests.lean','docs/contribution-contract.schema.json','tools/check_contributor_contract.py']:inputs[f]=raw(ROOT/f)
RUN='runs/online-ch2-weighted-identity-20261011/'
expected={'fresh-core-BODY-review-v1.json':'ec9f6ed5f0cf4a7ee82c02354ff7f439a9eafc9baed1982b3be40394c979733b','fresh-canary-BODY-review-v1.json':'f0988dbb4c4a341ea7448f3db389c40c2149222806ae9b94a6dfd4c77dbb972d','fresh-canary-contract-source-review-v1.json':'39045da4ccbef972b3690ed081495f9cc4115aff1e3bbe3347b5f791b716df1b'}
for f,h in expected.items():
 inputs[RUN+f]=raw(ROOT/(RUN+f));assert sha(inputs[RUN+f])==h
core=json.loads(inputs[RUN+'fresh-core-BODY-review-v1.json']);canary=json.loads(inputs[RUN+'fresh-canary-BODY-review-v1.json'])
assert core['verdict']=='accepted-candidate-core-only' and not core['blocking_repairs']
assert canary['verdict']=='accepted-candidate-canary-BODY-only' and not canary['blocking_repairs']
# Verify and snapshot every exact source/input bound by the actual distinct BODY reviews.
for review in [core,canary]:
 for row in review['input_raw_hashes_before_after']:
  path=Path(row['path']);rel=path.relative_to(ROOT).as_posix();b=raw(path)
  assert row['before']==row['after']==sha(b),rel
  if rel in inputs:assert inputs[rel]==b
  inputs[rel]=b
for f in ['fresh-blind-reconstruction-v2.json','fresh-canary-blind-reconstruction-v1.json','production-type-value-constants-v1.json','production-value-export-v1.json','production-value-export-v1-stdout.txt','production-value-export-v1-stderr.txt','ExportWeightedProductionValuesV1.lean','canary-selected-values-v1.json']:
 inputs[RUN+f]=raw(ROOT/(RUN+f))
assert json.loads(inputs[RUN+'production-value-export-v1.json'])['actual_exit']==0
values=json.loads(inputs[RUN+'production-type-value-constants-v1.json'])
value_nodes={x['declaration']:x for x in values['nodes']}
scalar='BanditRL.OnlineWeightedPotential.weighted_difference_sum_eq';distance='BanditRL.OnlineWeightedPotential.distance_potential_sum_eq'
assert scalar in value_nodes[distance]['VALUE_constants']
assert {'Finset.sum_range_by_parts',"Finset.sum_range_sub'"}<=set(value_nodes[scalar]['VALUE_constants'])
assert len(core['verification']['axioms'])==2 and len(canary['verification']['five_axiom_sets'])==5
for row in canary['verification']['five_axiom_sets']:assert set(row['axioms'])=={'propext','Classical.choice','Quot.sound'}
assert canary['approved_Test_raw_sha256']==sha(inputs['Tests/OnlineWeightedPotentialCanary.lean'])
assert core['approved_source_raw_sha256']==sha(inputs['BanditRLProof/OnlineWeightedPotential.lean'])

for f,b in inputs.items():put(OUT/'before'/f,b)
put(OUT/'approved-plan.json',raw(PLAN))
changes={}
changes['.gitattributes']=append(inputs['.gitattributes'],'BanditRLProof/OnlineWeightedPotential.lean text eol=lf\nTests/OnlineWeightedPotentialCanary.lean text eol=lf\n')
for file,imp in [('BanditRLProof.lean','import BanditRLProof.OnlineWeightedPotential'),('Tests.lean','import Tests.OnlineWeightedPotentialCanary')]:
 assert imp not in inputs[file].decode('utf-8');changes[file]=append(inputs[file],imp+'\n')
boundary='Locally compiled and independently source/BODY-reviewed exact identity with explicit algebraic generalization. Combined package gates remain pending. Chapter2 remains partial, accepted=false and complete proof denominator=null; all eight forward containers and six future claims remain open. Whole Chapters1-16 Goal ACTIVE; unmerged and unpublished.';lesson=copy.deepcopy(plan['reader_lesson']);card=copy.deepcopy(plan['source_card'])
card['local_status']={'status':'compiled','label':'Locally compiled and source-reviewed exact identity','boundary':boundary}
card['relationship']='Unnumbered second display equality in the proof of Theorem2.13. '+plan['generalization_delta']+' '+boundary
lesson['position']='Orabona v10, printed14/PDF26, Theorem2.13 proof second display equality. '+boundary
lesson['dependencies']=[scalar]
lesson['lean_notes']=plan['generalization_delta']+' The distance proof actually reuses '+scalar+'. The scalar companion VALUE contains Finset.sum_range_by_parts and Finset.sum_range_sub\'. These are selected actual compiled VALUE occurrences, not necessity claims or a complete transitive graph. Exact folded statements and full proof source links expose both declarations through the shared catalog. Existing OGD/OSD production theorems remain prospective reuse overlays only; their accepted bodies are unchanged.'
for file,key in [('website/content/chapters.json','chapters'),('website/content/readings.json','readings'),('website/content/highlights.json','highlights'),('docs/contracts/online-book-v1/coverage.json','chapters')]:
 old=json.loads(inputs[file]);obj=copy.deepcopy(old)
 if file.endswith('/chapters.json'):
  r=next(x for x in obj[key] if x['slug']=='online-ogd');r['module_globs'].append('BanditRLProof/OnlineWeightedPotential.lean');r['learning_goals'].append('Explain the exact weighted-distance equality, its interior reciprocal-step correction and terminal residual.');r['completion_definition']+=' '+boundary
  check=copy.deepcopy(obj);z=next(x for x in check[key] if x['slug']=='online-ogd');orig=next(x for x in old[key] if x['slug']=='online-ogd')
  for k in ['module_globs','learning_goals','completion_definition']:z[k]=orig[k]
  assert check==old
 elif file.endswith('/readings.json'):
  r=next(x for x in obj[key] if x['slug']=='online-ogd');arr=r['source_theorems'];ix=next(i for i,x in enumerate(arr) if '2.13' in x['label'] and ('nonincreasing' in x['label'].lower() or 'variable' in x['label'].lower()))
  arr.insert(ix+1,card);check=copy.deepcopy(obj);next(x for x in check[key] if x['slug']=='online-ogd')['source_theorems'].pop(ix+1);assert check==old
 elif file.endswith('/highlights.json'):
  assert not any(x['full_name']==lesson['full_name'] for x in obj[key]);obj[key].append(lesson);assert obj[key][:-1]==old[key]
 else:
  r=next(x for x in obj[key] if x['chapter']==2);assert r['accepted'] is False and r['mandatory_count'] is None and r['required_open_forward_containers']==8 and r['required_future_mathematical_claims_open_unenumerated']==6
  name='weighted_identity_package_20261011';assert name not in r;r[name]=copy.deepcopy(next(x['proposed_record'] for x in plan['diff_plan'] if x['path']==file));r[name]['stage']='locally-compiled-source-BODY-reviewed-candidate; combined package gates pending';r[name]['evidence']=RUN+'fresh-canary-BODY-review-v1.json';check=copy.deepcopy(obj);del next(x for x in check[key] if x['chapter']==2)[name];assert check==old
 changes[file]=dump(obj)
names=plan['registry_contract']['proposed_production_ids'];names=[n.removeprefix('declaration:') if hasattr(n,'removeprefix') else n[len('declaration:'):] for n in names]
protected=['BanditRLProof/OnlineWeightedPotential.lean','BanditRLProof.lean','website/content/chapters.json','website/content/readings.json','website/content/highlights.json']
manifest={'schema_version':'2.0','id':'ONLINE-CH2-WEIGHTED-IDENTITY-20261011','route':'online-learning/chapter-2/weighted-distance-identity','frontier_cell':'online-ogd','source_facing':True,'source':{'kind':'book','title':'Online Learning: A Modern Introduction Using Convex Optimization','version':'arXiv1912.13213v10 SHA256 cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17','anchor':'Theorem2.13 proof unnumbered second display equality; PDF26/printed14','url':'https://arxiv.org/pdf/1912.13213v10#page=26'},'target':'Expose exact weighted-distance source equality with initial, interior and terminal terms. '+boundary,'affected_files':protected,'declarations':names,'reuse_plan':{'classification':'adapt','decision':'adapt_existing','searched_existing':['Frozen reuse-search and exact source contract in weighted identity RUN; current draft does not rerun retrieval.'],'reused_declarations':['Finset.sum_range_by_parts',"Finset.sum_range_sub'"],'new_shared_declarations':names,'known_consumers':[],'planned_consumers':['Five separately reviewed full Test canaries; approval pending','Existing OGD/OSD are prospective reuse overlays only, not current formal edges'],'no_duplicate_wrapper':True,'decision_reason':'One shared source-normal-form identity and distance specialization; no separate project.'},'reader_contract':{k:True for k in ['source_anchor_visible','natural_language_formula_proof','hidden_assumptions_visible','source_vs_lean_delta_visible','lean_folded','dependencies_visible','remaining_boundary_visible']},'semantic_roundtrip':{'required':True,'status':'source-reviewed','formalizer':'/root/adaptive_formalizer','blind_decoder':'/root/weighted_identity_blind','source_reviewer':'/root/adaptive_reviewer','verdict':'Production accepted-with-explicit-generalization per parent; canary source/BODY acceptance pending; package not accepted.','remaining_semantic_delta':plan['generalization_delta']+' Current production BODY receipt must be rebound by exact hash before application; no copied historical verdict.'},'graph_contribution':{'lean_graph':'integration-node','overview_graph':'updated','functor_hypergraph':'none-found-with-reason','functor_reason':'Ordinary summation-by-parts reuse, no new proved setting transport.','focus_targets':names,'visual_review':'Pending exact candidate integration/registry/rendered-site review.','edge_semantics':'formal-solid; overlays-dashed'},'progress_updates':{'teaching_route':'Proposed one adjacent exact-identity source card and lesson.','banditrlwiki':'no-change-with-reason: no Bandit setting result.','results_ledger':'no-change-with-reason: no chapter/global milestone.','roadmap':'no-change-with-reason: keep existing route registry; C2partial8+6open and GoalACTIVE.','website_surfaces':protected[2:]},'truth_boundary':boundary+' Native prospective adapter unexecuted; later transport of prior phases retrospective.','verification':{'focused_checks':['Parent reports production compile actualexit0 at RAW63d94480e5e5a337acf5019c62e092fd36b1d2bf1a6edfc6f5b6bc5b95aa885a; BODY receipt ec9... not resolved by this draft.','Owned Test file Tests/OnlineWeightedPotentialCanary.lean and Test root Tests.lean; exact module hash/five theorem source packet/ten support definitions and accepted source+BODY receipts REQUIRED before apply. No schema-extra ownership fields.','Two exact new-file LF rules only; old .gitattributes bytes preserved.'],'bandit_check':'Pending current shared root/Tests/full harness gates.','site_build':'Pending authorized build after fresh gates.','site_check':'Pending exact old registry-object preservation and formula/folded-header/full-proof links.','independent_review':'Production explicit-generalization acceptance parent-reported; actual receipt binding and distinct canary/integration/final reviews pending.'},'contributor':{'name':'ABRL agent-assisted weighted identity package','role':'Source-reviewed formalization candidate; authorship unchanged'}}
manifest['reuse_plan']['known_consumers']=[distance]
manifest['reuse_plan']['planned_consumers']=['OGD/OSD production reuse only as prospective overlays; no existing BODY edits.']
manifest['semantic_roundtrip'].update(status='source-reviewed',verdict='Production and five complete canaries accepted by distinct source/BODY reviews as bounded candidates with explicit generalization; no whole-package acceptance.',remaining_semantic_delta=plan['generalization_delta'])
manifest['verification']['focused_checks']=[
 'Production focused compile, public probe, two exact fences and standard axiom sets verified by '+RUN+'fresh-core-BODY-review-v1.json SHA256 '+expected['fresh-core-BODY-review-v1.json']+'. Core RAW '+core['approved_source_raw_sha256']+'.',
 'Owned Test file Tests/OnlineWeightedPotentialCanary.lean RAW '+canary['approved_Test_raw_sha256']+' and Test root Tests.lean. Five complete Test theorems and ten support definitions; source packet SHA256 '+canary['frozen_canary_context_headers_sha256']+'. Actual focused/public probe/selected VALUE export exit0, five fences and standard axiom sets verified by '+RUN+'fresh-canary-BODY-review-v1.json SHA256 '+expected['fresh-canary-BODY-review-v1.json']+'.',
 'Actual Test-layer consumers: '+', '.join(x['declaration'] for x in canary['verification']['five_axiom_sets'])+'. These are implementation counts, never source completion counts.',
 'Production actual VALUE export '+RUN+'production-type-value-constants-v1.json SHA256 '+sha(inputs[RUN+'production-type-value-constants-v1.json'])+'; scalar actual by-parts/telescoping occurrences and distance actual scalar companion occurrence checked. Occurrence not necessity or complete graph.',
 'Two exact file-specific LF rules only; prior attributes bytes preserved.'
]
manifest['verification']['independent_review']='Production '+RUN+'fresh-core-BODY-review-v1.json SHA256 '+expected['fresh-core-BODY-review-v1.json']+'; canary '+RUN+'fresh-canary-BODY-review-v1.json SHA256 '+expected['fresh-canary-BODY-review-v1.json']+'. Exact integration/final package review and combined gates still pending; future actual gate receipts remain separately recorded, never inferred from this candidate manifest.'
def validate(v,s):
 import re
 types={'object':dict,'array':list,'string':str,'boolean':bool}
 if 'type' in s:assert isinstance(v,types[s['type']])
 if 'const' in s:assert v==s['const']
 if 'enum' in s:assert v in s['enum']
 if isinstance(v,dict):
  assert all(k in v for k in s.get('required',[]))
  if s.get('additionalProperties') is False:assert set(v)<=set(s.get('properties',{}))
  for k,x in v.items():
   if k in s.get('properties',{}):validate(x,s['properties'][k])
 if isinstance(v,list):
  assert len(v)>=s.get('minItems',0)
  if s.get('uniqueItems'):assert len(set(json.dumps(x,sort_keys=True) for x in v))==len(v)
  for x in v:validate(x,s.get('items',{}))
 if isinstance(v,str):
  assert len(v)>=s.get('minLength',0)
  if 'pattern' in s:assert re.search(s['pattern'],v)
validate(manifest,json.loads(inputs['docs/contribution-contract.schema.json']))
assert manifest['affected_files']==protected and manifest['declarations']==names
changes['research-wiki/contribution-contracts/ONLINE-CH2-WEIGHTED-IDENTITY-20261011.json']=dump(manifest)
assert len(changes)==8
rows=[]
for f,b in changes.items():
 before=inputs.get(f);assert before is not None or not (ROOT/f).exists()
 put(OUT/'after'/f,b)
 diff=''.join(difflib.unified_diff((before or b'').decode('utf-8').splitlines(True),b.decode('utf-8').splitlines(True),fromfile=f+' BEFORE',tofile=f+' PROPOSED'))
 put(OUT/'diffs'/(f.replace('/','__')+'.diff'),diff.encode('utf-8'))
 rows.append({'path':f,'before_sha256':sha(before) if before is not None else None,'proposed_sha256':sha(b),'snapshot':'after/'+f})
for f,b in inputs.items():assert raw(ROOT/f)==b,'input changed during generation: '+f
report={'status':'draft only; no apply operation exists','approved_plan_sha256':PLAN_SHA,'helper_sha256':sha(raw(Path(__file__))),'snapshot_inputs':{f:sha(b) for f,b in inputs.items()},'original_plan_inputs':len(plan['input_raw_sha256']),'rows':rows,'invariants':{'all_original_inputs_unchanged':True,'old_parsed_objects_unchanged_except_named_appends':True,'manifest_schema2_valid':True,'affected_files_exact_protected_only':True,'production_declarations_exactly_two':True,'canonical_writes':False,'canary_acceptance':'accepted-candidate-canary-BODY-only; apply unavailable','registry_old_object_preservation':'must be checked on actual later generated registry; not claimed from JSON proposal'},'pending':['Distinct exact integration review and real combined gates','Later generated registry old-object preservation and rendered link inspection'],'bound_reviews':expected,'actual_VALUE_selected_parents':{scalar:['Finset.sum_range_by_parts',"Finset.sum_range_sub'"],distance:[scalar]}}
put(OUT/'invariant-report-v1.json',dump(report));print(json.dumps(report,indent=2))
