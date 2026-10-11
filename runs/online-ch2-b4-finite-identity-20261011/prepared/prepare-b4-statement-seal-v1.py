import hashlib, json, subprocess
from datetime import datetime, timezone
from pathlib import Path

ROOT=Path.cwd()
DOC=Path('docs/contracts/online-ch2-b4-finite-identity-v1')
RUN=Path('runs/online-ch2-b4-finite-identity-20261011')
def sha(b): return hashlib.sha256(b).hexdigest()
def now(): return datetime.now(timezone.utc).isoformat()
def git(*args): return subprocess.check_output(['git',*args]).decode().strip()
def put(p,b):
 p=Path(p);p.parent.mkdir(parents=True,exist_ok=True)
 assert not p.exists(),str(p)
 p.write_bytes(b)
def js(p,o):put(p,(json.dumps(o,ensure_ascii=False,indent=2)+'\n').encode())
def row(p):
 p=Path(p);b=p.read_bytes();return {'path':p.as_posix(),'sha256':sha(b),'bytes':len(b)}
assert git('rev-parse','HEAD')=='b8a4b13ca96709b1adff0d1907814dc3d3d76cc8'
assert git('branch','--show-current')=='codex/research-online-ch2-b4-finite-identity'
assert not git('status','--porcelain')
assert not Path('BanditRLProof/OnlineCumulativePotential.lean').exists()
assert not Path('Tests/OnlineCumulativePotentialCanary.lean').exists()
ports=[]
for label,folder in [
 ('header-proposal','tmp/online-ch2-b4-finite-identity-proposal-20261011'),
 ('neutral-blind','tmp/online-ch2-b4-finite-identity-blind-20261011'),
 ('source-header-topology','tmp/online-ch2-b4-finite-identity-source-review-20261011'),
 ('independent-source-topology','tmp/online-ch2-b4-finite-identity-topology-review-20261011'),
 ('header-elaboration','tmp/online-ch2-b4-finite-identity-formalizer-20261011'),
 ('preceding-prescient-delivery','tmp/online-ch2-prescient-euclidean-pr-delivery-current-20261011')]:
 src=Path(folder)
 for p in sorted(src.rglob('*')):
  if not p.is_file():continue
  q=RUN/label/p.relative_to(src)
  put(q,p.read_bytes());ports.append({'original':p.as_posix(),'destination':q.as_posix(),'sha256':sha(p.read_bytes()),'bytes':p.stat().st_size})
source_pixels=[]
for n in [141,142,278,279]:
 p=Path('tmp/online-lookahead-terminal-independent-review-20261011')/('page-%s.png'%n)
 q=RUN/'source-originals'/p.name;put(q,p.read_bytes())
 ports.append({'original':p.as_posix(),'destination':q.as_posix(),'sha256':sha(p.read_bytes()),'bytes':p.stat().st_size})
 source_pixels.append(dict(row(q),pdf_page_1based=n,printed_page=n-12,parent_personally_viewed=True))
put(RUN/'prepared'/'prepare-b4-statement-seal-v1.py',Path(__file__).read_bytes())
js(RUN/'exact-input-port-manifest-v1.json',{'UTC':now(),'rows':ports,'all_exact_bytes':all(Path(x['original']).read_bytes()==Path(x['destination']).read_bytes() for x in ports),'self_excluded':True,'chronology':'Copies of actual earlier ignored evidence; original receipts retain original locations. No contemporaneous execution in RUN is claimed.'})
put(RUN/'.gitattributes',b'* -text\n')
put(DOC/'.gitattributes',b'* -text\n')
header=Path('tmp/online-ch2-b4-finite-identity-proposal-20261011/neutral-proposed-header-v1.txt').read_bytes()
assert sha(header)=='92e0dcfac53595e35b68bfd8083c09640d06da809355ab02ec4eb4b007b0bd67'
put(DOC/'neutral-frozen-header-v1.txt',header)
source_review=json.loads((RUN/'source-header-topology/source-header-review-v1.json').read_bytes())
invpath=Path('docs/contracts/online-ch2-complete-target-freeze-v1/effective-targets-frozen-v3.2.json')
inv=json.loads(invpath.read_bytes());assert sha(invpath.read_bytes())=='61cf1901a632aeee35ee71511ba53b115ae0958649ea78b786536a4404684ba1'
parents=[]
for o in inv['effective_targets']:
 if o['target_id'] in ['repair:7.47-terminal','repair:15.31-terminal']:
  parents.append({'target_id':o['target_id'],'row_sha256':sha(json.dumps(o,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()),'row':o})
memory=json.loads(Path('runs/process_memory.json').read_bytes())
consult=[]
for e in memory['entries']:
 checks=[]
 for v in e.get('evidence',[]):
  p=Path(v['file']);needle=v['needle'];assert p.exists() and needle in p.read_text(encoding='utf-8'),(e['id'],v)
  checks.append({'path':p.as_posix(),'sha256':sha(p.read_bytes()),'needle':needle,'found':True})
 consult.append({'id':e['id'],'process_only':True,'evidence_checks':checks,'application':'Keep atomic inputs, retain mathematical targets after tooling/API failures, preserve verified fragments, and leave scheduler defaults unchanged.'})
js(RUN/'process-memory-consultation-v1.json',{'UTC':now(),'memory':row('runs/process_memory.json'),'control_plane_math_authority':False,'consulted':consult,'scheduler_defaults_changed':False})
governance=['AGENTS.md','CONTRIBUTING.md','docs/contributor-codex-contract.md','docs/theorem-publication-protocol.md','docs/proof-digestion-protocol.md','docs/evidence-routed-memory-protocol.md','docs/openai-math-assimilation-protocol.md','research-wiki/openai-math-2026-intake.json','runs/process_memory.json','.agents/skills/bandit-substantive-advance/SKILL.md','.agents/skills/bandit-semantic-roundtrip/SKILL.md','.agents/skills/bandit-lean-formalization/SKILL.md']
sc={
 'UTC':now(),'status':'STATEMENT-SEAL PROPOSAL; independent parent-contract review pending; NO BODY AUTHORIZATION',
 'task':'ONLINE-CH2-B4-FINITE-IDENTITY-20261011','requested_model_effort':'GPT-6 Astra / medium; runtime not independently attested',
 'source':{'title':'Online Learning: A Modern Introduction Using Convex Optimization','author':'Francesco Orabona','arxiv':'1912.13213v10','pdf_sha256':source_review['source_pdf']['sha256'],'anchors':['Theorem7.47 proof terminal accounting (printed129-130)','Theorem15.31 terminal convention (printed266-267)'],'original_pixels':source_pixels},
 'source_inventory':row(invpath),'parent_fingerprints':parents,
 'sole_leaf':{'id':'repair:7.47-terminal/finite-real-identity','parent_status':'Both whole parent repair records remain OPEN; only this necessary algebra subclause may be accepted after all gates.','header':row(DOC/'neutral-frozen-header-v1.txt'),'module':'BanditRLProof/OnlineCumulativePotential.lean','declaration':'BanditRL.OnlineCumulativePotential.finite_regret_identity','public_theorems':1,'public_definitions':0},
 'semantic_roundtrip':{'formalizer':'/root/b4_finite_identity_formalizer; original proposed header prepared by /root/adaptive_formalizer','fresh_blind_actor':'/root/b4_finite_identity_blind','source_reviewer':'/root/adaptive_decoder','independent_topology_reviewer':'/root/adaptive_reviewer','blind':row(RUN/'neutral-blind/fresh-blind-v1.json'),'source_header':row(RUN/'source-header-topology/source-header-review-v1.json'),'blind_binding':row(RUN/'source-header-topology/fresh-blind-binding-v1.json'),'accepted_delta':'Arbitrary carrier and total real-valued functions expose finite-value bookkeeping only. Full EReal/algorithm transport is still mandatory and OPEN.'},
 'atomic_binder_audit':source_review['atomic_binder_audit'],'local_lets':source_review['local_lets'],'expanded_project_assumption_bundles':[],'EXCESS':[],
 'index_mapping':json.loads((RUN/'header-proposal/header-proposal-v1.json').read_bytes())['index_mapping'],
 'source_topology':{'proposal':row(RUN/'source-header-topology/topology-proposal-v2.json'),'independent_accepted_review':row(RUN/'independent-source-topology/fresh-independent-source-topology-review-v2.json'),'historical_v1_repair':row(RUN/'independent-source-topology/fresh-independent-source-topology-review-v1.json'),'source_nodes':29,'exclusions_retained':4,'verified_edges':0,'chronology':'SOURCE topology extracted and independently repaired/accepted before any B4 proof BODY. Source narrative, corrected obligations and implementation graph stay distinct.'},
 'elaboration':{'report':row(RUN/'header-elaboration/preparation-report-v1.json'),'actual_original_header_receipt_v2':row(RUN/'header-elaboration/header-original-context-elaboration-v2.json'),'before_context':row(RUN/'header-elaboration/context-before-v2.json'),'after_context':row(RUN/'header-elaboration/context-after-v2.json'),'result':'Original full header elaborates as Prop definition, actual Lean exit0. This supplies no theorem proof. Both original imports frozen; minimal context advisory not applied.'},
 'reuse_plan':{'decision':'new_shared','search_evidence':str(RUN/'header-proposal'),'search_extent':'Five actual successful bounded retrievals including broad declaration list; no exhaustive absence claim. Standard Mathlib finite sums proposed. Existing weighted scalar identity and finite-simplex FTRL contracts differ.','two_planned_consumers':['corrected optimistic FTRL finite terminal accounting','corrected BTRL finite terminal accounting'],'no_duplicate_wrapper':True,'pins_unchanged':True},
 'proof_route':'One serial algebra proof route using standard finite-sum telescoping; no extra public optimizer, gradient, norm, finite-value producer, desired-regret or algorithm hypotheses. No helper definitions or second Lean project.',
 'learning':{'control_plane_math_authority':False,'process_memory':row(RUN/'process-memory-consultation-v1.json'),'parallelism':'serial mathematical construction with distinct independent semantic/topology audit actors; not multiple sufficient mathematical routes','failure_history':['Independent topology v1 REPAIR T1-T4 retained; v2 repaired/accepted.','First header-probe console Unicode failure after Lean exit0 retained as tooling evidence; v2 actual stable replay0.','Repeated-hint sharp source completion ordinary rational counterevidence retained; only its invalid cancellation is SOURCE_INVALID, not the virtual-repeat operation.'],'salvage':'All proposal/failed topology/headers/receipts retained; no fragment or directory discarded.','purification':'pending; never infer PURIFIED from PROVED, PR or merge','exposition_seal':'pending until actual local reader/gates/review'},
 'reader_plan':'One coherent identity card and adjacent declaration-bound lesson: source anchor, variables/indices, full signed equality, natural-language telescoping proof, exact Lean folded, source-vs-Lean delta, real dependencies, terminal-gap correction and remaining red boundary. Preserve all old parsed Book objects.',
 'graph_plan':{'Source Proof Graph':'Reviewed source-only v2 with original/corrected separate and OPEN analytic obligations.','Lean Graph':'One prospective canonical algebra node; actual TYPE/VALUE occurrence evidence only after compilation, no necessity claim.','Compressed spine':'Single finite cumulative-potential telescope; implementation bookkeeping compressed with full drill-down.','Overview':'Partial chapter remains partial; no whole parent/container completion.','Functor Hypergraph':'none-found-with-reason: this bookkeeping identity alone does not establish a transport or new discovery.'},
 'remaining_mandatory':['Whole corrected7.47 actual hinted producer, proper/finiteness/EReal adapter, zero-hint ghost attainment/support qualification, stability and Young bound.','Whole corrected15.31 actual minima, support/strong-convexity, final repeated-state convention and interior movement bound.','B1-B7 and all seven required containers/six future claims remain; no target removed.'],
 'chapter_state':{'required_open_forward_containers':7,'future_claims_open':6,'chapter2_status':'partial','chapter2_accepted':False,'mandatory_count':None,'Goal':'ACTIVE'},
 'governance_RAW_context':[row(p) for p in governance],
 'delivery_parent':{'prescient_PR':'https://github.com/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/pull/221','remote_delivery_HEAD':'b8a4b13ca96709b1adff0d1907814dc3d3d76cc8','verification':row(RUN/'preceding-prescient-delivery/actual-PR221-delivery-verification-current-v2.json'),'state':'OPEN DRAFT unmerged/unpublished; CI running at recorded snapshot; no main/live update'},
 'gates_required':['independent contract freeze audit','committed clean preproof context and independent verification plus explicit parent BODY authorization','exact header fence + focused compilation + TYPE/VALUE export + axiom audit','distinct production BODY review','complete canary headers/blind/source freeze after production acceptance and before canary BODY','same canonical root/Tests/full harness','schema3 contributor contract/process-memory gates','actual source snapshot/RAW-ZIP governance binding','site build/check/structural preservation and original-pixel reader review','independent final bounded acceptance','commit/push/reviewable PR delivery; chapter/global remain OPEN'],
 'authorization':'This proposal does not authorize BODY. After independent freeze audit, parent seals/commits exact inputs, captures clean preproof context and obtains independent verification before explicit BODY authorization.'}
js(DOC/'source-contract-proposal-v1.json',sc)
print('prepared',len(ports),'exact source/evidence ports; contractSHA',sha((DOC/'source-contract-proposal-v1.json').read_bytes()))
