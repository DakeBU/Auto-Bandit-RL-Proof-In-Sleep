import copy,hashlib,json,subprocess
from pathlib import Path
from datetime import datetime,timezone
DOC=Path('docs/contracts/online-ch2-b4-finite-identity-v1')
RUN=Path('runs/online-ch2-b4-finite-identity-20261011')
CORE=Path('BanditRLProof/OnlineCumulativePotential.lean')
TEST=Path('Tests/OnlineCumulativePotentialCanary.lean')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def row(p):return {'path':p.as_posix(),'sha256':sha(p),'bytes':p.stat().st_size}
def put(p,b):
 p.parent.mkdir(parents=True,exist_ok=True)
 with p.open('xb') as f:f.write(b)
def js(p,j):put(p,(json.dumps(j,ensure_ascii=False,indent=2)+'\n').encode())
def git(*a):return subprocess.check_output(['git',*a]).decode().strip()
assert git('rev-parse','HEAD')=='cb4fe8ec8b979a698c31d3ebf5a350ac7242a66a'
assert git('status','--porcelain')=='?? Tests/OnlineCumulativePotentialCanary.lean'
assert sha(CORE)=='61c811c0b1f941ec22ac41f64e555a0e4d4d8dc32b8145ea53808dbdc0fc17da'
assert sha(TEST)=='a3f7a41bf1ddd25a4a623c865c028e029af267132faaeef9c70f9d28e3a30a8f'
for name,key in [('leaf-freeze-receipt-v1.json','frozen_inputs'),('canary-freeze-receipt-v1.json','frozen_inputs'),('precanary-preparation-addendum-v1.json','added_inputs')]:
 for r in json.loads((DOC/name).read_bytes())[key]:assert sha(r['path'])==r['sha256']
base=Path('tmp/online-ch2-b4-finite-identity-canary-core-20261011')
j=json.loads((base/'artifact-manifest-v1.json').read_bytes())
for r in j['rows']:assert sha(base/r['path'])==r['sha256'] and (base/r['path']).stat().st_size==r['bytes']
assert sha(Path('tmp/online-ch2-b4-finite-identity-canary-body-review-20261011/fresh-canary-body-review-v1.json'))=='1547b91ce76afe56c7c7a54be446887b8058fb071e4ddb32e4e48547bf33b8f3'
proposal=Path('tmp/online-ch2-b4-finite-identity-integration-proposal-v3-20261011/proposal-v3.json')
assert sha(proposal)=='417bee256fbabcc0862067fdf4c4bfdddf857b628dd06aa9b380ea5e9712ea96'
reviews=[]
for p in Path('tmp/online-ch2-b4-finite-identity-integration-review-20261011').glob('*.json'):
 v=json.loads(p.read_bytes())
 if '417bee256fbabcc0862067fdf4c4bfdddf857b628dd06aa9b380ea5e9712ea96' in json.dumps(v) and str(v.get('verdict','')).startswith('accepted') and not v.get('blocking_repairs',[]):reviews.append(p)
assert len(reviews)==1,'Exact V3 independent reader approval required'
ports=[]
for suffix,label in [
 ('precanary-v2-20261011/context-v2','actual-precanary-v2'),('precanary-v2-review-20261011','independent-precanary-v2'),
 ('canary-body-authorization-20261011','canary-authorization'),('canary-core-20261011','canary-core'),
 ('canary-body-review-20261011','independent-canary-body'),('integration-proposal-20261011','reader-proposal-v1'),
 ('integration-proposal-v2-20261011','reader-proposal-v2'),('integration-proposal-v3-20261011','reader-proposal-v3'),
 ('integration-review-20261011','independent-integration'),('integration-metadata-20261011','integration-metadata-drafts'),
 ('precanary-addendum-commit-20261011','actual-precanary-addendum-commit')]:
 src=Path('tmp/online-ch2-b4-finite-identity-'+suffix)
 for p in sorted(src.rglob('*')):
  if not p.is_file():continue
  q=RUN/label/p.relative_to(src);put(q,p.read_bytes())
  ports.append({'original':p.as_posix(),'destination':q.as_posix(),'sha256':sha(p),'bytes':p.stat().st_size})
 put(RUN/label/'.gitattributes',b'* -text\n* whitespace=cr-at-eol\n*.raw -diff\n*.olean -diff\n')
baseline=Path('tmp/online-ch2-prescient-euclidean-site-20261011-v1/books/registry.json')
registry=json.loads(baseline.read_bytes());assert len(registry['nodes'])==11104
q=RUN/'integration-baseline/previous-registry-v1.json';put(q,baseline.read_bytes())
ports.append({'original':baseline.as_posix(),'destination':q.as_posix(),'sha256':sha(baseline),'bytes':baseline.stat().st_size})
js(RUN/'exact-canary-and-integration-port-manifest-v1.json',{'UTC':datetime.now(timezone.utc).isoformat(),'rows':ports,
 'all_exact_bytes':all(Path(r['original']).read_bytes()==Path(r['destination']).read_bytes() for r in ports),
 'boundary':'Exact earlier ignored executions/reviews/proposals, original namespaces unchanged. No contemporaneous RUN claim.',
 'previous_registry_nodes':11104})
proposal_json=json.loads(proposal.read_bytes());preservation=[]
for name,patches in proposal_json['patches'].items():
 p=Path(name);before=p.read_bytes();original=json.loads(before);j=copy.deepcopy(original)
 expected=proposal_json['input_raw_sha256'][name];assert hashlib.sha256(before).hexdigest()==expected
 for patch in patches:
  assert patch['op']=='add' and patch['path'].endswith('/-')
  obj=j
  for part in patch['path'].split('/')[1:-1]:obj=obj[int(part)] if isinstance(obj,list) else obj[part]
  assert isinstance(obj,list);obj.append(patch['value'])
 restored=copy.deepcopy(j)
 for patch in reversed(patches):
  obj=restored
  for part in patch['path'].split('/')[1:-1]:obj=obj[int(part)] if isinstance(obj,list) else obj[part]
  assert obj.pop()==patch['value']
 assert restored==original
 put(RUN/'integration-baseline'/p.name,before)
 p.write_bytes((json.dumps(j,ensure_ascii=False,indent=2)+'\n').encode())
 preservation.append({'path':name,'before_sha256':hashlib.sha256(before).hexdigest(),'after_sha256':sha(p),'removing_only_new_appends_recovers_all_old_parsed_objects':True})
for name,line in [('BanditRLProof.lean','import BanditRLProof.OnlineCumulativePotential'),('Tests.lean','import Tests.OnlineCumulativePotentialCanary')]:
 p=Path(name);b=p.read_bytes();assert line.encode() not in b
 p.write_bytes(b.rstrip(b'\r\n')+b'\n'+line.encode()+b'\n')
metadata=RUN/'integration-metadata-drafts'
manifest=json.loads((metadata/'contribution-manifest-draft-v2.json').read_bytes())
canary_decls=['BanditRL.OnlineCumulativePotentialCanary.finite_identity_one_round_positive_gap','BanditRL.OnlineCumulativePotentialCanary.finite_identity_two_round_terminal_splice']
boundary='Only one finite-real corrected algebra subclause and its two concrete public canaries are locally compiled and independently BODY-reviewed. Read combined gate, final acceptance and reader status from separate actual receipts in this RUN; focused evidence does not replace them. Full EReal adapter, actual optimistic-FTRL/BTRL producer, ghost attainment, support, stability, Young and both corrected whole7.47/15.31 remain OPEN. Seven Chapter2 containers and six future claims remain open; Chapter2 partial,accepted=false,complete proof denominator=null; Chapters1-16 Goal ACTIVE. Unmerged/unpublished; no main/live/PURIFIED/native whole-loop claim.'
manifest['target']=manifest['target'].split('DRAFT metadata, not applied.')[0]+boundary
manifest['truth_boundary']=boundary
manifest['verification']['focused_checks']=[s for s in manifest['verification']['focused_checks'] if 'final Test file/evidence bindings pending' not in s]
manifest['reuse_plan']['known_consumers']=canary_decls
manifest['reuse_plan']['planned_consumers']=['Future finite corrected optimistic-FTRL and BTRL accounting adapters; not implemented.']
manifest['semantic_roundtrip']['remaining_semantic_delta']=manifest['semantic_roundtrip']['remaining_semantic_delta'].replace('Canary HEADER reviews do not imply accepted canary BODY.','Both exact-header canaries have separate bounded BODY acceptance; no whole algorithm endpoint is supplied.')
manifest['verification']['focused_checks'] += [str(TEST)+' SHA256 '+sha(TEST),str(RUN/'canary-core/canary-core-report-v1.json')+' SHA256 '+sha(RUN/'canary-core/canary-core-report-v1.json'),str(RUN/'independent-canary-body/fresh-canary-body-review-v1.json')+' SHA256 '+sha(RUN/'independent-canary-body/fresh-canary-body-review-v1.json')]
manifest['verification']['independent_review']='Production and both public canary BODY candidates independently accepted. Reader three-append plan and timely V3 status reviewed. Fresh shared root/Tests/full harness, current contributor/process gates, official site/structural/reader QA and bounded FINAL acceptance remain required in this RUN.'
manifest['verification']['bandit_check']='Actual clean committed candidate root/Tests/full-harness receipts and bounded FINAL acceptance are recorded separately in this RUN; focused tests do not substitute for these gates.'
manifest['verification']['site_build']='Actual plain preflight and Lean-verified build after successful same-candidate full harness are recorded separately in this RUN.'
manifest['verification']['site_check']='Actual official check, old-object/registry preservation and isolated local reader pixel review are recorded separately in this RUN; no live verification claim.'
manifest['progress_updates']['teaching_route']='updated: one corrected finite-real identity card, one declaration-bound lesson and one module glob; all pre-existing parsed objects retained.'
manifest['progress_updates']['results_ledger']='updated: production1/canary2 independently reviewed local candidates; whole parent/container remains open. Fresh combined and final acceptance evidence are separate in this RUN.'
manifest['learning_contract']['salvage']['reason']+=' Canary time-binder annotation failure and pre-canary ZIP governance omission are retained as implementation/environment repairs, with exact earlier receipts. All old mathematical targets retained.'
manifest['learning_contract']['reader_backpressure']['exposition_evidence']='Reviewed reader V3 successor in '+str(RUN/'reader-proposal-v3/proposal-v3.json')+'; actual render/Exposition Seal require separate current evidence. Planned reader-debt budget0 is not measured acceptance.'
manifest['learning_contract']['salvage']['promoted_fragments']+=canary_decls
js(Path('research-wiki/contribution-contracts/online-ch2-b4-finite-identity-20261011.json'),manifest)
digest=json.loads((metadata/'proof-digestion-draft-v1.json').read_bytes())
digest['status']='Integrated local production/canary candidates; fresh combined/reader/final acceptance still required'
digest['UTC']=datetime.now(timezone.utc).isoformat()
digest['canary_evidence']={'declarations':canary_decls,'Test':row(TEST),'report':row(RUN/'canary-core/canary-core-report-v1.json'),'independent_BODY_review':row(RUN/'independent-canary-body/fresh-canary-body-review-v1.json'),'first_conjunct_actual_core_consumers':True}
digest['purification']['canonicalization']='One shared production module and root import, two genuine concrete Test consumers and Test-root import. Final purification/exposition require separate audit.'
digest['role_bindings']['evidence']=str(RUN/'integration-metadata-drafts/input-bindings-v1.json')+' plus current canary report/review bindings above.'
digest['remaining']='Only the finite-real corrected algebra subclause and its two genuine Test witnesses are locally compiled and BODY-reviewed. Fresh complete gates/final acceptance/Exposition Seal remain required. Full EReal/actual producers/ghost attainment/support/stability/Young and both corrected source parents remain OPEN;7requiredcontainers/6futureclaims/C2partial/GoalACTIVE. Unmerged/unpublished.'
digest.pop('no_BODY_or_pp_proofs_read',None)
digest['exposure']={'source_only_draft_author_no_BODY_read':True,'stabilizing_parent':'Inspected production and Test source BODY plus independent reports; no claim of source-blindness.'}
js(DOC/'proof-digestion-record-v1.json',digest)
p=Path('MANIFEST.md');b=p.read_bytes()
addition='\n\n### B4 finite-real cumulative regret identity\n\n`BanditRL.OnlineCumulativePotential.finite_regret_identity` is a locally compiled and independently BODY-reviewed finite-real corrected algebra subclause near Orabona v10 Theorem7.47 (PDF141-142), related to the Theorem15.31 terminal repair (PDF278-279). It retains the final comparator regularizer minus initial played regularizer, within-potential sum, signed interior drift and arbitrary terminal gap. Two independently reviewed public canaries actually specialize the same core. No optimizer/actual algorithm/EReal performance endpoint is asserted. Fresh shared root/Tests/full-harness/site and final acceptance evidence are separate in `runs/online-ch2-b4-finite-identity-20261011`. Full EReal/producer/attainment/support/stability/Young and both corrected parent endpoints remain open. Chapter2 remains partial:7requiredcontainers/6futureclaims,accepted=false,complete proof denominator=null; Chapters1-16 Goal ACTIVE. Unmerged and unpublished.\n'
assert b'### B4 finite-real cumulative regret identity' not in b;p.write_bytes(b+addition.encode())
js(RUN/'integration-application-v1.json',{'UTC':datetime.now(timezone.utc).isoformat(),'reader_proposal':row(RUN/'reader-proposal-v3/proposal-v3.json'),'preservation':preservation,
 'source_core':row(CORE),'canary_Test':row(TEST),'source_inventory_unchanged_sha256':sha('docs/contracts/online-ch2-complete-target-freeze-v1/effective-targets-frozen-v3.2.json'),
 'root_imports_added':True,'required_open_containers':7,'future_claims_open':6,'Chapter2':'partial','Goal':'ACTIVE','main_live_updated':False,'full_gates':'pending on next clean committed candidate'})
put(RUN/'prepared/integrate-b4-finite-identity-v1.py',Path(__file__).read_bytes())
print(json.dumps({'exact_ports':len(ports),'core':sha(CORE),'Test':sha(TEST),'applied_reader_appends':len(preservation),'combined_gates':'pending'}))
