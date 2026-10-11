import hashlib,json,subprocess
from pathlib import Path
from datetime import datetime,timezone
DOC=Path('docs/contracts/online-ch2-b4-finite-identity-v1')
RUN=Path('runs/online-ch2-b4-finite-identity-20261011')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def put(p,b):
 p.parent.mkdir(parents=True,exist_ok=True)
 with p.open('xb') as f:f.write(b)
def row(p):return {'path':p.as_posix(),'sha256':sha(p),'bytes':p.stat().st_size}
def git(*args):return subprocess.check_output(['git',*args]).decode().strip()
assert git('rev-parse','HEAD')=='40c2f30f7cee38c9d2f716ffdac18a459a5af25a'
assert not Path('Tests/OnlineCumulativePotentialCanary.lean').exists()
assert sha('BanditRLProof/OnlineCumulativePotential.lean')=='61c811c0b1f941ec22ac41f64e555a0e4d4d8dc32b8145ea53808dbdc0fc17da'
src=Path('tmp/online-ch2-b4-finite-identity-canary-freeze-review-20261011')
j=json.loads((src/'fresh-independent-canary-freeze-review-v1.json').read_bytes())
assert j['verdict'].startswith('accepted') and not j.get('blocking_repairs',[])
ports=[]
for p in sorted(src.rglob('*')):
 if not p.is_file():continue
 q=RUN/'independent-canary-freeze'/p.relative_to(src);put(q,p.read_bytes())
 ports.append({'original':p.as_posix(),'destination':q.as_posix(),'sha256':sha(p),'bytes':p.stat().st_size})
put(RUN/'independent-canary-freeze/.gitattributes',b'* -text\n*.raw -diff\n')
put(RUN/'prepared/seal-b4-canaries-v1.py',Path(__file__).read_bytes())
put(RUN/'independent-canary-freeze-port-v1.json',(json.dumps({'rows':ports,'boundary':'Exact copied ignored independent review; original receipt paths retained.'},indent=2)+'\n').encode())
rows=[row(p) for base in [DOC,RUN] for p in sorted(base.rglob('*')) if p.is_file()]
rows.append(row(Path('BanditRLProof/OnlineCumulativePotential.lean')))
assert len(rows)==len({r['path'] for r in rows})
old=json.loads((DOC/'leaf-freeze-receipt-v1.json').read_bytes())
assert all(sha(r['path'])==r['sha256'] for r in old['frozen_inputs'])
seal={'UTC':datetime.now(timezone.utc).isoformat(),'decision':'CANARY STATEMENTS SEALED; explicit Test BODY authorization remains pending clean committed context and independent review',
 'pre_seal_HEAD':git('rev-parse','HEAD'),'branch':git('branch','--show-current'),
 'requested_model_effort':'GPT-6 Astra / medium; runtime not independently attested',
 'production_candidate_only':'accepted-local-candidate; finite-real equality, no whole B4/container/chapter closure',
 'frozen_inputs':rows,'independent_canary_freeze_review':row(RUN/'independent-canary-freeze/fresh-independent-canary-freeze-review-v1.json'),
 'Test_BODY_present':False,'Test_BODY_authorized':False,'prepared_checker':'prepared/check-b4-precanary-context-v2.py',
 'gate_recorder':'prepared/capture-gate-v1.py; unchanged generic recorder, selected active source RAW/ZIP only, historical RUN bound by clean HEAD and this seal',
 'current':{'Chapter2':'partial','accepted':False,'required_open_containers':7,'future_claims_open':6,'whole_B4':'OPEN','Goal':'ACTIVE','main_live_updated':False}}
put(DOC/'canary-freeze-receipt-v1.json',(json.dumps(seal,ensure_ascii=False,indent=2)+'\n').encode())
print(json.dumps({'seal_sha256':sha(DOC/'canary-freeze-receipt-v1.json'),'frozen_inputs':len(rows),'independent_review_sha256':sha(RUN/'independent-canary-freeze/fresh-independent-canary-freeze-review-v1.json')}))
