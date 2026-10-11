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
assert subprocess.check_output(['git','rev-parse','HEAD']).strip()==b'46ff1cee7d4d8fd586063d29b7eeab93018ba08b'
assert not subprocess.check_output(['git','status','--porcelain']).strip()
assert not Path('Tests/OnlineCumulativePotentialCanary.lean').exists()
seal=DOC/'canary-freeze-receipt-v1.json';assert sha(seal)=='7d69c7a32df454ab91324c7b2aeb120e6bc736847fc3c429695711e2678504e8'
old=json.loads(seal.read_bytes())['frozen_inputs']
assert all(sha(r['path'])==r['sha256'] for r in old)
review=Path('tmp/online-ch2-b4-finite-identity-precanary-preparation-v2-review-20261011/fresh-independent-precanary-preparation-review-v2.json')
j=json.loads(review.read_bytes())
assert j['verdict'].startswith('accepted') and not j.get('blocking_repairs',[])
assert j['approved_checker_sha256']=='40e305c03fb97bdde62cb56fcf140a50fb43b2827905c8ea4b2a4a46938724fd'
assert j['approved_recorder_sha256']=='bafe784fad8810f866105ffd19e3504f70ebf1e28949611549d584630a5b7ce8'
ports=[];added=[]
for suffix,label in [
 ('precanary-preparation-v2-review-20261011','independent-precanary-preparation-v2'),
 ('precanary-20261011/context-v1','actual-precanary-v1-repair'),
 ('precanary-review-20261011','independent-precanary-v1-repair'),
 ('canary-freeze-commit-20261011','actual-canary-freeze-commit-v1-repair'),
 ('canary-freeze-commit-v2-20261011','actual-canary-freeze-commit-v2')]:
 src=Path('tmp/online-ch2-b4-finite-identity-'+suffix)
 for p in sorted(src.rglob('*')):
  if not p.is_file():continue
  q=RUN/label/p.relative_to(src);put(q,p.read_bytes());added.append(row(q))
  ports.append({'original':p.as_posix(),'destination':q.as_posix(),'sha256':sha(p),'bytes':p.stat().st_size})
 q=RUN/label/'.gitattributes';put(q,b'* -text\n*.raw -diff\n');added.append(row(q))
base=Path('tmp/online-ch2-b4-finite-identity-precanary-preparation-v2-20261011')
for p in sorted(base.glob('*.py')):
 q=RUN/'prepared'/p.name;put(q,p.read_bytes());added.append(row(q))
 ports.append({'original':p.as_posix(),'destination':q.as_posix(),'sha256':sha(p),'bytes':p.stat().st_size})
p=RUN/'prepared/prepare-b4-precanary-addendum-v1.py';put(p,Path(__file__).read_bytes());added.append(row(p))
p=RUN/'precanary-preparation-v2-port-manifest-v1.json'
put(p,(json.dumps({'rows':ports,'boundary':'Exact earlier ignored execution/repair/preparation receipts. Original namespaces retained. No historical record modified.'},indent=2)+'\n').encode());added.append(row(p))
assert not {r['path'] for r in old}&{r['path'] for r in added}
assert len(added)==len({r['path'] for r in added})
actual={p.as_posix() for base in [DOC,RUN] for p in base.rglob('*') if p.is_file()}|{'BanditRLProof/OnlineCumulativePotential.lean'}
assert actual=={r['path'] for r in old+added}|{seal.as_posix()}
j={'UTC':datetime.now(timezone.utc).isoformat(),'original_seal_sha256':sha(seal),'added_inputs':added,
 'scope':'Append-only preparation repair; original317 inputs and both canary declarations unchanged. Old capture lacked7 governance ZIP members, so rejected. RecorderV2 includes those7; checkerV4 binds original seal, independently accepted helper hashes, added inputs and complete own path set before/after.',
 'execution_target':'prepared/check-b4-precanary-context-v4.py','recorder':'prepared/capture-gate-v2.py',
 'authorization':'No Test BODY authorization. Fresh actual clean capture and independent review still required.',
 'failure_preservation':'Original CRLF diff diagnostics and command-local CR-aware check0 retained; RAW bytes never normalized. Original recorderV1 actual capture and all helper repair findings retained.',
 'chapter_state':'C2partial/wholeB4OPEN/7requiredcontainers+6futureclaimsOPEN/GoalACTIVE/mainliveunchanged'}
p=DOC/'precanary-preparation-addendum-v1.json';put(p,(json.dumps(j,indent=2)+'\n').encode())
print(json.dumps({'addendum_sha256':sha(p),'added_inputs':len(added),'original_inputs_unchanged':len(old)}))
