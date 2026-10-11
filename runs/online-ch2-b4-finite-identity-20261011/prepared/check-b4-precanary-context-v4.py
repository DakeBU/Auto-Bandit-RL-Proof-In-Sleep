"""Read-only pre-canary context check; external unchanged gate recorder captures full active source RAW/ZIP."""
import hashlib, json, subprocess
from pathlib import Path
ROOT=Path.cwd()
DOC=Path('docs/contracts/online-ch2-b4-finite-identity-v1')
RUN=Path('runs/online-ch2-b4-finite-identity-20261011')
SEAL=DOC/'canary-freeze-receipt-v1.json'
ADDENDUM=DOC/'precanary-preparation-addendum-v1.json'
CORE=Path('BanditRLProof/OnlineCumulativePotential.lean')
TEST=Path('Tests/OnlineCumulativePotentialCanary.lean')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def git(*args):return subprocess.check_output(['git',*args]).decode().strip()
def states():
 return {'HEAD':git('rev-parse','HEAD'),'branch':git('branch','--show-current'),
 'status':git('status','--porcelain'),'core_sha256':sha(CORE),'Test_exists':TEST.exists(),
 'mathlib_HEAD':git('-C','.lake/packages/mathlib','rev-parse','HEAD'),
 'mathlib_status':git('-C','.lake/packages/mathlib','status','--porcelain')}
before=states()
assert not before['status'] and not before['Test_exists']
assert before['branch']=='codex/research-online-ch2-b4-finite-identity'
assert before['core_sha256']=='61c811c0b1f941ec22ac41f64e555a0e4d4d8dc32b8145ea53808dbdc0fc17da'
assert before['mathlib_HEAD']=='5e932f97dd25535344f80f9dd8da3aab83df0fe6' and not before['mathlib_status']
seal_bytes_before=SEAL.read_bytes();seal_sha_before=hashlib.sha256(seal_bytes_before).hexdigest()
assert seal_sha_before=='7d69c7a32df454ab91324c7b2aeb120e6bc736847fc3c429695711e2678504e8'
seal=json.loads(seal_bytes_before);addendum_bytes=ADDENDUM.read_bytes();addendum=json.loads(addendum_bytes)
assert addendum['original_seal_sha256']==seal_sha_before
rows=seal['frozen_inputs']+addendum['added_inputs'];names=[r['path'] for r in rows]
required={(RUN/'independent-precanary-preparation-v2/fresh-independent-precanary-preparation-review-v2.json').as_posix(),CORE.as_posix(),(DOC/'canary-neutral-one-round-frozen-header-v1.txt').as_posix(),
 (DOC/'canary-neutral-two-round-frozen-header-v1.txt').as_posix(),(DOC/'canary-freeze-proposal-v1.json').as_posix(),
 (RUN/'independent-production-body/fresh-production-body-review-v1.json').as_posix(),
 (RUN/'independent-canary-freeze/fresh-independent-canary-freeze-review-v1.json').as_posix(),
 (RUN/'prepared/check-b4-precanary-context-v4.py').as_posix(),
 (RUN/'prepared/capture-gate-v2.py').as_posix()}
assert rows and len(names)==len(set(names)) and required<=set(names)
assert all(Path(r['path']).is_file() and sha(r['path'])==r['sha256'] and Path(r['path']).stat().st_size==r['bytes'] for r in rows)
actual={p.as_posix() for base in [DOC,RUN] for p in base.rglob('*') if p.is_file()}|{CORE.as_posix()}
assert actual==set(names)|{SEAL.as_posix(),ADDENDUM.as_posix()}
assert sha(__file__)==sha(RUN/'prepared/check-b4-precanary-context-v4.py')
check=json.loads((RUN/'independent-canary-freeze/fresh-independent-canary-freeze-review-v1.json').read_bytes())
assert check['verdict'].startswith('accepted') and not check.get('blocking_repairs',[])
preparation_review=json.loads((RUN/'independent-precanary-preparation-v2/fresh-independent-precanary-preparation-review-v2.json').read_bytes())
assert preparation_review['verdict'].startswith('accepted') and not preparation_review.get('blocking_repairs',[])
assert preparation_review['approved_checker_sha256']==sha(__file__)
assert preparation_review['approved_recorder_sha256']==sha(RUN/'prepared/capture-gate-v2.py')
old=json.loads((DOC/'leaf-freeze-receipt-v1.json').read_bytes())
assert all(sha(r['path'])==r['sha256'] for r in old['frozen_inputs'])
assert SEAL.read_bytes()==seal_bytes_before and sha(SEAL)==seal_sha_before
assert ADDENDUM.read_bytes()==addendum_bytes
assert all(sha(r['path'])==r['sha256'] and Path(r['path']).stat().st_size==r['bytes'] for r in rows)
actual_after={p.as_posix() for base in [DOC,RUN] for p in base.rglob('*') if p.is_file()}|{CORE.as_posix()}
assert actual_after==actual==set(names)|{SEAL.as_posix(),ADDENDUM.as_posix()}
after=states();assert before==after
print(json.dumps({'status':'PRECANARY_INPUTS_READY; no Test BODY','context':before,
 'canary_seal_sha256':sha(SEAL),'preparation_addendum_sha256':sha(ADDENDUM),'frozen_rows':len(rows),'old_statement_seal_rows':len(old['frozen_inputs']),
 'complete_own_contract_evidence_path_set_exact':True,'before_after_stable':True,
 'scope':'Finite-real identity canary only; whole B4/chapter/Goal remain OPEN. Active source RAW/ZIP is supplied by outer recorder; historical RUN is bound by clean committed HEAD and this exact seal.'}))
