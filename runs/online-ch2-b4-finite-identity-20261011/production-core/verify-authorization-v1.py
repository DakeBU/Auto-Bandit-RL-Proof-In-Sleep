from pathlib import Path
import hashlib,json,subprocess,datetime
root=Path('E:/ABRL/worktrees/research-online-book'); out=root/'tmp/online-ch2-b4-finite-identity-core-20261011'; out.mkdir(exist_ok=True)
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def put(n,s):
 b=s.encode('utf-8') if isinstance(s,str) else s
 with (out/n).open('xb') as f:f.write(b)
auth=root/'tmp/online-ch2-b4-finite-identity-body-authorization-20261011/parent-authorization-v1.json'
assert sha(auth)=='d2ddf2ec4aa1aba8186125b6dcbf81e9d8fa3155c9cfbb21eab323ab1197db29'
a=json.loads(auth.read_text()); checks=[(auth,a and sha(auth))]
for p,k in [('docs/contracts/online-ch2-b4-finite-identity-v1/leaf-freeze-receipt-v1.json','seal_sha256'),('docs/contracts/online-ch2-b4-finite-identity-v1/neutral-frozen-header-v1.txt','header_sha256'),('tmp/online-ch2-b4-finite-identity-preproof-20261011/capture-v3/receipt.json','actual_preproof_context_sha256'),('tmp/online-ch2-b4-finite-identity-preproof-review-20261011/fresh-independent-preproof-context-review-v1.json','independent_preproof_review_sha256')]:
 assert sha(root/p)==a[k];checks.append((root/p,a[k]))
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=str(root)).decode().strip()==a['HEAD']
assert subprocess.check_output(['git','branch','--show-current'],cwd=str(root)).decode().strip()==a['branch']
assert not subprocess.check_output(['git','status','--porcelain'],cwd=str(root)).strip()
assert not (root/'BanditRLProof/OnlineCumulativePotential.lean').exists()
seal=json.loads((root/'docs/contracts/online-ch2-b4-finite-identity-v1/leaf-freeze-receipt-v1.json').read_text())
rows=json.loads((root/'tmp/online-ch2-b4-finite-identity-preproof-20261011/capture-v3/source-RAW-before.json').read_text())
for r in seal['frozen_inputs']+rows:
 assert sha(root/r['path'])==r['sha256'],r['path']
put('authorization-verified-v1.json',json.dumps(dict(UTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),HEAD=a['HEAD'],branch=a['branch'],clean=True,core_absent=True,frozen_rows_verified=len(seal['frozen_inputs']),preproof_rows_verified=len(rows),hashes={str(p):h for p,h in checks}),indent=2)+'\n')