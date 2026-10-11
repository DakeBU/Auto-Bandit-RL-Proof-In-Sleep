from pathlib import Path
import hashlib,json,subprocess,sys
ROOT=Path(__file__).resolve().parents[2]
PY=sys.executable
NS='tmp/online-ch2-b4-strong-convex-growth-gates-20261011'
SITE='tmp/online-ch2-b4-strong-convex-growth-site-20261011-v1'
HELPER='runs/online-ch2-b4-finite-identity-20261011/prepared/capture-gate-v2.py'
assert hashlib.sha256((ROOT/HELPER).read_bytes()).hexdigest()=='bafe784fad8810f866105ffd19e3504f70ebf1e28949611549d584630a5b7ce8'
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT).decode().strip()=='cf1a424f2312e7c5b730717cf0a96d65837894bd'
assert not subprocess.check_output(['git','status','--porcelain=v1'],cwd=ROOT)
prior=json.loads((ROOT/'tmp/online-main-reconciliation-gates-20261011/full-harness-v5/receipt.json').read_text(encoding='utf-8'))
args=[PY,'-B','-X','utf8',HELPER,'--root',str(ROOT),'--run',NS]
for name in prior['owned_source']:
 if not name.startswith('docs/contracts/'):args+=['--owned-source',name]
for folder in prior['leaf_contract_roots']+['docs/contracts/online-ch2-b4-finite-identity-v1','docs/contracts/online-ch2-b4-strong-convex-growth-v1']:
 args+=['--leaf-contract',folder]
pc=[PY,'-B','-X','utf8']
gates=[('production-root-v1',['lake','build','BanditRLProof']),('shared-Tests-v1',['lake','build','Tests']),
 ('full-harness-v1',pc+['tools/bandit.py','check']),
 ('contributor-actual-main-base-v1',pc+['tools/check_contributor_contract.py','--base','4490854eea1d7e5b8ef224980e2c2d641a85df28']),
 ('process-memory-v1',pc+['tools/check_process_memory.py']),
 ('axiom-audit-v1',['lake','env','lean','docs/contracts/online-ch2-b4-strong-convex-growth-v1/combined-axiom-audit-probe-v1.lean']),
 ('site-preflight-v1',pc+['website/scripts/build_site.py','--output','tmp/online-ch2-b4-strong-convex-growth-site-preflight-20261011-v1']),
 ('site-build-v1',pc+['website/scripts/build_site.py','--lean-verified','--output',SITE]),
 ('site-check-v1',pc+['website/scripts/check_site.py','--output',SITE])]
summary=[]
for label,cmd in gates:
 print('START',label,flush=True)
 proc=subprocess.run(args+['--label',label,'--']+cmd,cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
 receipt=ROOT/NS/label/'receipt.json'
 if not receipt.exists():
  print(proc.stdout.decode('utf-8','replace'),proc.stderr.decode('utf-8','replace'),flush=True)
  raise RuntimeError('Recorder failed before receipt: '+label)
 r=json.loads(receipt.read_text(encoding='utf-8'))
 row={'label':label,'recorder_exit':proc.returncode,'actual_exit':r['actual_exit'],'capture_integrity_ok':r['capture_integrity_ok'],
  'receipt_sha256':hashlib.sha256(receipt.read_bytes()).hexdigest(),'HEAD':r['pre_git']['HEAD'],'RAW_files':r.get('full_RAW_inventory_files')}
 summary.append(row);print(json.dumps(row),flush=True)
 if proc.returncode or r['actual_exit']!=0 or not r['capture_integrity_ok']:
  print((receipt.parent/'stdout.raw').read_text(encoding='utf-8',errors='replace')[-9000:],flush=True)
  print((receipt.parent/'stderr.raw').read_text(encoding='utf-8',errors='replace')[-6000:],flush=True)
  raise RuntimeError('Actual gate failed; retained original evidence: '+label)
out=ROOT/NS/'parent-nine-gates-summary-v1.json'
with out.open('x',encoding='utf-8') as f:json.dump({'gates':summary,'source_HEAD':'cf1a424f2312e7c5b730717cf0a96d65837894bd','leaf_accepted':False,'Goal':'ACTIVE'},f,indent=2);f.write('\n')
print('ALL_NINE_ACTUAL_GATES_PASSED',flush=True)
