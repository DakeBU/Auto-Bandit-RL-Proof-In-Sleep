from pathlib import Path
import importlib.util,json,subprocess,sys,hashlib
sys.dont_write_bytecode=True
r=Path.cwd();p=r/'tmp/online-main-reconciliation-20261011/contributor-checker-candidate-v1';sp=importlib.util.spec_from_file_location('candidate',p/'tools/check_contributor_contract.py');m=importlib.util.module_from_spec(sp);sp.loader.exec_module(m);m.ROOT=r
base='f07aa9a2a5df241087ffab1c3579d1b59d8bf6f6'
rows=[('ONLINE-CONVEX-MIGRATION-20261005.json','OnlineConvexExtended.lean'),('ONLINE-CONVEX-MIGRATION-20261005.json','OnlineConvexExamples.lean'),('online-first-order-migration-20261005.json','OnlineConvexFirstOrder.lean'),('ONLINE-OGD-MIGRATION-20261005.json','OnlineGradientDescentVariable.lean'),('ONLINE-OGD-MIGRATION-20261005.json','OnlineGradientDescentSource.lean')]
results=[{'manifest':a,'source':b,'certificate':m.historical_row_certificate(base,'research-wiki/contribution-contracts/'+a,'BanditRLProof/'+b)} for a,b in rows]
x={'scope':'read-only development certificate probe; not actual contributor gate','HEAD':subprocess.check_output(['git','rev-parse','HEAD']).decode().strip(),'checker_sha256':hashlib.sha256((p/'tools/check_contributor_contract.py').read_bytes()).hexdigest(),'results':results,'all_five_certified':all(z['certificate'] for z in results)}
(p/'actual-five-row-development-probe-v2.json').write_bytes((json.dumps(x,indent=2)+'\n').encode());print(x['HEAD']);print(bool(x['all_five_certified']));sys.exit(not x['all_five_certified'])
