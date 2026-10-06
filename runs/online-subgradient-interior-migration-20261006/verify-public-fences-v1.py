"""Three actual native guards for exact frozen canonical public headers."""
from pathlib import Path
import hashlib,json,subprocess,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header
run=Path(__file__).parent;contract=Path('docs/contracts/online-subgradient-interior-migration-v1');load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'));sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
freeze=load(run/'draft-freeze-v1.json');headers=load(contract/'headers.json');public=Path('BanditRLProof/OnlineSubgradientInterior.lean')
assert (run/'original-OnlineSubgradientInterior.lean.txt').read_bytes() in public.read_bytes()
for group in ['fixed_shared_modules','fixed_old_canary']:
 for p,h in freeze[group].items():assert sha(p)==h,p
assert Path('Tests.lean').read_bytes().startswith((run/'original-Tests.lean.txt').read_bytes())
for n,row in headers.items():
 actual=lean_declaration_header(public,n);assert actual==row['statement'] and hashlib.sha256(actual.encode()).hexdigest()==freeze['headers'][n]
 fp=run/'native-public-fences'/(n+'.json');assert not fp.exists()
 subprocess.run([sys.executable,'-X','utf8',str(run/'run-command.py'),'public-fence-v1-'+n,sys.executable,'-X','utf8','tools/bandit.py','statement-fence','--declaration','BanditRL.OnlineConvex.'+n,'--file',str(public),'--output',str(fp)],check=True)
 assert load(fp)['statement_hash']==freeze['headers'][n]
 subprocess.run([sys.executable,'-X','utf8',str(run/'run-command.py'),'safe-public-v1-'+n,sys.executable,'-X','utf8','tools/bandit.py','safe-verify','--fence',str(fp),'--lean-file',str(public),'--lean-file','Tests/OnlineSubgradientInteriorCanary.lean','--lean-file','Tests/OnlineRelativeSubgradientCanary.lean'],check=True)
for n,row in load(contract/'canary-headers-v1.json').items():assert lean_declaration_header(Path('Tests/OnlineRelativeSubgradientCanary.lean'),n)==row['statement']
o=run/'public-safe-guard-audit-v1.json';assert not o.exists();o.write_text(json.dumps(dict(status='passed',guards=3,unchanged_headers=freeze['headers'],old_module_bytes_contiguous=True,old_canary_fixed=True,Tests_original_raw_prefix=True,new_canary_headers_unchanged=True,guard_is_not_compilation=True),indent=2)+'\n',encoding='utf-8')
print('Three native guards passed; actual Lean compilation remains separate evidence.')
