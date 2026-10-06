"""Nine native statement guards; byte/token checks remain separate from compilation."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header
run=Path(__file__).parent
contract=Path('docs/contracts/online-subgradient-sum-migration-v1')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'))
freeze=load(run/'draft-freeze-v1.json')
headers=load(contract/'headers.json')
public=Path('BanditRLProof/OnlineSubgradientSum.lean')
assert public.read_bytes()==(run/'original-OnlineSubgradientSum.lean.txt').read_bytes()
for group in ['fixed_shared_files','whole_old_canary']:
 for p,h in freeze[group].items():assert sha(p)==h,p
assert len(headers)==9
for n,row in headers.items():
 actual=lean_declaration_header(public,n)
 assert actual==row['statement'] and hashlib.sha256(actual.encode()).hexdigest()==freeze['headers'][n]
 fp=run/'native-public-fences'/(n+'.json');assert not fp.exists()
 subprocess.run([sys.executable,str(run/'run-command.py'),'public-fence-v1-'+n,sys.executable,'-X','utf8','tools/bandit.py','statement-fence','--declaration','BanditRL.OnlineConvex.'+n,'--file',public.as_posix(),'--output',fp.as_posix()],check=True)
 assert load(fp)['statement_hash']==freeze['headers'][n]
 subprocess.run([sys.executable,str(run/'run-command.py'),'safe-public-v1-'+n,sys.executable,'-X','utf8','tools/bandit.py','safe-verify','--fence',fp.as_posix(),'--lean-file',public.as_posix(),'--lean-file','Tests/OnlineSubgradientSumCanary.lean'],check=True)
t=public.read_text(encoding='utf-8');a=t.index('def SourceSubgradientSum');b=t.index('\ntheorem ',a);full=t[a:b].strip()
assert hashlib.sha256(full.encode()).hexdigest()==freeze['complete_definition_sha256']
assert re.findall(r'\S+',full)==load(contract/'scoped-contexts.json')['full_definition_tokens']
p=run/'public-safe-guard-audit-v1.json';assert not p.exists()
p.write_bytes((json.dumps(dict(status='passed',guards=9,unchanged_headers=freeze['headers'],original_module_bytes_exact=True,whole_twenty_canary_proofs_three_definitions_fixed=True,project_roots_and_pins_fixed=True,complete_M_definition_tokens_unchanged=True,guard_is_not_compilation=True),indent=2)+'\n').encode())
print('Nine native guards passed; complete M/original module/whole canary/shared files fixed. Compilation separate.')
