"""Native eleven proof guards and exact definition/test byte checks, separate from builds."""
from pathlib import Path
import hashlib,json,subprocess,sys,re
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header
run=Path(__file__).parent;contract=Path('docs/contracts/online-subgradient-differentiability-migration-v1')
load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'));sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
freeze=load(run/'draft-freeze-v1.json');headers=load(contract/'headers.json');public=Path('BanditRLProof/OnlineSubgradientDifferentiability.lean')
assert (run/'original-OnlineSubgradientDifferentiability.lean.txt').read_bytes() in public.read_bytes()
for group in ['fixed_shared_files','whole_old_canary']:
 for p,h in freeze[group].items():assert sha(p)==h,p
assert Path('Tests.lean').read_bytes().startswith((run/'original-Tests.lean.txt').read_bytes())
for n,row in headers.items():
 actual=lean_declaration_header(public,n);assert actual==row['statement'] and hashlib.sha256(actual.encode()).hexdigest()==freeze['headers'][n]
 fp=run/'native-public-fences'/(n+'.json');assert not fp.exists()
 subprocess.run([sys.executable,str(run/'run-command.py'),'public-fence-v1-'+n,sys.executable,'-X','utf8','tools/bandit.py','statement-fence','--declaration','BanditRL.OnlineConvex.'+n,'--file',public.as_posix(),'--output',fp.as_posix()],check=True)
 assert load(fp)['statement_hash']==freeze['headers'][n]
 subprocess.run([sys.executable,str(run/'run-command.py'),'safe-public-v1-'+n,sys.executable,'-X','utf8','tools/bandit.py','safe-verify','--fence',fp.as_posix(),'--lean-file',public.as_posix(),'--lean-file','Tests/OnlineSubgradientDifferentiabilityCanary.lean','--lean-file','Tests/OnlineDifferentiabilityBoundaryCanary.lean'],check=True)
canary=Path('Tests/OnlineDifferentiabilityBoundaryCanary.lean')
for n,row in load(contract/'new-canary-terminals-v1.json')['headers'].items():assert lean_declaration_header(canary,n)==row['statement'],n
text=public.read_text(encoding='utf-8');start=text.index('def SourceDifferentiableAt');end=text.index('\ntheorem ',start);full=text[start:end].strip()
assert hashlib.sha256(full.encode()).hexdigest()==freeze['complete_definition_sha256']
assert re.findall(r'\S+',full)==load(contract/'scoped-contexts.json')['full_definition_tokens']
out=run/'public-safe-guard-audit-v1.json';assert not out.exists();out.write_bytes((json.dumps(dict(status='passed',guards=11,unchanged_headers=freeze['headers'],old_module_bytes_contiguous=True,whole_old_canary_fixed=True,Tests_original_raw_prefix=True,new_three_canary_headers_unchanged=True,complete_local_real_definition_tokens_unchanged=True,guard_is_not_compilation=True),indent=2)+'\n').encode())
print('Eleven native guards passed; full definition tokens/old source bytes/testprefix/3newtest headers fixed. Compilation separate.')
