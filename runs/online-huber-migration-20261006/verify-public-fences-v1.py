"""Check all nineteen fixed native headers; guards do not certify compilation."""
from pathlib import Path
import hashlib,json,subprocess,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header
run=Path(__file__).parent;load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'))
freeze=load(run/'draft-freeze-v1.json');headers=load('docs/contracts/online-huber-migration-v1/headers.json')
for n,row in headers.items():
 actual=lean_declaration_header(Path(row['file']),n);assert actual==row['statement'] and hashlib.sha256(actual.encode()).hexdigest()==freeze['headers'][n]
 fence=run/'native-public-fences'/(n+'.json');assert not fence.exists()
 subprocess.run([sys.executable,'-X','utf8',str(run/'run-command.py'),'public-fence-v1-'+n,sys.executable,'-X','utf8','tools/bandit.py','statement-fence','--declaration','BanditRL.OnlineHuber.'+n,'--file',row['file'],'--output',str(fence)],check=True)
 assert load(fence)['statement_hash']==freeze['headers'][n]
 subprocess.run([sys.executable,'-X','utf8',str(run/'run-command.py'),'safe-public-v1-'+n,sys.executable,'-X','utf8','tools/bandit.py','safe-verify','--fence',str(fence),'--lean-file',row['file'],'--lean-file','Tests/OnlineHuberCanary.lean'],check=True)
out=run/'public-safe-guard-audit-v1.json';assert not out.exists()
with out.open('w',encoding='utf-8',newline='\n') as f:json.dump(dict(status='passed',guards=19,unchanged_headers=freeze['headers'],full_definition_contexts='three definitions retained with whole-module mathematical tokens, not short-header fingerprints alone',guard_is_not_compilation=True),f,indent=2);f.write('\n')
print('Nineteen native guards passed; compilation evidence is separate.')
