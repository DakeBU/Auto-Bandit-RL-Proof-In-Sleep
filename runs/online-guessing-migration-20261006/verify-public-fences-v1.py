"""Create/check twelve native frozen-header guards; these are not compilation."""
from pathlib import Path
import hashlib,json,subprocess,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header
run=Path(__file__).parent;load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'))
freeze=load(run/'draft-freeze-v2.json');headers=load('docs/contracts/online-guessing-migration-v1/headers-native-v2.json')
for n,row in headers.items():
 actual=lean_declaration_header(Path(row['file']),n);assert actual==row['statement'] and hashlib.sha256(actual.encode()).hexdigest()==freeze['headers'][n]
 fence=run/'native-public-fences'/(n+'.json');assert not fence.exists()
 subprocess.run([sys.executable,'-X','utf8',str(run/'run-command.py'),'public-fence-v1-'+n,sys.executable,'-X','utf8','tools/bandit.py','statement-fence','--declaration','BanditRL.OnlineGradientDescent.'+n,'--file',row['file'],'--output',str(fence)],check=True)
 assert load(fence)['statement_hash']==freeze['headers'][n]
 subprocess.run([sys.executable,'-X','utf8',str(run/'run-command.py'),'safe-public-v1-'+n,sys.executable,'-X','utf8','tools/bandit.py','safe-verify','--fence',str(fence),'--lean-file',row['file'],'--lean-file','Tests/OnlineGuessingComparisonCanary.lean'],check=True)
out=run/'public-safe-guard-audit-v1.json';assert not out.exists()
with out.open('w',encoding='utf-8',newline='\n') as f:json.dump(dict(status='passed',guards=12,unchanged_headers=freeze['headers'],fingerprints='authoritative native-normalized-v2, all mathematical tokens same as rawv1',guard_is_not_compilation=True),f,indent=2);f.write('\n')
print('Twelve native guards passed; separately no compilation claim.')
