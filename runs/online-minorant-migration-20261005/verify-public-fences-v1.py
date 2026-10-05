"""Execute four actual native guards separately from Lean elaboration."""
from pathlib import Path
import hashlib,json,subprocess,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header
run=Path(__file__).parent;freeze=json.loads((run/'draft-freeze-v1.json').read_text(encoding='utf-8'))
for n,h in freeze['headers'].items():
 fence=run/'native-draft-fences'/(n+'.json');data=json.loads(fence.read_text(encoding='utf-8'))
 header=lean_declaration_header(Path(data['file']),n)
 assert header==data['statement'] and hashlib.sha256(header.encode()).hexdigest()==h==data['statement_hash']
 assert all(a in header for a in data['source_assumptions'])
 subprocess.run([sys.executable,'-X','utf8',str(run/'run-command.py'),'safe-public-v1-'+n,sys.executable,'-X','utf8','tools/bandit.py','safe-verify','--fence',str(fence),'--lean-file',data['file'],'--lean-file','Tests/OnlineConvexMinorantCanary.lean'],check=True)
out=run/'public-safe-guard-audit-v1.json';assert not out.exists()
with out.open('w',encoding='utf-8',newline='\n') as f:
 json.dump(dict(status='passed',guards=4,unchanged_headers=freeze['headers'],assumption_fragments_retained=True,guard_is_not_compilation=True),f,indent=2);f.write('\n')
print('Four actual native guards passed, not compilation.')
