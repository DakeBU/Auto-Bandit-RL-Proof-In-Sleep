"""Actual native safe guards on unchanged public headers, separately from Lean."""
from pathlib import Path
import hashlib,json,subprocess,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header
run=Path(__file__).parent;freeze=json.loads((run/'draft-freeze-v1.json').read_text(encoding='utf-8'))
for n,hh in freeze['headers'].items():
    fence=run/'native-fences'/(n+'.json');f=json.loads(fence.read_text(encoding='utf-8'))
    header=lean_declaration_header(Path(f['file']),n)
    assert header==f['statement'] and f['statement_hash']==hh
    assert all(a in header for a in f['source_assumptions'])
    group=Path(f['file']).stem
    subprocess.run([sys.executable,'-X','utf8',str(run/'run-command.py'),'safe-public-v1-'+n,
        sys.executable,'-X','utf8','tools/bandit.py','safe-verify','--fence',str(fence),'--lean-file',f['file'],
        '--lean-file','Tests/'+group+'Canary.lean'],check=True)
with (run/'public-safe-guard-audit-v1.json').open('w',encoding='utf-8',newline='\n') as f:
    json.dump(dict(status='passed',unchanged_frozen_headers=freeze['headers'],native_safe_checks=22,actual_assumption_fragments=True,
        guard_is_not_compilation=True,body_canary_package_accepted=False),f,indent=2);f.write('\n')
print('22 actual native public safe guards passed; header/placeholder guard, not compilation.')
