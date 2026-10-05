"""Run actual native safe guards for all seven unchanged public headers."""
from pathlib import Path
import hashlib,json,subprocess,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header
run=Path(__file__).parent
freeze=json.loads((run/'draft-freeze-v1.json').read_text(encoding='utf-8'))
for name,hh in freeze['headers'].items():
    fence=run/'native-fences'/(name+'.json')
    f=json.loads(fence.read_text(encoding='utf-8'))
    header=lean_declaration_header(Path(f['file']),name)
    assert f['statement']==header and f['statement_hash']==hh
    assert all(a in header for a in f['source_assumptions'])
    subprocess.run([sys.executable,'-X','utf8',str(run/'run-command.py'),'safe-public-v1-'+name,
        sys.executable,'-X','utf8','tools/bandit.py','safe-verify','--fence',str(fence),
        '--lean-file','BanditRLProof/OnlineFTLFailure.lean','--lean-file','Tests/OnlineFTLFailureCanary.lean'],check=True)
with (run/'public-safe-guard-audit-v1.json').open('w',encoding='utf-8',newline='\n') as out:
    json.dump(dict(status='passed',unchanged_frozen_headers=freeze['headers'],native_safe_checks=7,
        actual_assumption_fragments=True,guard_is_not_compilation=True,
        body_canary_package_acceptance=False),out,indent=2);out.write('\n')
print('Seven actual native public safe guards passed; this is a header/placeholder guard, not compilation.')
