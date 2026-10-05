"""Check all new code/JSON/docs while preserving explicitly listed raw output bytes."""
from pathlib import Path
import json,subprocess,sys
base='f6daaa68927398df9fd8b756f3ac2dd28247c1e7';run=Path(__file__).parent
paths=subprocess.check_output(['git','diff','--name-only',base+'...HEAD'],encoding='utf-8').splitlines()
exceptions=[];checked=[]
for p in paths:
    reason=None
    if p.startswith(run.as_posix()+'/'):
        if p.endswith('.log'):reason='exact raw command output'
        elif '/leaves/pre-integration-' in p and p.endswith('.txt'):reason='exact prior reviewed source/reader bytes'
        elif p.endswith('/leaves/canary-attempt-v1.lean.txt'):reason='exact failed canary source snapshot'
        elif p.endswith('/source-printed9-10-pdf21-22.txt'):reason='exact source PDF extraction'
    if reason:exceptions.append(dict(path=p,reason=reason))
    else:checked.append(p)
result=subprocess.run(['git','diff','--check',base+'...HEAD','--',*checked],stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
out=run/'scoped-diff-audit-v1.json';assert not out.exists()
with out.open('w',encoding='utf-8',newline='\n') as f:json.dump(dict(exit_code=result.returncode,base=base,checked_paths=checked,exceptions=exceptions,production_and_JSON_scripts_docs_checked=True),f,indent=2);f.write('\n')
print('Checked',len(checked),'paths; exact enumerated raw exceptions',len(exceptions))
if result.returncode:print(result.stdout.decode('utf-8',errors='replace'))
sys.exit(result.returncode)
