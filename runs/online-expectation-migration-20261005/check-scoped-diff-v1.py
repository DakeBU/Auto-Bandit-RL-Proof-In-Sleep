"""Check production/JSON/scripts/docs with enumerated exact raw evidence exceptions."""
from pathlib import Path
import json,subprocess,sys
base='7c3b241a13b1b43d1efcd08429f33c93b890a981';run=Path(__file__).parent
paths=subprocess.check_output(['git','diff','--name-only',base+'...HEAD'],encoding='utf-8').splitlines()
exceptions=[];checked=[]
for p in paths:
 reason=None
 if p.startswith(run.as_posix()+'/'):
  if p.endswith('.log'):reason='exact raw command output'
  elif ('/leaves/pre-integration-' in p or '/original-' in p) and p.endswith('.txt'):reason='exact original reviewed source/reader bytes'
  elif p.endswith('/source-printed10-11-pdf22-23.txt'):reason='exact source PDF extraction'
 if reason:exceptions.append(dict(path=p,reason=reason))
 else:checked.append(p)
p=subprocess.run(['git','diff','--check',base+'...HEAD','--',*checked],stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
out=run/('scoped-diff-audit-'+sys.argv[1]+'.json');assert not out.exists()
with out.open('w',encoding='utf-8',newline='\n') as f:
 json.dump(dict(exit_code=p.returncode,base=base,checked_paths=checked,exceptions=exceptions,production_JSON_scripts_docs_checked=True),f,indent=2);f.write('\n')
print('Checked',len(checked),'paths; exact enumerated raw exceptions',len(exceptions))
if p.returncode:print(p.stdout.decode('utf-8',errors='replace'))
sys.exit(p.returncode)
