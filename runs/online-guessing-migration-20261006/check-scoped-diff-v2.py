"""Check production and metadata; enumerate preserved raw-evidence exceptions."""
from pathlib import Path
import json,subprocess,sys
base='25c77a837c849eb78832673063483db5f663a73a';run=Path(__file__).parent
paths=subprocess.check_output(['git','diff','--name-only',base+'...HEAD'],encoding='utf-8').splitlines()
exceptions=[];checked=[]
for p in paths:
 reason=None
 if p.startswith(run.as_posix()+'/'):
  if p.endswith('.log'):reason='exact raw command output'
  elif ('/leaves/pre-integration-' in p or '/leaves/original-' in p or '/original-' in p or '/leaves/import-comment-before-repair-' in p or '/leaves/reader-before-renderer-adapter-v2.' in p or '/leaves/manifest-before-contributor-list-v2.' in p) and p.endswith('.txt'):reason='exact reviewed source or reader bytes before integration/repair'
  elif p.endswith('/source-printed15-pdf27.txt') or p.endswith('/source-chapter1-pdf13-19.txt'):reason='exact source PDF extraction'
 if reason:exceptions.append(dict(path=p,reason=reason))
 else:checked.append(p)
child=subprocess.run(['git','diff','--check',base+'...HEAD','--',*checked],stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
out=run/('scoped-diff-audit-'+sys.argv[1]+'.json');assert not out.exists()
with out.open('w',encoding='utf-8',newline='\n') as f:json.dump(dict(exit_code=child.returncode,base=base,checked_paths=checked,exceptions=exceptions,production_JSON_scripts_docs_checked=True),f,indent=2);f.write('\n')
print('Checked',len(checked),'paths; exact enumerated raw exceptions',len(exceptions))
if child.returncode:print(child.stdout.decode('utf-8',errors='replace'))
sys.exit(child.returncode)
