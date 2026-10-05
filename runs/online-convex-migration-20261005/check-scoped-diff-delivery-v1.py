"""Check every committed path except explicit task raw-evidence originals."""
from pathlib import Path
import json,subprocess
run=Path(__file__).parent;base='a2728b1da2109844ffec64f594827197cd9b541b'
paths=subprocess.check_output(['git','diff','--name-only',base+'...HEAD'],encoding='utf-8').splitlines()
freeze=json.loads((run/'draft-freeze-v1.json').read_text(encoding='utf-8'))
immutable=['source-printed9-10-pdf21-22.txt','convention-printed6-pdf17.txt','leaves/public-axioms-v1.lean']
for g in freeze['groups']:immutable+=['original-'+g+'.lean.txt','original-'+g+'Canary.lean.txt','leaves/pre-integration-BanditRLProof--'+g+'.lean.txt']
exceptions=[p for p in paths if p.startswith(run.as_posix()+'/') and (p.endswith('.log') or p in {run.as_posix()+'/'+n for n in immutable})]
checked=[p for p in paths if p not in exceptions];records=[];outputs=[]
for i in range(0,len(checked),100):
    cmd=['git','diff','--check',base+'...HEAD','--']+checked[i:i+100]
    p=subprocess.run(cmd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT);records.append(dict(command=cmd,exit_code=p.returncode));outputs.append(p.stdout)
    if p.returncode:
        (run/'scoped-diff-failure-delivery-v1.log').write_bytes(b''.join(outputs));print(p.stdout.decode('utf-8',errors='replace')[-2400:]);raise SystemExit(p.returncode)
(run/'scoped-diff-delivery-v1.log').write_bytes(b''.join(outputs))
with (run/'scoped-diff-delivery-v1.json').open('w',encoding='utf-8',newline='\n') as f:
    json.dump(dict(status='passed',stacked_base=base,source_commit=subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf-8').strip(),checked_paths=checked,exception_paths=exceptions,commands=records,
        reason='Task raw logs and explicitly enumerated exact source/module/canary snapshots plus one frozen original axiom probe only; repaired v2 probe checked; every other production/JSON/script/document checked.'),f,indent=2);f.write('\n')
print('Scoped diff checked',len(checked),'paths;',len(exceptions),'explicit raw-evidence exceptions.')
