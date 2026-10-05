"""Keep raw evidence byte-exact; check all other committed package paths."""
from pathlib import Path
import json,subprocess
run=Path(__file__).parent;base='4b55f5ebebb370ebe9e173b9bf5155b97a2e3998'
paths=subprocess.check_output(['git','diff','--name-only',base+'...HEAD'],encoding='utf-8').splitlines()
# Explicit historical byte snapshots; never extend this to arbitrary code/docs.
immutable=['original-public-module.lean.txt','original-public-canary.lean.txt',
    'failed-raw-snapshot-v1-01.lean.txt','source-printed12-pdf24.txt',
    'leaves/pre-integration-BanditRLProof--OnlineFTLFailure.lean.txt',
    'leaves/failed-comment-integration-v1-01.lean.txt']
exceptions=[p for p in paths if p.startswith(run.as_posix()+'/') and
    (p.endswith('.log') or p in {run.as_posix()+'/'+n for n in immutable})]
checked=[p for p in paths if p not in exceptions];records=[];outputs=[]
for i in range(0,len(checked),100):
    cmd=['git','diff','--check',base+'...HEAD','--']+checked[i:i+100]
    p=subprocess.run(cmd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    records.append(dict(command=cmd,exit_code=p.returncode));outputs.append(p.stdout)
    if p.returncode:
        (run/'scoped-diff-failure-v2.log').write_bytes(b''.join(outputs))
        print(p.stdout.decode('utf-8',errors='replace')[-2400:]);raise SystemExit(p.returncode)
(run/'scoped-diff-v2.log').write_bytes(b''.join(outputs))
with (run/'scoped-diff-v2.json').open('w',encoding='utf-8',newline='\n') as f:
    json.dump(dict(status='passed',stacked_base=base,source_commit=subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf-8').strip(),
        checked_paths=checked,exception_paths=exceptions,commands=records,
        reason='Task raw logs and six explicit exact-raw original/failed/source snapshots only; every other changed production/JSON/script/document/evidence path checked.'),f,indent=2);f.write('\n')
print('Scoped diff checked',len(checked),'paths;',len(exceptions),'explicit raw-evidence exceptions.')
