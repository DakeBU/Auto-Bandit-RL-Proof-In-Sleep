"""Final scoped diff gate; retain exact raw evidence, bound every other package path."""
from pathlib import Path
import json,subprocess
run=Path(__file__).parent;base='64e25407a4a2b952fa4597d6c2cffc8df16810e8'
allpaths=subprocess.check_output(['git','diff','--name-only',base+'...HEAD'],encoding='utf-8').splitlines()
immutable=['leaves/native-types-v2.lean','leaves/neutral-types-v1.lean','leaves/neutral-types-v2.lean',
           'leaves/pre-integration-BanditRLProof--OnlineGradientDescent.lean.txt']
exceptions=[p for p in allpaths if p.startswith(run.as_posix()+'/') and
    (p.endswith('.log') or any(p==run.as_posix()+'/'+n for n in immutable))]
checked=[p for p in allpaths if p not in exceptions];commands=[];raw=[]
for start in range(0,len(checked),100):
    cmd=['git','diff','--check',base+'...HEAD','--']+checked[start:start+100]
    p=subprocess.run(cmd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    commands.append(dict(command=cmd,exit_code=p.returncode));raw.append(p.stdout)
    assert p.returncode==0,p.stdout.decode('utf-8',errors='replace')[-1800:]
(run/'delivery-scoped-diff-v2.log').write_bytes(b''.join(raw))
with (run/'delivery-scoped-diff-v2.json').open('w',encoding='utf-8',newline='\n') as f:
    json.dump(dict(status='passed',stacked_base=base,source_commit=subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf-8').strip(),
        checked_paths=checked,exception_paths=exceptions,commands=commands,
        reason='Task raw .logs and four exact immutable draft/type/snapshot blank EOF inputs only; all other changed proofs/JSON/scripts/evidence checked.'),f,indent=2);f.write('\n')
print('Final diff checked',len(checked),'paths;',len(exceptions),'explicit immutable raw evidence exceptions.')
