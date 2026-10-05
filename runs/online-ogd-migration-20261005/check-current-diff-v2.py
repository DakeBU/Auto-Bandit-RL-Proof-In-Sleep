"""Check the full package diff, retaining only exact raw evidence exceptions."""
from pathlib import Path
import json,subprocess
run=Path(__file__).parent;base='64e25407a4a2b952fa4597d6c2cffc8df16810e8'
allpaths=subprocess.check_output(['git','diff','--name-only',base+'...HEAD'],encoding='utf-8').splitlines()
immutable=['leaves/native-types-v2.lean','leaves/neutral-types-v1.lean','leaves/neutral-types-v2.lean',
           'leaves/pre-integration-BanditRLProof--OnlineGradientDescent.lean.txt']
exceptions=[p for p in allpaths if p.startswith(run.as_posix()+'/') and
    (p.endswith('.log') or any(p==run.as_posix()+'/'+n for n in immutable))]
checked=[p for p in allpaths if p not in exceptions]
p=subprocess.run(['git','diff','--check',base+'...HEAD','--']+checked,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
(run/'current-scoped-diffcheck-v2.log').write_bytes(p.stdout)
with (run/'current-scoped-diffcheck-v2.json').open('w',encoding='utf-8',newline='\n') as f:
    json.dump(dict(status='passed' if p.returncode==0 else 'failed',exit_code=p.returncode,stacked_base=base,
        source_commit=subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf-8').strip(),
        checked_paths=checked,exception_paths=exceptions,
        reason='Only task raw compiler logs and four exact immutable prior failed/type/snapshot inputs; all changed production/public proofs/JSON/schema/scripts included.'),f,indent=2);f.write('\n')
assert p.returncode==0,p.stdout.decode('utf-8',errors='replace')[-1200:]
print('Checked',len(checked),'package paths; preserved',len(exceptions),'explicit immutable raw evidence paths.')
