"""Commit only this package, retaining exact immutable whitespace evidence."""
from pathlib import Path
import json,subprocess,sys
run=Path(__file__).parent
paths=['BanditRLProof.lean','BanditRLProof/OnlineGradientDescent.lean','BanditRLProof/OnlineGradientDescentSource.lean',
    'Tests.lean','Tests/OnlineGradientDescentSourceCanary.lean','MANIFEST.md','runs/lifecycle_sessions.jsonl','runs/trials.jsonl',
    'website/content/chapters.json','website/content/highlights.json','website/content/readings.json',
    'research-wiki/contribution-contracts/ONLINE-OGD-MIGRATION-20261005.json',
    'conversion-windows/ONLINE-OGD-MIGRATION-20261005.md','docs/contracts/online-ogd-migration-v1',
    'docs/contracts/online-ogd-migration-v2','proof-obligations/ONLINE-OGD-MIGRATION-20261005.md',
    'runs/online-ogd-migration-20261005','tasks/ONLINE-OGD-MIGRATION-20261005.md']
def call(args):
    p=subprocess.run(args,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    if p.returncode:print(p.stdout.decode('utf-8',errors='replace')[-1600:]);raise SystemExit(p.returncode)
    return p.stdout.decode('utf-8')
assert json.loads((run/'full-harness-v2-01-exit.json').read_text())['exit_code']==0
assert call(['git','branch','--show-current']).strip()=='codex/research-online-ogd-migration'
base='64e25407a4a2b952fa4597d6c2cffc8df16810e8'
assert call(['git','rev-parse','HEAD']).strip()==base
call(['git','add','--']+paths)
allpaths=call(['git','diff','--cached','--name-only']).splitlines()
immutable=['leaves/native-types-v2.lean','leaves/neutral-types-v1.lean','leaves/neutral-types-v2.lean',
           'leaves/pre-integration-BanditRLProof--OnlineGradientDescent.lean.txt']
exceptions=[p for p in allpaths if p.startswith(run.as_posix()+'/') and
    (p.endswith('.log') or any(p==run.as_posix()+'/'+n for n in immutable))]
checked=[p for p in allpaths if p not in exceptions]
cmd=['git','diff','--cached','--check','--']+checked
p=subprocess.run(cmd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
(run/'candidate-scoped-diffcheck-v2.log').write_bytes(p.stdout)
with (run/'candidate-scoped-diffcheck-v2-exit.json').open('w',encoding='utf-8',newline='\n') as f:
    json.dump(dict(command=cmd,exit_code=p.returncode,checked_paths=checked,exception_paths=exceptions,
        reason='Exact raw compiler .log evidence plus four immutable failed/type/snapshot inputs; no production proof/schema/JSON whitespace exception.'),f,indent=2);f.write('\n')
assert p.returncode==0
call(['git','add','--',str(run)])
out=call(['git','commit','-m','Repair source-faithful projected OGD regularity and audit retained interfaces'])
print(out[:900])
head=call(['git','rev-parse','HEAD']).strip()
status=call(['git','status','--porcelain']);assert not status,status
with (run/'candidate-commit-v2.json').open('w',encoding='utf-8',newline='\n') as f:
    json.dump(dict(commit=head,stacked_base=base,branch='codex/research-online-ogd-migration',
        clean_immediately_after_commit=True,source_reader_commit=head,full_harness_passed=True,
        note='Metadata written after source commit; commit this receipt separately before clean site build.'),f,indent=2);f.write('\n')
print('Source candidate committed',head,'clean before receipt; metadata commit required before site.')
