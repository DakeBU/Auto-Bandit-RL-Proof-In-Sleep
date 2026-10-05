"""Run actual Lean elaboration and focused builds after reviewed stabilization."""
from pathlib import Path
import json,subprocess,sys
run=Path(__file__).parent
assert (run/'contract-binding-audit-v1.json').is_file()
f=json.loads((run/'draft-freeze-v1.json').read_text(encoding='utf-8'))
def gate(label,*args):subprocess.run([sys.executable,'-X','utf8',str(run/'run-command.py'),label,*args],check=True)
for g in f['groups']:
    gate('body-'+g+'-v1-01','lake','env','lean','BanditRLProof/'+g+'.lean')
    gate('canary-'+g+'-v1-01','lake','env','lean','Tests/'+g+'Canary.lean')
gate('public-axioms-v1-01','lake','env','lean',str(run/'leaves/public-axioms-v1.lean'))
targets=['BanditRLProof.'+g for g in f['groups']]+['Tests.'+g+'Canary' for g in f['groups']]
gate('focused-build-v1-01','lake','build',*targets)
gate('verify-public-fences-v1-01',sys.executable,'-X','utf8',str(run/'verify-public-fences-v1.py'))
print('Four actual public bodies/four canary modules/53 named axioms/focused build/22 safe guards succeeded; separate body/package review pending.')
