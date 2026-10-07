"""Concrete scoped Git/PR delivery only after actual source FINAL and native acceptance."""
from common_v4 import *
fixed(True,True);passed('record-acceptance-v1-01');passed('prepare-pr-payload-v1-01')
assert load(RUN/'native-acceptance-overlay-v1.json')['status']=='passed'
assert load(RUN/'accepted-decision-v1.json')['source_package_accepted']
subprocess.run([sys.executable,'-B','-X','utf8',str(RUN/'commit-owned-v1.py'),'Accept exact source plane example after distinct final review'],check=True)
gate('contributor-final-v1-01',sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base',BASE)
gate('scoped-diff-final-v1-01',sys.executable,'-B','-X','utf8',RUN/'check-scoped-diff-v2.py','final-v1')
subprocess.run([sys.executable,'-B','-X','utf8',str(RUN/'commit-owned-v1.py'),'Bind final source acceptance contributor and raw scope gates'],check=True)
gate('committed-raw-audit-v1-01',sys.executable,'-B','-X','utf8',RUN/'audit-committed-raw-v1.py')
subprocess.run([sys.executable,'-B','-X','utf8',str(RUN/'commit-owned-v1.py'),'Preserve exact committed plane-example evidence before publication'],check=True)
assert not subprocess.check_output(['git','status','--porcelain'],text=True).strip()
gate('push-creation-v1-01','git','-c','credential.helper=','-c','credential.helper=!gh auth git-credential','push','-u','origin','codex/research-online-convex-nondifferentiability')
gate('create-pr-v1-01',sys.executable,'-B','-X','utf8',RUN/'create-pr-v1.py')
print('Actual draft PR created; mandatory app attachment/delivery final raw head audit remain.')
