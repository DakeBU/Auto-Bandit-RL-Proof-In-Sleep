"""Scoped delivery after actual FINAL; app attachment and direct final audit separate."""
from common_v2 import *
fixed(True,True);passed('record-acceptance-v1-01');passed('prepare-pr-payload-v1-01')
assert load(RUN/'native-acceptance-overlay-v1.json')['status']=='passed'
subprocess.run([sys.executable,'-B','-X','utf8',str(RUN/'commit-owned-v1.py'),'Accept source uncountability consequence after distinct final review'],check=True)
gate('contributor-final-v1-01',sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base',BASE)
gate('scoped-diff-final-v1-01',sys.executable,'-B','-X','utf8',RUN/'check-scoped-diff-v1.py','final-v1')
subprocess.run([sys.executable,'-B','-X','utf8',str(RUN/'commit-owned-v1.py'),'Bind exact-base final cardinality contribution checks'],check=True)
gate('committed-raw-audit-v1-01',sys.executable,'-B','-X','utf8',RUN/'audit-committed-raw-v1.py')
subprocess.run([sys.executable,'-B','-X','utf8',str(RUN/'commit-owned-v1.py'),'Preserve exact cardinality evidence before draft publication'],check=True)
assert not subprocess.check_output(['git','status','--porcelain'],text=True).strip()
gate('push-creation-v1-01','git','-c','credential.helper=','-c','credential.helper=!gh auth git-credential','push','-u','origin','codex/research-online-convex-uncountability')
gate('create-pr-v1-01',sys.executable,'-B','-X','utf8',RUN/'create-pr-v1.py')
print('Actual draft created; required app attachment/delivery metadata/DIRECT final raw head audit remain.')
