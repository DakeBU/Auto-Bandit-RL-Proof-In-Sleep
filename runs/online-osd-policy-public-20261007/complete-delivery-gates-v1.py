"""Authorized scoped delivery after actual FINAL/native acceptance."""
from common_v1 import *
fixed(True);passed('record-acceptance-v1-01');passed('prepare-pr-payload-v1-01')
assert load(RUN/'native-acceptance-overlay-v1.json')['status']=='passed'
subprocess.run([sys.executable,'-B','-X','utf8',str(RUN/'commit-owned-v1.py'),'Accept current finite-history OSD policy source reuse evidence'],check=True)
gate('contributor-final-v1-01',sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base',BASE)
gate('scoped-diff-final-v1-01',sys.executable,'-B','-X','utf8',RUN/'check-scoped-diff-v1.py','final-v1')
subprocess.run([sys.executable,'-B','-X','utf8',str(RUN/'commit-owned-v1.py'),'Bind final exact-base policy contributor and raw evidence checks'],check=True)
gate('committed-raw-audit-v1-01',sys.executable,'-B','-X','utf8',RUN/'audit-committed-raw-v1.py')
subprocess.run([sys.executable,'-B','-X','utf8',str(RUN/'commit-owned-v1.py'),'Preserve exact current policy evidence before draft publication'],check=True)
assert not subprocess.check_output(['git','status','--porcelain'],text=True).strip()
gate('push-creation-v1-01','git','-c','credential.helper=','-c','credential.helper=!gh auth git-credential','push','-u','origin','codex/research-online-osd-policy-migration')
gate('create-pr-v1-01',sys.executable,'-B','-X','utf8',RUN/'create-pr-v1.py')
print('Scoped draft actually created; app attachment/delivery metadata/DIRECT final raw audit remain.')
