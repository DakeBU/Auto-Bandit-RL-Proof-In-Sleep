"""Scoped draft delivery after actual FINAL/native gates; direct final audit separate."""
from common_v2 import *
fixed(True);passed('record-acceptance-v1-01');passed('prepare-pr-payload-v2-01');assert load(RUN/'native-acceptance-overlay-v1.json')['status']=='passed'
subprocess.run([sys.executable,'-B','-X','utf8',str(RUN/'commit-owned-v1.py'),'Accept canonical OSD source reuse after distinct final review'],check=True)
gate('contributor-final-v1-01',sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base',BASE)
gate('scoped-diff-final-v1-01',sys.executable,'-B','-X','utf8',RUN/'check-scoped-diff-v1.py','final-v1')
subprocess.run([sys.executable,'-B','-X','utf8',str(RUN/'commit-owned-v1.py'),'Bind final exact-base canonical OSD evidence checks'],check=True)
gate('committed-raw-audit-v1-01',sys.executable,'-B','-X','utf8',RUN/'audit-committed-raw-v1.py')
subprocess.run([sys.executable,'-B','-X','utf8',str(RUN/'commit-owned-v1.py'),'Preserve exact current OSD evidence before draft publication'],check=True)
assert not subprocess.check_output(['git','status','--porcelain'],text=True).strip()
gate('push-creation-v1-01','git','-c','credential.helper=','-c','credential.helper=!gh auth git-credential','push','-u','origin','codex/research-online-osd-migration')
gate('create-pr-v1-01',sys.executable,'-B','-X','utf8',RUN/'create-pr-v1.py')
print('Actual scoped draft created; app attachment/delivery metadata/DIRECT final raw head audit remain.')
