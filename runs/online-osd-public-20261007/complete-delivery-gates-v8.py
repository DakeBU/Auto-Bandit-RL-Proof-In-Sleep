"""Scoped draft delivery after FINAL and separately reviewed native metadata repair."""
from common_v2 import *
fixed(True);passed('record-acceptance-repair-v5-01');passed('prepare-pr-payload-v6-01')
assert load(RUN/'native-acceptance-overlay-v1.json')['status']=='passed'
r=load(RUN/'native-metadata-repair-receipt-v1.json')
assert r['actor']['task']=='/root/source_reviewer' and r['verdict'] in ['accepted','accepted-with-explicit-delta']
assert r['repair_verdict']['M6']['verdict']=='satisfied' and sha(r['report'])==r['report_sha256']
assert not r.get('required_repairs',[]) and not r.get('required_mathematical_repairs',[]) and not r.get('required_metadata_repairs',[])
reviewed={x['path']:x['sha256'] for x in r['reviewed_files']}
for x in load(RUN/'native-metadata-repair-inputs-v1.json')['rows']:assert reviewed[x['path']]==x['sha256'] and sha(x['path'])==x['sha256']
subprocess.run([sys.executable,'-B','-X','utf8',str(RUN/'commit-owned-v1.py'),'Accept canonical OSD reuse and native metadata repair'],check=True)
gate('contributor-final-v1-01',sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base',BASE)
gate('scoped-diff-final-v1-01',sys.executable,'-B','-X','utf8',RUN/'check-scoped-diff-v1.py','final-v1')
subprocess.run([sys.executable,'-B','-X','utf8',str(RUN/'commit-owned-v1.py'),'Bind final exact-base canonical OSD evidence checks'],check=True)
gate('committed-raw-audit-v1-01',sys.executable,'-B','-X','utf8',RUN/'audit-committed-raw-v1.py')
subprocess.run([sys.executable,'-B','-X','utf8',str(RUN/'commit-owned-v1.py'),'Preserve exact current OSD evidence before draft publication'],check=True)
assert not subprocess.check_output(['git','status','--porcelain'],text=True).strip()
gate('push-creation-v1-01','git','-c','credential.helper=','-c','credential.helper=!gh auth git-credential','push','-u','origin','codex/research-online-osd-migration')
gate('create-pr-v1-01',sys.executable,'-B','-X','utf8',RUN/'create-pr-v1.py')
print('Actual scoped draft created; app attachment/delivery metadata/DIRECT final raw head audit remain.')
