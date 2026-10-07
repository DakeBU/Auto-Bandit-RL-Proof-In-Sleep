"""Resume scoped publication only after distinct byte-preservation metadata review."""
from common_v1 import *
fixed(True);passed('record-acceptance-v1-01');passed('committed-raw-audit-v3-01');passed('prepare-publication-metadata-v3-01')
r=load(RUN/'delivery-metadata-receipt-v2.json');assert r['actor']['task']=='/root/source_reviewer' and r['verdict'] in ['accepted','accepted-with-explicit-delta'] and sha(r['report'])==r['report_sha256']
for k in ['required_repairs','required_mathematical_repairs','required_metadata_repairs']:assert not r.get(k,[]),k
assert all(r['repair_verdict'][k]['verdict']=='satisfied' for k in ['D1','D2','D3','D4'])
reviewed={x['path']:x['sha256'] for x in r['reviewed_files']}
for x in load(RUN/'delivery-metadata-review-inputs-v2.json')['rows']:assert reviewed[x['path']]==x['sha256']==sha(x['path']),x['path']
assert not (RUN/'created-PR-v1.json').exists() and not (RUN/'push-creation-v1-01-exit.json').exists()
subprocess.run([sys.executable,'-B','-X','utf8',str(RUN/'commit-owned-v1.py'),'Review policy publication raw-byte preservation repair'],check=True)
gate('contributor-final-v2-01',sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base',BASE)
gate('scoped-diff-final-v2-01',sys.executable,'-B','-X','utf8',RUN/'check-scoped-diff-v1.py','final-v2')
subprocess.run([sys.executable,'-B','-X','utf8',str(RUN/'commit-owned-v1.py'),'Bind repaired exact-base policy publication gates'],check=True)
gate('committed-raw-audit-v4-01',sys.executable,'-B','-X','utf8',RUN/'audit-committed-raw-v3.py')
subprocess.run([sys.executable,'-B','-X','utf8',str(RUN/'commit-owned-v1.py'),'Preserve captured final policy Git raw tree before draft publication'],check=True)
assert not subprocess.check_output(['git','status','--porcelain'],text=True).strip()
gate('push-creation-v1-01','git','-c','credential.helper=','-c','credential.helper=!gh auth git-credential','push','-u','origin','codex/research-online-osd-policy-migration')
gate('create-pr-v1-01',sys.executable,'-B','-X','utf8',RUN/'create-pr-v3.py')
print('Actual repaired scoped draft created; app attachment/delivery/DIRECT final remain.')
