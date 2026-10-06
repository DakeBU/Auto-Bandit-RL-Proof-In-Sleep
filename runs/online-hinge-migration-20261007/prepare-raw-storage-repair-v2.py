"""Repair Git evidence storage without rewriting reviewed files or failed attempts."""
from common_v2 import *
audit=load(RUN/'raw-storage-repair-audit-v1.json')
assert audit['mismatches'] and all(r['only_CRLF_normalization'] for r in audit['mismatches'])
for r in audit['mismatches']: assert sha(r['path'])==r['working_sha256']
fixed(True)
old=RUN/'prepare-delivery-v1.py';text=old.read_text(encoding='utf-8')
text=text.replace("'contributor-final-v1-01'","'contributor-final-v2-01'").replace("'scoped-diff-final-v1-01'","'scoped-diff-final-v2-01'").replace("'committed-raw-audit-v1-01'","'committed-raw-audit-v2-01'").replace("'committed-raw-audit-v1.json'","'committed-raw-audit-v2.json'").replace("'pr-payload-v1.json'","'pr-payload-v2.json'").replace("'pr-payload-before-API-v1.json'","'pr-payload-before-API-v2.json'").replace("'create-pr-v1-01'","'create-pr-v2-01'")
text=text.replace("paths=['accepted-decision-v1.json'","paths=['raw-storage-repair-v2.json','accepted-decision-v1.json'")
text=text.replace('Unused pre-use helper corrections and readonly lookup diagnostics preserved, no mathematical weakening.', 'Unused pre-use helper corrections and readonly lookup diagnostics preserved, no mathematical weakening. Actual initial committed-raw-audit-v1-01 failed because Git core.autocrlf normalized native CRLF evidence; task-local -text attributes and renormalized staging preserve exact original reviewed working bytes. Version2 raw/contributor/scoped checks replace the failed delivery gate, whose raw output remains.')
write(RUN/'prepare-delivery-v2.py',text)
raw=(RUN/'audit-committed-raw-v1.py').read_text(encoding='utf-8').replace("'committed-raw-audit-v1.json'","'committed-raw-audit-v2.json'")
write(RUN/'audit-committed-raw-v2.py',raw)
payload=load(RUN/'pr-payload-v1.json')
payload['body']+='\nDelivery evidence storage repair: initial raw Git audit actually failed because core.autocrlf normalized CRLF logs/snapshots. A task-local .gitattributes -text rule and renormalized staging preserve the exact original reviewed working bytes; no reviewed file/source/statement/body changed. Original failed audit retained; fresh version2 contributor/scoped/raw audits are required before this draft delivery.\n'
write(RUN/'pr-payload-v2.json',payload)
write(RUN/'pr-body-v2.md',payload['body'])
write(RUN/'pr-payload-before-API-v2.json',dict(path=(RUN/'pr-payload-v2.json').as_posix(),sha256=sha(RUN/'pr-payload-v2.json'),before_first_API_use=True))
create=(RUN/'create-pr-v1.py').read_text(encoding='utf-8').replace("'pr-payload-v1.json'","'pr-payload-v2.json'").replace("'pr-payload-before-API-v1.json'","'pr-payload-before-API-v2.json'")
write(RUN/'create-pr-v2.py',create)
helpers=[RUN/n for n in ['audit-committed-raw-v2.py','prepare-delivery-v2.py','create-pr-v2.py']]
for p in helpers: compile(p.read_text(encoding='utf-8'),str(p),'exec')
generated('raw-storage-repair-helpers-before-use-v2.json',helpers)
write(RUN/'raw-storage-repair-v2.json',dict(status='repair-prepared-not-yet-gate-passed',failure='committed-raw-audit-v1-01',cause='core.autocrlf=true normalized native CRLF evidence in Git staging',affected_raw_files=len(audit['mismatches']),only_CRLF_normalization=True,original_reviewed_working_bytes_preserved=True,original_failed_audit_retained=True,scope='task-owned run local .gitattributes only; no repo/global configuration/source change',required_fresh_gates=['contributor-final-v2-01','scoped-diff-final-v2-01','committed-raw-audit-v2-01','DIRECT-final-v2'],source_package_accepted=True,chapter_complete=False,goal_complete=False))
print('Version2 exact-byte storage repair prepared; all original reviewed bytes unchanged.')
