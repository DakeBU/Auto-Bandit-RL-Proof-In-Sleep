"""Freeze source review before auditing existing proof bodies in the new context."""
from common_v1 import *
fixed();passed('prepare-source-review-v1-01')
r=load(RUN/'source-contract-receipt-v1.json');assert r['actor']['task']=='/root/source_reviewer' and r['verdict'] in ['accepted','accepted-with-explicit-delta']
assert sha(r['report'])==r['report_sha256']
for k in ['required_repairs','required_mathematical_repairs','required_metadata_repairs']:assert not r.get(k,[]),(k,r.get(k))
reviewed={x['path']:x['sha256'] for x in r['reviewed_files']}
for x in load(RUN/'source-contract-inputs-v1.json')['rows']:assert reviewed[x['path']]==x['sha256'] and sha(x['path'])==x['sha256'],x['path']
write(RUN/'stabilized-decision-v1.json',dict(status=r['verdict'],source_report_sha256=r['report_sha256'],source_receipt_sha256=sha(RUN/'source-contract-receipt-v1.json'),actual21_headers_unchanged=True,all21_context_types_under9_audited_renamings=True,new_proofs=0,new_definitions=0,proof_bodies_preexist_current_draft=True,current_focused_BODY_pending=True,chapter_complete=False,goal_complete=False))
event('stabilized',dict(current_distinct_source_contract_accepted=True,actual_headers=(CONTRACT/'headers-v1.json').as_posix(),new_proofs=0,existing_bodies_preexist=True))
event('proving',dict(route='Single lower reuse/body audit; existing dependent leaves are ready. Actual focused/kernel/native/value/canary evidence pending.',new_proofs=0))
write(RUN/'30_lower_worker-v1.md','/root single lower staged reuse audit, not independent reviewer. Existing21 public bodies are unchanged and predate this draft; current source/context stabilized. Audit actual selected history/Nat.rec projection, played support and finite-loss producer chain, same actual telescope/weighted potential/tuning and complete74 canaries. No target/body edits or new declaration-count growth. Combined gates and reader remain separate future evidence.')
fixed();print('Current source/context stabilized; actual existing BODY audit may begin, whole Goal ACTIVE.')
