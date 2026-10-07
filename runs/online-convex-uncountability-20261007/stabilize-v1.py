"""Stabilize exactly the independently reviewed targets after real context repair."""
from common_v1 import *
fixed();r=load(RUN/'source-contract-receipt-v3.json')
assert r['actor']['task']=='/root/source_reviewer' and r['verdict']=='accepted-with-explicit-delta'
assert r['repair_verdict']['M1']['verdict']=='satisfied'
assert sha(r['report'])==r['report_sha256']
for k in ['required_mathematical_repairs','mathematical_repairs','required_metadata_repairs']:assert not r.get(k,[])
reviewed={p['path']:p['sha256'] for p in r['reviewed_files']}
rows=[]
for row in load(RUN/'source-contract-inputs-v3.json')['rows']:
 assert reviewed[row['path']]==row['sha256']==sha(row['path']),row['path'];rows.append(row)
write(RUN/'contract-reviewed-bindings-v1.json',dict(status='passed',rows=rows,original_v1_report_and_receipt_preserved=True,metadata_M1_separately_reviewed=True,immutable_native_journal_snapshots_used=True))
write(RUN/'stabilized-decision-v1.json',dict(stage='stabilized',effective_mathematical_contract=CONTRACT.as_posix(),source_review_receipt=(RUN/'source-contract-receipt-v3.json').as_posix(),source_review_sha256=sha(RUN/'source-contract-receipt-v3.json'),effective_neutral_context='blind-packet-v2.md',context_repair_M1='satisfied by separate review after actual standalone v2 compilation and distinct reconstruction',frozen_raw_headers=load(RUN/'draft-freeze-v1.json')['headers'],native_normalized_headers=load(CONTRACT/'native-statement-fingerprints-v1.json'),dependency_ready='Actual pinned9API/2target types + accepted real2 same-function producers; single injectivepreimage and subset route.',new_definitions=0,allowed_new_public_proofs=2,proof_compiled=False,source_package_accepted=False,chapter_complete=False,goal_complete=False))
native('failed-context-trial-v1','trial-log','--task',TASK,'--role','lower','--kind','attempt','--status','failed','--run-id',RUN.name,'--attempt-id','UNCOUNTABLE-CONTEXT-V1','--statement-hash',load(CONTRACT/'native-statement-fingerprints-v1.json')['convex_uncountable_nondifferentiability'],'--verifier-evidence',RUN/'neutral-context-v1-01.log','--harness','hierarchical','--progress-class','no-progress','--error-signature','Standalone neutral packet imports missing DifferentiableAt','--notes','Actual context-only failure; corrected import context independently compiled/redecoded/reviewed, source math headers unchanged. No theorem progress implied.')
event('stabilized',dict(decision=(RUN/'stabilized-decision-v1.json').as_posix(),metadata_M1_separately_satisfied=True,headers_unchanged=True))
event('proving',dict(lower_route='injective second-axis map -> source closedsegment uncountable -> same-function ambient nonsmooth-locus uncountable',owned_files=[PUBLIC.as_posix(),CANARY.as_posix()],proof_compiled=False))
write(RUN/'30_worker-route-v1.md','Actual worker starts after distinct source-target CONTRACT and separately accepted missing-import repair. Exactly two public proof headers fixed, zero definitions. Injective second-coordinate embedding/countablepreimage/Icc cardinal contradiction then actual source-segment-to-nonsmooth-locus inclusion. No alternate countability oracle/general cardinality project. Three planned genuine canaryproofs: uncountable segment intersection, countable distinct endpointpair, countable scalarabs nonsmoothlocus. Any target edit requires new version/review; body repair only on this route.')
print('Exact two public targets stabilized/proving; context failure/repaired review retained, actual bodies pending.')
