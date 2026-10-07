"""Stabilize only the separately source-reviewed locator repair and exact unchanged targets."""
from common_v4 import *
fixed();r=load(RUN/'source-contract-receipt-v2.json')
assert r['actor']['task']=='/root/source_reviewer' and r['verdict']=='accepted-with-explicit-delta'
assert r['repair_verdict']['M1']['verdict']=='satisfied' and sha(r['report'])==r['report_sha256']
for k in ['required_mathematical_repairs','mathematical_repairs','required_metadata_repairs']:assert not r.get(k,[])
reviewed={p['path']:p['sha256'] for p in r['reviewed_files']}
for row in load(RUN/'source-contract-inputs-v2.json')['rows']:assert reviewed[row['path']]==row['sha256']==sha(row['path']),row['path']
rows=[]
for v in [1,2]:
 receipt=RUN/('source-contract-receipt-v'+str(v)+'.json');review=load(receipt)
 for p in ['runs/lifecycle_sessions.jsonl','runs/trials.jsonl']:
  expected=next(a['sha256'] for a in review['reviewed_files'] if a['path']==p);h=hashlib.sha256();out=b'';match=None
  for line in Path(p).read_bytes().splitlines(keepends=True):
   out+=line;h.update(line)
   if h.hexdigest()==expected:match=out;break
  assert match is not None,(p,v)
  dest=RUN/'snapshots'/('contract-v'+str(v)+'-reviewed-'+p.replace('/','--')+'.txt');write(dest,match);assert sha(dest)==expected
  rows.append(dict(receipt=receipt.as_posix(),path=p,sha256=expected,resolved=dest.as_posix()))
write(RUN/'contract-native-prefix-bindings-v1.json',dict(status='passed',rows=rows,original_rejected_v1_preserved=True))
write(RUN/'stabilized-decision-v2.json',dict(stage='stabilized',effective_contract=CONTRACT.as_posix(),source_review_receipt=(RUN/'source-contract-receipt-v2.json').as_posix(),source_review_sha256=sha(RUN/'source-contract-receipt-v2.json'),metadata_repair_M1='separately accepted, v1 preserved',source_fingerprints_unchanged=True,statement_raw_fingerprints=load(RUN/'draft-freeze-v1.json')['headers'],native_normalized_fingerprints=load(CONTRACT/'native-statement-fingerprints-v1.json'),dependency_ready='Actual3target propositions and15pinned APItypes elaborated; normprojection/horizontal derivative/scalarabs/segment finite route.',allowed_new_public_proofs=3,allowed_new_public_definitions=1,proof_compiled=False,source_package_accepted=False,chapter_complete=False,goal_complete=False))
event('stabilized',dict(decision=(RUN/'stabilized-decision-v2.json').as_posix(),metadata_M1_repair_reviewed=True,terminal_headers_unchanged=True))
event('proving',dict(lower_route='normconvex coordinatepullback -> smooth horizontal restriction and abs-at0 contradiction -> allclosedsegment',owned_files=[PUBLIC.as_posix(),CANARY.as_posix()],proof_compiled=False))
write(RUN/'30_worker-route-v1.md','Actualworker starts onlyafter separatelyacceptedCONTRACTv2metadatarepair. Publicdefinition/threeheaders fixed. Convexnorm throughactualfirstcoordinate linearmap; differentiate along x+t*e0 and contradictactual scalarabs at0; actualclosedsegment firstcoordinate0. Allowedproofrepairbodyonly; anyterminalchange needsversion/review. All5planned canaryscenario proofs pendingactualcompilation. No cardinality terminal or chapterclosure.')
print('Source CONTRACTv2 stabilized/proving recorded; exact1definition/3proof headers unchanged, bodypending.')
