from common_v1 import *
fixed()
r=load(RUN/'general-init-BODY-receipt-v1.json')
assert sha(RUN/'general-init-BODY-receipt-v1.json')=='ab038b4c25f861d2c0a10b102e1450a89c3a19a515d1c24e97838d3ffa467381'
assert r['verdict']=='accepted-with-explicit-delta' and not r['required_blocking_repairs']
assert sha(r['report'])==r['report_sha256'] and sha(r['input_index'])==r['input_index_sha256']
for row in load(r['input_index'])['rows']:assert sha(row['path'])==row['sha256'],row['path']
assert r['approved_future_exact_scope']==load(CONTRACT/'future-mutation-scope-draft-v3.json')
plan=load(CONTRACT/'exact-import-plans-draft-v3.json')['rows'][0]
p=Path(plan['path']);before=Path(plan['snapshot'])
assert p.read_bytes()==before.read_bytes() and sha(p)==plan['baseline_sha256']
result=before.read_bytes()+plan['append_exact_utf8'].encode('utf8')
assert hashlib.sha256(result).hexdigest()==plan['permitted_result_sha256']
p.write_bytes(result)
write(RUN/'root-integration-receipt-v1.json',dict(review_receipt_sha256=sha(RUN/'general-init-BODY-receipt-v1.json'),review_input_count_verified=293,scope_sha256=sha(CONTRACT/'future-mutation-scope-draft-v3.json'),exact_plan=plan,actual_result_sha256=sha(p),old_root_raw_snapshot_preserved=True,only_exact_reviewed_import_appended=True,Tests_import_pending_canary_BODY=True,new_production_bodies=4,new_source_objects_final_accepted=0,chapter_complete=False,goal_complete=False))
from common_proving_v2 import fixed as stage_fixed
stage_fixed()
write(RUN/'memory-digest-proving-v2.md','Four frozen G001-G004 actual public producers compiled, whole-type values and standard complete axioms/four fences/safe checks passed;9required direct VALUE dependencies. Distinct BODY accepted-with-explicit-delta, source17 inventory complete at contract level, original16/old50 immutable. Root exact import appended after BODY under reviewed prefix snapshot. Source object acceptance and wholechapter/rootTests/fullharness/contributor/registry/site/FINAL/delivery pending. SourceReviewer v4 corrects initial0 observations0,1 bestregret+1/2 (first-loss correction -1/4); actuallegalFTL nonnegative by prefix minima. Old v3 false reviewer example preserved and explicitly superseded. G4 BODY seven-slot excluded-scope retains stale proposed-tense from decoder; actual BODY evidence separately confirms proof existence, carry forward current compiled/BODY-ready wording. General-init terminal1+tail, upperepsilon and TRUEbestaverage0 distinct; no ordinaryfixedcomparatorlimit. Whole1-16GoalACTIVE/C2partial/C3-16unenumerated-null/requiredappendices; no merge/main/live/retirement.')
print('293 BODY RAW verified; exact reviewed root import integrated, Tests/canary and full chapter gates pending.',flush=True)
