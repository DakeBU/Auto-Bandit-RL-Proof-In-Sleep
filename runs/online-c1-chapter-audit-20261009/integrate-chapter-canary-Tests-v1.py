from common_proving_v2 import *
fixed()
r=load(RUN/'chapter-canary-BODY-receipt-v1.json')
assert sha(RUN/'chapter-canary-BODY-receipt-v1.json')=='387496d0a7ddf05a3dac7568d053e8d9bfba67e620ae9a2614e80df8d0abbe1a'
assert r['verdict']=='accepted-with-explicit-delta' and not r['required_blocking_repairs']
assert sha(r['report'])==r['report_sha256'] and sha(r['input_index'])==r['input_index_sha256']
for row in load(r['input_index'])['rows']:assert sha(row['path'])==row['sha256'],row['path']
assert r['exact_Tests_import_now_permitted']
assert sha(ROOT/'Tests/OnlineLearningChapterAuditCanary.lean')==r['test_module_sha256']==load(RUN/'chapter-canary-public-readiness-v1.json')['Test_sha256']
plan=next(p for p in load(CONTRACT/'exact-import-plans-draft-v3.json')['rows'] if Path(p['path']).name=='Tests.lean')
p=Path(plan['path']);before=Path(plan['snapshot'])
assert p.read_bytes()==before.read_bytes() and sha(p)==plan['baseline_sha256']
result=before.read_bytes()+plan['append_exact_utf8'].encode('utf8')
assert hashlib.sha256(result).hexdigest()==plan['permitted_result_sha256']
p.write_bytes(result)
write(RUN/'Tests-integration-receipt-v1.json',dict(review_receipt_sha256=sha(RUN/'chapter-canary-BODY-receipt-v1.json'),review_input_count_verified=925,exact_plan=plan,actual_result_sha256=sha(p),old_Test_root_RAW_preserved=True,only_exact_reviewed_import_appended=True,actual_canary_proofs=27,canonical_new_proofs=4,additional_source_family_count=1,chapter_complete=False,goal_complete=False))
fixed()
print('925 BODY RAW verified; exact reviewed Tests root import appended; full gates pending.',flush=True)
