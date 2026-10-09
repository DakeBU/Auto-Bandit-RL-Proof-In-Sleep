from common import *
fixed()
p=RUN/'publication-helper-review-v1.json';r=load(p)
assert sha(p)=='2a1f13cde804d65b60f7711184fcd38a796511a79b799f7189e4e1b3c20e61dc'
assert r['verdict']=='accepted-with-explicit-delta' and not r['required_repairs']
assert sha(r['report'])==r['report_sha256']
assert sha(r['input_manifest'])==r['input_manifest_sha256']
for row in load(r['input_manifest'])['rows']:assert sha(row['path'])==row['sha256']
assert sha(RUN/'six-BODY-review-v1.json')==r['BODY_receipt_sha256']
assert sha(RUN/'publication-plan-review-v1.json')==r['plan_receipt_sha256']
for p in [RUN/n for n in ['prospective-contribution-v1.json','publication-review-binding-v1.json','publication-materialized-v1.json']]+[ROOT/'research-wiki/contribution-contracts'/(TASK+'.json')]:assert not p.exists(),p
write(RUN/'publication-caller-preflight-v1.json',dict(review_sha256=sha(RUN/'publication-helper-review-v1.json'),
    report_sha256=r['report_sha256'],input_manifest_sha256=r['input_manifest_sha256'],all_helper_rows_rehashed=True,
    BODY_and_plan_receipts_matched=True,all_four_new_paths_absent=True,external_caller_check=True,self_enforcement_claim=False))
capture('publication-materializer-command-v1',sys.executable,'-B','-X','utf8',RUN/'materialize-publication-v1.py')
from publication_guard_v1 import fixed as published_fixed
published_fixed()
print('Exact reviewed materializer completed and post-state guard passed.')
