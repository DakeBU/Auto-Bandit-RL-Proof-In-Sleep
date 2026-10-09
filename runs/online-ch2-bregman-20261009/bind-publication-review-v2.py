from common import *
fixed()
rp=RUN/'canary-BODY-publication-review-v2.json'
assert sha(rp)=='0856c03edebfef8f680329c47ce4347edcf1c4613f26ec4ea428b666d04873f6'
r=load(rp)
assert r['BODY_verdict']==r['materialization_verdict']=='accepted' and not r['required_repairs']
assert load(CONTRACT/'exact-publication-plan-v2.json')['rows']==r['approved_five_rows']
write(RUN/'publication-review-binding-v2.json',dict(review_sha256=sha(rp),plan_sha256=sha(CONTRACT/'exact-publication-plan-v2.json'),source_review_report_sha256=sha(RUN/'canary-BODY-publication-review-v2.md'),bounded_materialization_only=True,chapter_complete=False,whole_Goal_status='ACTIVE'))
fixed()
