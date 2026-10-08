from common_integrated_v2 import *

fixed_integrated()
assert load(RUN/'final-reader-inputs-v4.json')['fixed_input_count'] == 876
text = (RUN/'common_accepted_v3.py').read_text(encoding='utf8')
for old,new in [('final-reader-receipt-v3','final-reader-receipt-v4'),('FINAL-metadata-snapshots-v3','FINAL-metadata-snapshots-v4'),
    ('final-reader-inputs-v3','final-reader-inputs-v4'),('== 846','== 876')]:
    assert old in text
    text=text.replace(old,new)
write(RUN/'common_accepted_v4.py',text)
text=(RUN/'record-acceptance-v3.py').read_text(encoding='utf8')
for old,new in [('common_accepted_v3','common_accepted_v4'),('final-reader-receipt-v3','final-reader-receipt-v4'),
    ('accepted-reader-discharge-v3','accepted-reader-discharge-v4'),('accepted-decision-v3','accepted-decision-v4'),
    ('memory-digest-accepted-v3','memory-digest-accepted-v4'),('retrieval-index-accepted-v3','retrieval-index-accepted-v4'),
    ('accepted-reviewer-trial-v3','accepted-reviewer-trial-v4'),('accepted-scoped-trials-v3','accepted-scoped-trials-v4'),
    ('accepted-lifecycle-v3','accepted-lifecycle-v4'),('accepted-frontier-refresh-v3','accepted-frontier-refresh-v4'),
    ('accepted-frontier-shadow-v3','accepted-frontier-shadow-v4'),('accepted-frontier-v3','accepted-frontier-v4'),
    ('accepted-memory-record-v3','accepted-memory-record-v4'),('accepted-retrieval-record-v3','accepted-retrieval-record-v4'),
    ('40_reviewer_decision-v3','40_reviewer_decision-v4'),('native-acceptance-overlay-v3','native-acceptance-overlay-v4'),
    ('FINAL846','FINAL876')]:
    assert old in text,old
    text=text.replace(old,new)
text=text.replace('fresh v9/F1F2 distinct review required.',
    'fresh v9/F1F2 distinct review satisfied. Rejected FINALv3 stale prospective pointer M1 retained; operative publicationv4/title-bodyv4 distinct metadata repair review required.')
write(RUN/'record-acceptance-v4.py',text)
text=(RUN/'deliver-reviewed-v3.py').read_text(encoding='utf8')
for old,new in [('common_accepted_v3','common_accepted_v4'),('native-acceptance-overlay-v3','native-acceptance-overlay-v4'),
    ('final-reader-receipt-v3','final-reader-receipt-v4'),('source-scope-pre-publication-v3','source-scope-pre-publication-v4'),
    ("'pre-publication-v3'","'pre-publication-v4'"),('scoped-diff-pre-publication-v3','scoped-diff-pre-publication-v4'),
    ('prospective-pr-title-v3','prospective-pr-title-v4'),('prospective-pr-body-v3','prospective-pr-body-v4'),
    ('PR-payload-v3','PR-payload-v4'),('contributor-pre-publication-v3','contributor-pre-publication-v4'),
    ('branch-push-v3','branch-push-v4'),('draft-PR-create-v3','draft-PR-create-v4'),('created-PR-v3','created-PR-v4')]:
    assert old in text,old
    text=text.replace(old,new)
text=text.replace("    accepted_fixed()\n    head =", "    accepted_fixed()\n    assert 'prospective-pr-title/body-v4' in (RUN/'proposed-publication-v4.md').read_text(encoding='utf8')\n    assert sha(RUN/'prospective-pr-body-v4.md') == sha(RUN/'prospective-pr-body-v3.md')\n    head =")
write(RUN/'deliver-reviewed-v4.py',text)
text=(RUN/'close-delivery-v3.py').read_text(encoding='utf8')
for old,new in [('common_accepted_v3','common_accepted_v4'),('deliver_reviewed_v3','deliver_reviewed_v4'),
    ('deliver-reviewed-v3','deliver-reviewed-v4'),('created-PR-v3','created-PR-v4'),('app-attach-v3','app-attach-v4'),
    ('accepted-decision-v3','accepted-decision-v4'),('delivery-obligations-overlay-v3','delivery-obligations-overlay-v4'),
    ('delivery-handoff-v3','delivery-handoff-v4'),('contributor-delivery-v3','contributor-delivery-v4'),
    ('scoped-diff-delivery-v3','scoped-diff-delivery-v4'),("'delivery-v3'","'delivery-v4'"),
    ('source-scope-delivery-v3','source-scope-delivery-v4'),('fresh FINALv3','fresh FINALv4')]:
    assert old in text,old
    text=text.replace(old,new)
write(RUN/'close-delivery-v4.py',text)
text=(RUN/'final-direct-audit-v3.py').read_text(encoding='utf8').replace('common_accepted_v3','common_accepted_v4').replace('created-PR-v3','created-PR-v4').replace('prospective-pr-body-v3','prospective-pr-body-v4')
write(RUN/'final-direct-audit-v4.py',text)
import ast
for filename in ['common_accepted_v4.py','record-acceptance-v4.py','deliver-reviewed-v4.py','close-delivery-v4.py','final-direct-audit-v4.py']:
    ast.parse((RUN/filename).read_text(encoding='utf8'),filename=filename)
print('Five v4 action helpers parse; actual accepted FINALv4 still required before execution.')
