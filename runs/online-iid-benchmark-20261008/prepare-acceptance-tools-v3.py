from common_integrated_v2 import *

fixed_integrated()
assert load(RUN/'final-reader-inputs-v3.json')['fixed_input_count'] == 846
current_site = load(RUN/'registry-v9.json')['source_commit']
text = (RUN/'common_accepted_v2.py').read_text(encoding='utf8')
for old, new in [('final-reader-receipt-v2', 'final-reader-receipt-v3'), ('FINAL-metadata-snapshots-v2', 'FINAL-metadata-snapshots-v3'),
    ('final-reader-inputs-v2', 'final-reader-inputs-v3'), ('== 778', '== 846')]:
    assert old in text
    text = text.replace(old, new)
text = text.replace("requirements = load(RUN/'stabilized-contract-v2.json')", "assert r.get('inputs_unchanged') and r.get('before_after_raw_hashes_match')\n    requirements = load(RUN/'stabilized-contract-v2.json')")
write(RUN/'common_accepted_v3.py', text)
text = (RUN/'record-acceptance-v2.py').read_text(encoding='utf8')
for old, new in [('common_accepted_v2','common_accepted_v3'), ('final-reader-receipt-v2','final-reader-receipt-v3'),
    ('accepted-reader-discharge-v2','accepted-reader-discharge-v3'), ('accepted-decision-v2','accepted-decision-v3'),
    ('registry-v6','registry-v9'), ('pixel-review-v6','pixel-review-v9'), ('memory-digest-accepted-v2','memory-digest-accepted-v3'),
    ('retrieval-index-accepted-v2','retrieval-index-accepted-v3'), ('accepted-reviewer-trial-v2','accepted-reviewer-trial-v3'),
    ('accepted-scoped-trials-v2','accepted-scoped-trials-v3'), ('accepted-lifecycle-v2','accepted-lifecycle-v3'),
    ('accepted-frontier-refresh-v2','accepted-frontier-refresh-v3'), ('accepted-frontier-shadow-v2','accepted-frontier-shadow-v3'),
    ('accepted-frontier-v2','accepted-frontier-v3'), ('accepted-memory-record-v2','accepted-memory-record-v3'),
    ('accepted-retrieval-record-v2','accepted-retrieval-record-v3'), ('40_reviewer_decision-v2','40_reviewer_decision-v3'),
    ('native-acceptance-overlay-v2','native-acceptance-overlay-v3'), ('FINAL778','FINAL846'),
    ('Clean af28b5d local v6', 'Clean '+current_site+' local v9'),
    ('clean af28b5d586c8d1e6cf4d5a901466050356e6ab6d local v6source', 'clean '+current_site+' local v9source')]:
    assert old in text, old
    text = text.replace(old, new)
text = text.replace('Frozen8terminal contract progresses8->0 ONLY.',
    'Frozen8terminal contract progresses8->0 ONLY. Rejected FINALv2/F1/F2 reader inversion and missing t>0 retained; exact reader-only repair/fresh v9/F1F2 distinct review required.')
write(RUN/'record-acceptance-v3.py', text)
print('Conditional v3 acceptance tools prepared; not executed; reviewer/native gates remain separate.')
