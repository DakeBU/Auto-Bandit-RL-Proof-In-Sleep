from common_integrated_v2 import *

fixed_integrated()
r = load(RUN / 'formula-render-v6.json')
assert len(r['images']) == 14
assert r['site_source_commit'] == 'af28b5d586c8d1e6cf4d5a901466050356e6ab6d'
for row in r['images']:
    assert sha(row['path']) == row['sha256']
write(RUN / 'pixel-review-v6.json', dict(status='passed', actor='/root',
    all_14_individually_viewed=True,
    method='Actual functions view_image original-detail calls on all fourteen current images across the continuation; no synthetic preview.',
    images=r['images'], formula_report_sha256=sha(RUN / 'formula-render-v6.json'),
    site_source_commit=r['site_source_commit'],
    checks=['Current viewport and source card are unclipped after the separately recorded label-only repairs.',
        'Eight notes show fixed expected minimum, same-law variance and actual strict-past excess formulas with explicit partial deterministic scope.',
        'Four catalogue panels show full types/source links with actual built-in wrapping; no horizontal clipping.',
        'Known population mean is explicitly an oracle; finite normalization does not claim asymptotic success.',
        'Long technical notes were expanded for audit; exact statements remain separately accessible.',
        'Compiled route/package labels do not claim a textbook chapter or total Goal is complete.'],
    no_generated_site_edits=True, not_live_or_physical_device_evidence=True,
    independent_FINAL_reader_review_pending=True, chapter_complete=False, goal_complete=False))
print('Actual current fourteen images individually viewed; distinct FINAL still required.')
