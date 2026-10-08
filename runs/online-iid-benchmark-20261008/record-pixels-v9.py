from common_integrated_v2 import *

fixed_integrated()
r = load(RUN / 'formula-render-v9.json')
assert len(r['images']) == 14
assert r['site_source_commit'] == load(RUN/'registry-v9.json')['source_commit']
for row in r['images']:
    assert sha(row['path']) == row['sha256']
write(RUN / 'pixel-review-v9.json', dict(status='passed', actor='/root',
    all_14_individually_viewed=True,
    method='Actual functions view_image original-detail calls on all fourteen current images across the continuation; no synthetic preview.',
    images=r['images'], formula_report_sha256=sha(RUN / 'formula-render-v9.json'),
    site_source_commit=r['site_source_commit'],
    checks=['Current viewport/source card are unclipped; original v6 ROOT missed F1/F2, retained rejected evidence, and current v9 is freshly reviewed.',
        'Eight notes show fixed expected minimum, same-law variance and actual strict-past excess formulas with explicit partial deterministic scope.',
        'Four catalogue panels show full types/source links with actual built-in wrapping; no horizontal clipping.',
        'Known population mean is explicitly an oracle; finite normalization does not claim asymptotic success.',
        'Long technical notes were expanded for audit; exact statements remain separately accessible.',
        'All eight intuition fields put expectation inside fixed-comparator minimization; note6 averaging equation is explicitly t>0. Compiled route/package labels do not claim chapter/Goal completion.'],
    no_generated_site_edits=True, not_live_or_physical_device_evidence=True,
    independent_FINAL_reader_review_pending=True, chapter_complete=False, goal_complete=False))
print('Actual current fourteen images individually viewed; distinct FINAL still required.')
