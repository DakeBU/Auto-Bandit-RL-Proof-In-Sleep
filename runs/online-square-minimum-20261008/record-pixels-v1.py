from common_integrated_v1 import *

fixed_integrated()
r = load(RUN / 'formula-render-v1.json')
assert len(r['images']) == 12
for row in r['images']: assert sha(row['path']) == row['sha256']
write(RUN / 'pixel-review-v1.json', dict(status='passed', actor='/root', all_12_individually_viewed=True,
    method='Actual functions view_image original-detail calls on all twelve current images, not a synthetic or old preview.',
    images=r['images'], formula_report_sha256=sha(RUN / 'formula-render-v1.json'),
    checks=['Source card shows actual mean/minimum, signed same-process regret, positive-horizon log and sharp-tail formulas.',
        'Six current proof notes show the intended statements with source deltas/remaining IID and book scope visible.',
        'Four catalogue panels show exact wrapped definition/theorem types and source links, without horizontal clipping.',
        'The canonical route compiled label is expressly separate from whole textbook chapter completion.',
        'Actual DOM browser report has zero MathJax errors and no source formula horizontal scrollers.'],
    no_generated_site_edits=True, not_live_or_physical_device_evidence=True, chapter_complete=False, goal_complete=False))
print('Actual current12 images individually viewed; source/reader FINAL still required.')
