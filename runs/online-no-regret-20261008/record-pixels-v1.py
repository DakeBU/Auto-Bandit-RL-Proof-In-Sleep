from common_integrated_v2 import *
fixed_integrated()
r = load(RUN / 'formula-render-v1.json')
assert len(r['images']) == 12
for row in r['images']:
    assert sha(row['path']) == row['sha256']
assessments = [
    'Current route viewport: scoped compiled route and remaining chapter boundary visible.',
    'Source card: ordinary limit, eventual upper condition and finite convergence premise remain distinct; formulas visible.',
    'Public note 1: supplied actual finite real limit and upper condition yield nonpositive limit.',
    'Public note 2: actual nonpositive finite limits imply the upper condition.',
    'Public note 3: equivalence retains convergence for every fixed feasible comparator.',
    'Public note 4: one fixed affine loss stream telescopes to the signed prefix regret.',
    'Public note 5: actual upper condition and positive even/odd normalized values remain visible.',
    'Public note 6: same stream strict separation; no ordinary-limit claim for the mean learner.',
    'Catalogue LimitNoRegret: exact public definition header and separate literal-limit explanation visible.',
    'Catalogue loss: exact affine loss definition header and exogenous-stream explanation visible.',
    'Catalogue conditional iff: exact quantified finite-convergence premise wraps without clipping.',
    'Catalogue strict separation: same Icc domain, same loss and constant-zero prediction on both sides visible.'
]
rows = [dict(**row, root_individually_viewed=True, assessment=a)
        for row, a in zip(r['images'], assessments)]
write(RUN / 'pixel-review-v1.json', dict(
    status='passed', actor='/root', stage='actual local browser pixels',
    site_source_commit=r['site_source_commit'],
    render_record_sha256=sha(RUN / 'formula-render-v1.json'),
    browser_report_sha256=r['browser_report_sha256'],
    DOM_sha256=r['DOM_sha256'], images=rows,
    all_12_individually_viewed=True,
    observed_math='Ordinary limit and upper semantics separated; finite-convergence premise retained; signed even -1 and odd 0 on positive horizons; no formula clipping observed.',
    limits='Local desktop browser only; no physical-device, deployment, live-site, chapter acceptance or source-review assertion. Generated catalogue exposes exact statements and source links, not generated proof bodies.'
))
print('12 actual image hashes bound; root individual pixel review recorded.')
