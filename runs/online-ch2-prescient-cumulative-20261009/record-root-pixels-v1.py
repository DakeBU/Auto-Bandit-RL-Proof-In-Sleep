from publication_guard_v3 import *
fixed()
b = load(RUN / 'formula-render-v1-browser.json')
r = load(RUN / 'registry-inspected-v1.json')
assert len(b['images']) == 12 and not b['errors'] and not b['failed']
assert b['url'].startswith('file:///')
write(RUN / 'root-reader-pixel-review-v1.json', dict(
    actor='/root', tool='view_image detail original', image_count=12,
    images=rows(RUN / n for n in b['images']), source_commit=r['source_commit'],
    actual_personal_inspection=True,
    observations='Personally viewed all12 originals: first viewport, one new source card, five production notes, five individual production catalogue declarations. All displayed formulas render, ordered terminal/movement negative terms remain legible, variable sharp formula qualifies positivity beforeT and nonincrease between played rounds. Source card preserves the conditional-success/full-source-open boundary. Exact Lean disclosures remain folded in reader notes; built-in catalogue wrap fits the complete statements without the next declaration. No visible clipping or math-error in these captures.',
    unresolved_reader_concern='Shared normalization paragraph says Variable steps require T>0 and nonincrease only between played rounds. The common divergence_sum actually permits T=0 and arbitrary positive played schedule. Scope ambiguity sent to distinct source reviewer as reader-scope-triage-v1; not yet accepted by root or FINAL.',
    limits='Actual local file URI desktop1440 only, not HTTP/live/deployment/mobile/all-viewports. Root inspection does not discharge distinct FINAL personal viewing. No prior policy-rejected HTTP service retried.',
    package_accepted=False, chapter_complete=False, whole_Goal_status='ACTIVE'))
print('Actual12 original root inspection recorded; reader scope triage and FINAL pending.')
