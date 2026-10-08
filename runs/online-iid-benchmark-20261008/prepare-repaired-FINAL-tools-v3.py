from common_integrated_v2 import *

fixed_integrated()
assert load(RUN/'final-reader-receipt-v2.json')['verdict'] == 'rejected'
text = (RUN/'prepare-final-v2.py').read_text(encoding='utf8')
for old, new in [('pixel-review-v6','pixel-review-v9'), ('registry-v6','registry-v9'),
    ('site-build-v6','site-build-v9'), ('site-check-v6','site-check-v9'), ('registry-check-v6','registry-check-v9'),
    ('current-reader-capture-v6','current-reader-capture-v9'), ('-site-v6','-site-v9'),
    ('FINAL-review-v2-', 'FINAL-review-v3-'), ('FINAL-metadata-snapshots-v2','FINAL-metadata-snapshots-v3'),
    ('prospective-pr-title-v2','prospective-pr-title-v3'), ('prospective-pr-body-v2','prospective-pr-body-v3'),
    ('proposed-publication-v2','proposed-publication-v3'), ('final-reader-packet-v2','final-reader-packet-v3'),
    ('final-reader-inputs-v2','final-reader-inputs-v3'), ('final-reader-review-v2.md and final-reader-receipt-v2.json',
    'final-reader-review-v3.md and final-reader-receipt-v3.json'),
    ('scoped-diff-pre-FINAL-v8','scoped-diff-pre-FINAL-v10'), ("'pre-FINAL-v8'", "'pre-FINAL-v10'"),
    ('current v6 images','current v9 images'), ('Current clean af28b5d v6 browser passes.',
    'Previous clean af28b5d v6 browser passed geometry but was semantically rejected; current v9 must pass both.'),
    ('Applicable clean local v6 site','Applicable clean local v9 site'),
    ('Current site source_dirty=false,lean_verified=true from clean af28b5d,',
    'Current v9 site source_dirty=false,lean_verified=true from its exact clean reader-repair commit,')]:
    assert old in text, old
    text = text.replace(old, new)
text = text.replace('Write ONLY final-reader-review-v3.md',
    'REPAIR REVIEW: rejected FINALv2 report4430558222eef89fc4d481643a4c2e2cfe8b816aad07cd0d6d3ffb562dd3e0e3/receiptf414064aa437d80a275e5d172748a1795c9589e1445faedd81d3d3cf6b0dd78c remain immutable. Actual F1 reversed min/expectation wording in eight Intuition fields; F2 lacked t>0 in note6 formula. ROOT original pixel review missed both. Reader-semantic-repair-v9 snapshots original highlights bytes and changes ONLY these nine fields; all statements/bodies/source/CONTRACT/BODY unchanged. New v9 site and ALL14 fresh pixels must be independently reviewed, with explicit repair_verdicts.F1/F2. Do not resolve rejection by formulas elsewhere. Old FINAL778 bindings for original reader JSON are historical and resolve through reader-before-semantic-repair-v6.json.raw; no other old input change allowed except documented future own metadata. Exact repair-diff review is required. Old native acceptance-v2/common_accepted_v2 helper was PREPARED but NOT EXECUTED after rejection; no native accepted trial exists yet.\n\nWrite ONLY final-reader-review-v3.md')
text = text.replace('Distinct staged automated decoder/source-reviewer CONTRACT/BODY/FINAL records',
    'A rejected FINALv2 exposed reversed reader min/expectation wording and a missing t>0 qualifier; reader-only repair and fresh FINAL preserve that failure. Distinct staged automated decoder/source-reviewer CONTRACT/BODY/FINAL records')
text = text.replace('Current clean af28b5d v6 site passed browser/registry/site checks;',
    'Original af28b5d v6 site passed geometry but FINALv2 rejected reader semantics; reader-only repair/new v9 is required;')
write(RUN/'prepare-final-v3.py', text)
text = (RUN/'record-pixels-v6.py').read_text(encoding='utf8').replace('formula-render-v6','formula-render-v9').replace('pixel-review-v6','pixel-review-v9')
text = text.replace("'af28b5d586c8d1e6cf4d5a901466050356e6ab6d'", "load(RUN/'registry-v9.json')['source_commit']")
text = text.replace('Current viewport and source card are unclipped after the separately recorded label-only repairs.',
    'Current viewport/source card are unclipped; original v6 ROOT missed F1/F2, retained rejected evidence, and current v9 is freshly reviewed.')
text = text.replace('Compiled route/package labels do not claim a textbook chapter or total Goal is complete.',
    'All eight intuition fields put expectation inside fixed-comparator minimization; note6 averaging equation is explicitly t>0. Compiled route/package labels do not claim chapter/Goal completion.')
write(RUN/'record-pixels-v9.py', text)
print('Fresh repaired FINALv3 tools prepared; no acceptance executed.')
