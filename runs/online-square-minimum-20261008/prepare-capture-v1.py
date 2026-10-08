from common_integrated_v1 import *

fixed_integrated()
old = Path('runs/online-no-regret-20261008/capture-reader-v1.cjs')
s = old.read_text(encoding='utf8')
replacements = [
    ("['LimitNoRegret','NoRegretCounterexample.loss','limitNoRegret_iff_noRegret_of_converges','NoRegretCounterexample.strict_separation']",
     "['squaredBestRegret','squaredLoss_minimum_eq','squaredBestRegret_eq_comparatorRegret','meanPredict_bestRegret_refined']"),
    ("['noRegret_limit_nonpos','limitNoRegret_implies_noRegret','limitNoRegret_iff_noRegret_of_converges','NoRegretCounterexample.regret_eq','NoRegretCounterexample.no_limit','NoRegretCounterexample.strict_separation']",
     "['guessing_prefix_minimum','squaredLoss_minimum_eq','squaredBestRegret_eq_comparatorRegret','comparatorRegret_le_squaredBestRegret','meanPredict_bestRegret_bound','meanPredict_bestRegret_refined']"),
    ("['article.source-theorem-card',9,'no-regret-source-card-v1.png',1,10]", "['article.source-theorem-card',10,'square-minimum-source-card-v1.png',1,11]"),
    ('.length===13', '.length===14'), ('actualSourceGuideMathContainers:13', 'actualSourceGuideMathContainers:14'),
    ('actual-current-no-regret-panels-and-catalog-captured', 'actual-current-square-minimum-panels-and-catalog-captured')]
for before, after in replacements:
    assert s.count(before) == 1, before
    s = s.replace(before, after)
write(RUN / 'capture-reader-v1.cjs', s)
write(RUN / 'capture-tool-provenance-v1.json', dict(template=old.as_posix(), template_sha256=sha(old),
    edits='Select exact current minimum source card, six proof notes and four catalog definitions/types; expected actual source formula count14.',
    current_source_not_modified=True, capture_not_yet_run=True))
print('Current square-minimum DOM/pixel capture prepared; no site generated files edited.')
