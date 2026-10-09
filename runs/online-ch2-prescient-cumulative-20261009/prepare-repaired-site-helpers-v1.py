from common import *
# Prospective only: no canonical writes or commands. Executed after exact repair review.
s = (RUN / 'verify-registry-v2.py').read_text(encoding='utf8')
s = s.replace('from publication_guard_v3 import *', 'from publication_guard_v4 import *')
s = s.replace("'registry-inspected-v1.json'", "'registry-inspected-v2.json'")
write(RUN / 'verify-registry-v3.py', s)
s = (RUN / 'prepare-stage-v4.py').read_text(encoding='utf8')
for old, new in [('from publication_guard_v3 import *', 'from publication_guard_v4 import *'),
    ('exact-publication-plan-v2.json', 'exact-publication-plan-v3.json'),
    ('candidate-stage-plan-v3.json', 'candidate-stage-plan-v4.json'),
    ("'candidate-stage-v3'", "'candidate-stage-v4'"),
    ("'candidate-full-diff-check-v3'", "'candidate-full-diff-check-v4'"),
    ('exact-RAW-line-ending-snapshots-v3.json', 'exact-RAW-line-ending-snapshots-v4.json'),
    ('candidate-diff-audit-v3.json', 'candidate-diff-audit-v4.json')]:
    assert old in s, old
    s = s.replace(old, new)
write(RUN / 'prepare-stage-v5.py', s)
s = (RUN / 'commit-and-build-site-v4.py').read_text(encoding='utf8')
for old, new in [('from publication_guard_v3 import *', 'from publication_guard_v4 import *'),
    ('candidate-diff-audit-v3.json', 'candidate-diff-audit-v4.json'),
    ('candidate-stage-plan-v3.json', 'candidate-stage-plan-v4.json'),
    ('candidate-commit-v1', 'candidate-commit-v2'),
    ('Prove same-run prescient Bregman cumulative regret bounds', 'Clarify individual prescient cumulative interface assumptions'),
    ('contributor-stack-v1', 'contributor-stack-v2'), ('contributor-main-v1', 'contributor-main-v2'),
    ('site-build-v1', 'site-build-v2'), ('site-check-v1', 'site-check-v2'),
    ('registry-command-v1', 'registry-command-v2'), ('verify-registry-v2.py', 'verify-registry-v3.py'),
    ('clean-candidate-site-binding-v1.json', 'clean-candidate-site-binding-v2.json')]:
    assert old in s, old
    s = s.replace(old, new)
write(RUN / 'commit-and-build-site-v5.py', s)
s = (RUN / 'capture-prescient-cumulative-reader-v1.cjs').read_text(encoding='utf8')
s = s.replace('-v1.png', '-v2.png').replace('formula-render-v1-', 'formula-render-v2-')
needle = "if(file==='public-note-3-v2.png')"
assert s.count(needle) == 1
s = s.replace(needle, "const prose=await panel.innerText();if(!prose.includes('The shared iterate_divergence_sum interface allows every natural horizon T')||!prose.includes('Only iterate_variable_sharp and iterate_variable_regret require T>0'))throw Error('Repaired interface-scope prose missing');\n   " + needle)
write(RUN / 'capture-prescient-cumulative-reader-v2.cjs', s)
s = (RUN / 'run-file-browser-capture-v2.py').read_text(encoding='utf8')
for old, new in [('from publication_guard_v3 import *', 'from publication_guard_v4 import *'),
    ('registry-inspected-v1.json', 'registry-inspected-v2.json'),
    ('clean-candidate-site-binding-v1.json', 'clean-candidate-site-binding-v2.json'),
    ('browser-generated-inputs-before-v1.json', 'browser-generated-inputs-before-v2.json'),
    ('browser-generated-inputs-after-v1.json', 'browser-generated-inputs-after-v2.json'),
    ('online-ch2-prescient-cumulative-browser-v1', 'online-ch2-prescient-cumulative-browser-v2'),
    ('reader-file-browser-capture-command-v1', 'reader-file-browser-capture-command-v2'),
    ('capture-prescient-cumulative-reader-v1.cjs', 'capture-prescient-cumulative-reader-v2.cjs'),
    ('formula-render-v1-browser.json', 'formula-render-v2-browser.json')]:
    assert old in s, old
    s = s.replace(old, new)
write(RUN / 'run-file-browser-capture-v3.py', s)
for n in ['prepare-stage-v5.py', 'commit-and-build-site-v5.py', 'verify-registry-v3.py', 'run-file-browser-capture-v3.py']:
    compile((RUN/n).read_text(encoding='utf8'), n, 'exec')
print('Explicit repaired-site helpers prepared; no integration/staging/site executed.')
