from common_reviewed_v2 import *
headers_fixed(8)
assert load(RUN / 'canary-foundation-focused-build-v3-exit.json')['exit_code'] == 1
write(RUN / 'failed-canary-foundation-v3.lean.raw', CANARY.read_bytes())
write(RUN / 'canary-predictor-repair-v4.json', dict(
    obstruction='Actual predictor lambda was simplified in he, while the goal retained the original definition and real division notation.',
    audit='Rechecked same actual strict-past predictor, T2 support, centered variance and final quarter. No mathematical mismatch or public-target repair.',
    repair='Normalize both final sides with simpa using the already derived equality.',
    public_unchanged_sha256=sha(PUBLIC), package_accepted=False, chapter_complete=False, goal_complete=False))
text = CANARY.read_text(encoding='utf8')
before = '  exact he.trans (by simpa [observation] using hcenter)'
assert text.count(before) == 1
CANARY.write_bytes(text.replace(before,
    '  simpa [meanPredict, empiricalMean] using he.trans (by simpa [observation] using hcenter)').encode('utf8'))
write(RUN / 'canary-foundation-candidate-v4.lean.raw', CANARY.read_bytes())
gate('canary-foundation-focused-build-v4', 'lake', 'build', 'Tests.OnlineGuessingIIDBenchmarkCanary')
headers_fixed(8)
