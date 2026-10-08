from common_reviewed_v2 import *
headers_fixed(8)
assert load(RUN / 'canary-foundation-focused-build-v2-exit.json')['exit_code'] == 1
write(RUN / 'failed-canary-foundation-v2.lean.raw', CANARY.read_bytes())
write(RUN / 'canary-center-repair-v3.json', dict(
    obstruction='Simplification expressed one-half as inverse two; direct Eq.trans did not normalize division.',
    repair='Use simpa on the already proved centered integral certificate in the required Eq.trans type.',
    public_unchanged_sha256=sha(PUBLIC), package_accepted=False, chapter_complete=False, goal_complete=False))
text = CANARY.read_text(encoding='utf8')
assert text.count('  exact he.trans hcenter') == 1
CANARY.write_bytes(text.replace('  exact he.trans hcenter', '  exact he.trans (by simpa [observation] using hcenter)').encode('utf8'))
write(RUN / 'canary-foundation-candidate-v3.lean.raw', CANARY.read_bytes())
gate('canary-foundation-focused-build-v3', 'lake', 'build', 'Tests.OnlineGuessingIIDBenchmarkCanary')
headers_fixed(8)
