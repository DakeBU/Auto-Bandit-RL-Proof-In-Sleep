from common_reviewed_v2 import *
headers_fixed(8)
assert load(RUN / 'causal-canary-focused-build-v5-exit.json')['exit_code'] == 1
write(RUN / 'failed-causal-canary-v5.lean.raw', CANARY.read_bytes())
write(RUN / 'negative-canary-repair-v6.json', dict(obstruction='simp leaves negative inverse-two versus negative-one divided by two.',
    repair='Use norm_num for the same exact future-aware negative-regret fixture; no public change.',
    public_sha256=sha(PUBLIC), package_accepted=False, chapter_complete=False, goal_complete=False))
text = CANARY.read_text(encoding='utf8')
before = '  rw [two_round_fixed_minimum]\n  simp'
assert text.count(before) == 1
CANARY.write_bytes(text.replace(before, '  rw [two_round_fixed_minimum]\n  norm_num').encode('utf8'))
write(RUN / 'causal-canary-candidate-v6.lean.raw', CANARY.read_bytes())
gate('causal-canary-focused-build-v6', 'lake', 'build', 'Tests.OnlineGuessingIIDBenchmarkCanary')
headers_fixed(8)
