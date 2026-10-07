from common_v1 import *
write(RUN/'deterministic-repair-v2.json',dict(prior_exit=load(RUN/'deterministic-attempt-v1-exit.json')['exit_code'],
    prior_log_sha256=sha(RUN/'deterministic-attempt-v1.log'),
    cause='Unqualified harmonic_succ rewrite selected H(T+1) on the left rather than H((T+1)+1) on the right.',
    correction='Specify harmonic_succ (T+1), retaining the frozen terminal and exact index.',
    source_or_frozen_target_changed=False))
text=(RUN/'leaves/deterministic-v1.lean').read_text(encoding='utf-8')
old='rw [Finset.sum_range_succ, ih, harmonic_succ]'
assert text.count(old)==1
write(RUN/'leaves/deterministic-v2.lean',text.replace(old,
    'rw [Finset.sum_range_succ, ih, harmonic_succ (T + 1)]'))
gate('deterministic-attempt-v2','lake','env','lean',RUN/'leaves/deterministic-v2.lean')
