from common_v1 import *
write(RUN/'seeded-repair-v3.json',dict(prior_exit=load(RUN/'seeded-attempt-v2-exit.json')['exit_code'],
    prior_log_sha256=sha(RUN/'seeded-attempt-v2.log'),
    cause='The probability-space constant integral uses μ.real univ, not the ENNReal measure_univ form addressed by the first redundant simp.',
    correction='Use the actual probability API probReal_univ and one_smul at the final constant-integral comparison.',
    source_or_frozen_target_changed=False))
original=(RUN/'leaves/seeded-v2.lean').read_text(encoding='utf-8')
assert original.count('    exact hb\n')==1
write(RUN/'leaves/seeded-v3.lean',original.replace('    exact hb\n',
    '    simpa only [probReal_univ, one_smul] using hb\n'))
gate('seeded-attempt-v3','lake','env','lean',RUN/'leaves/seeded-v3.lean')
