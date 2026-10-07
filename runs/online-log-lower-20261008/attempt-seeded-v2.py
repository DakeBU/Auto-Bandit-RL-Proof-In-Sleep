from common_v1 import *
write(RUN/'seeded-repair-v2.json',dict(prior_exit=load(RUN/'seeded-attempt-v1-exit.json')['exit_code'],
    prior_log_sha256=sha(RUN/'seeded-attempt-v1.log'),
    cause='integral_const rewrite already simplifies probability mass; a redundant simp-only step reports no progress.',
    correction='Remove only that redundant tactic; all measurable/integrable production, fixed witness and frozen targets remain exact.',
    source_or_frozen_target_changed=False))
original=(RUN/'leaves/seeded-v1.lean').read_text(encoding='utf-8')
old='    simp only [measure_univ, ENNReal.toReal_one, one_smul] at hb\n'
assert original.count(old)==1
write(RUN/'leaves/seeded-v2.lean',original.replace(old,''))
gate('seeded-attempt-v2','lake','env','lean',RUN/'leaves/seeded-v2.lean')
