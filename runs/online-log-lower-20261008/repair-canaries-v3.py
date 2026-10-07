from common_v1 import *
write(RUN/'canary-repair-v3.json',dict(prior_exit=load(RUN/'public-canary-build-v2-exit.json')['exit_code'],
    prior_log_sha256=sha(RUN/'public-canary-build-v2.log'),
    cause='Guessed generic ENNReal.ofReal_div does not exist in pinned Mathlib.',
    correction='Use actually retrieved ENNReal.ofReal_div_of_pos with the explicit positive denominator 2.',
    mathematical_or_canary_headers_changed=False))
source=CANARY.read_text(encoding='utf-8')
old='  norm_num [seededPolicy,coinMeasure,BanditRLProof.Exp3.finiteActionMeasure,ENNReal.ofReal_div]'
new='''  norm_num [seededPolicy,coinMeasure,BanditRLProof.Exp3.finiteActionMeasure]
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
  norm_num'''
assert source.count(old)==1
CANARY.write_bytes(source.replace(old,new).encode('utf-8'))
write(RUN/'snapshots/canaries-body-v3.lean.raw',CANARY.read_bytes())
gate('public-canary-build-v3','lake','build','Tests.OnlineGuessingLogLowerCanary')
