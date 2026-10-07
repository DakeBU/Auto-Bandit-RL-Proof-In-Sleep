from common_v1 import *
write(RUN/'causal-repair-v2.json',dict(prior_exit=load(RUN/'causal-attempt-v1-exit.json')['exit_code'],
    prior_log_sha256=sha(RUN/'causal-attempt-v1.log'),
    cause='Broad simp rewrites reverse getElem on one side before discharging optional lookup at the original reverse-list index.',
    correction='Use exact in-range getElem? equality before any reverse-index rewriting.',
    source_or_frozen_target_changed=False))
original=(RUN/'leaves/causal-v1.lean').read_text(encoding='utf-8')
old='      simp [binaryStream, hj]'
new='      simp only [binaryStream, List.getElem?_eq_getElem hj, Option.getD_some]'
assert original.count(old)==1
write(RUN/'leaves/causal-v2.lean',original.replace(old,new))
gate('causal-attempt-v2','lake','env','lean',RUN/'leaves/causal-v2.lean')
