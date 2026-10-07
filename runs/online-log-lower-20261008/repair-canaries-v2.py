from common_v1 import *
write(RUN/'canary-repair-v2.json',dict(prior_exit=load(RUN/'public-canary-build-v1-exit.json')['exit_code'],
    prior_log_sha256=sha(RUN/'public-canary-build-v1.log'),
    cause='Rewrite could not infer concrete tail length from literal 2; ENNReal.ofReal rational conversion needs explicit division API.',
    correction='Instantiate actual causalPredict_cons_last at the concrete history; simplify ofReal_div explicitly.',
    mathematical_or_canary_headers_changed=False))
source=CANARY.read_text(encoding='utf-8')
old='  rw [show [true,true,false] = true :: [true,false] from rfl, causalPredict_cons_last]'
new='  rw [show (2 : ℕ) = [true,false].length from rfl, causalPredict_cons_last polyaNext true [true,false]]'
assert source.count(old)==1
source=source.replace(old,new)
source=source.replace('norm_num [seededPolicy,coinMeasure,BanditRLProof.Exp3.finiteActionMeasure]',
    'norm_num [seededPolicy,coinMeasure,BanditRLProof.Exp3.finiteActionMeasure,ENNReal.ofReal_div]')
CANARY.write_bytes(source.encode('utf-8'))
write(RUN/'snapshots/canaries-body-v2.lean.raw',CANARY.read_bytes())
gate('public-canary-build-v2','lake','build','Tests.OnlineGuessingLogLowerCanary')
