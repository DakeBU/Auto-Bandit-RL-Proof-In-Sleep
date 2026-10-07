from common_reviewed_v1 import *
reviewed_fixed();assert load(RUN/'public-canary-build-v1-exit.json')['exit_code']==1
assert 'No goals to be solved' in (RUN/'public-canary-build-v1.log').read_text(encoding='utf8')
s=CANARY.read_text(encoding='utf8');assert s.count('  ring\n')==1
CANARY.write_bytes(s.replace('  ring\n','',1).encode('utf8'))
write(RUN/'canary-proof-repair-v2.json',dict(failure='public-canary-build-v1',reason='simp completely closes linear_regret; following ring has no goal.',repair='Remove only redundant final tactic. Public module, nine target types, definitions, and all canary headers unchanged.',public_sha256=sha(PUBLIC),source_target_unchanged=True))
native('canary-repair-event-v2','lifecycle-event','--session',TASK,'--event','repair','--payload-json',json.dumps(dict(evidence=(RUN/'canary-proof-repair-v2.json').as_posix(),source_terminal_unchanged=True)))
native('canary-proving-event-v2','lifecycle-event','--session',TASK,'--event','proving','--payload-json',json.dumps(dict(reason='Same public theorem bodies; one redundant canary tactic removed',contract_version=1)))
gate('public-canary-build-v2','lake','build','Tests.OnlineNoRegretSemanticsCanary')
s=(RUN/'build-canary-v1.py').read_text(encoding='utf8');s=s[s.index("write(RUN/'public-canary-build-summary-v1.json'"):];exec(compile(s,'build-canary-v1-summary-after-v2-repair','exec'))
reviewed_fixed()
