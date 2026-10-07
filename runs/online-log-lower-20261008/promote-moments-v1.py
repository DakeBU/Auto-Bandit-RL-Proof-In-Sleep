from common_v1 import *
fixed()
assert load(RUN/'moments-attempt-v2-exit.json')['exit_code']==0
assert PUBLIC.read_bytes()==(RUN/'snapshots/public-law-v2.lean.raw').read_bytes()
PUBLIC.write_bytes((RUN/'leaves/moments-v2.lean').read_bytes())
write(RUN/'snapshots/public-moments-v1.lean.raw',PUBLIC.read_bytes())
gate('public-moments-build-v1','lake','build','BanditRLProof.OnlineGuessingLogLower')
write(RUN/'moments-progress-v1.json',dict(compiled_frozen_targets=10,
    actual_heads_moment='T/2', actual_second_moment='T*(2T+1)/6',
    actual_variance='(T+3)/(6*(T+2))',
    all_produced_from_recursive_law=True, public_sha256=sha(PUBLIC),
    source_lower_terminal_closed=False,BODY_review='pending',
    source_package_accepted=False,chapter_complete=False,goal_complete=False))
fixed()
