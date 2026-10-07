from common_v1 import *
fixed()
assert load(RUN/'loss-bridge-attempt-v2-exit.json')['exit_code']==0
assert PUBLIC.read_bytes()==(RUN/'snapshots/public-causal-v1.lean.raw').read_bytes()
PUBLIC.write_bytes((RUN/'leaves/loss-bridge-v2.lean').read_bytes())
write(RUN/'snapshots/public-loss-bridge-v1.lean.raw',PUBLIC.read_bytes())
gate('public-loss-bridge-build-v1','lake','build','BanditRLProof.OnlineGuessingLogLower')
write(RUN/'loss-bridge-progress-v1.json',dict(compiled_frozen_targets=13,
    produced='Same-path causal cumulative-loss successor, binary mean feasibility/minimum, exact count comparator loss and its expected value; conditional variance lower bound.',
    additional_auxiliary_definitions=['pathLearnerLoss','pathBestLoss'],
    auxiliary_definition_boundary='Specializations of actual shared same-path regret components, not independent per-book regret/probability libraries.',
    public_sha256=sha(PUBLIC), deterministic_and_randomized_terminals='unproved',
    BODY_review='pending',source_package_accepted=False,chapter_complete=False,goal_complete=False))
fixed()
