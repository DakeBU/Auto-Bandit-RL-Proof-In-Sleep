from common_body_v1 import *
fixed_integrated()
assert load(RUN/'candidate-frontier-refresh-v1-exit.json')['actual_exit']==2
write(RUN/'candidate-frontier-helper-repair-v2.json',dict(
    failed_receipt='candidate-frontier-refresh-v1-exit.json',failed_log='candidate-frontier-refresh-v1.log',
    failure='Unsupported CLI kind theorem. Actual --help permits lean/harness/retrieval/review.',
    repair='Use review for this package acceptance frontier, pointing to the actual BODY review; the separate exact Lean DAG and bodies are unchanged.',
    source_or_proof_or_global_frontier_changed=False))
native('candidate-frontier-refresh-v2','frontier-refresh','--root-objective',
    'Persistent Orabona Chapters1-16; three derived AE causal producers, whole program required',
    '--leaf',TASK,'--kind','review','--statement',
    'Three frozen AE causal public proofs compiled, actual original-process expected fixed excess and AE-only positive-variance canary; acceptance still awaits combined/reader/FINAL/native gates.',
    '--file',RUN/'public-body-review-v1.md','--source-status','source-reviewed','--leaf-status','gate-pending',
    '--dependency','review:source-body:accepted',
    '--dependency','lean:BanditRL.OnlineLearning.ae_predictable_private_seed_expectedFixed_excess:compiled',
    '--trials',RUN/'candidate-scoped-trials-v1.jsonl','--output',RUN/'candidate-frontier-v2.json','--shadow-status','pending')
native('candidate-frontier-shadow-v2','frontier-shadow','--trials',RUN/'candidate-scoped-trials-v1.jsonl',
    '--memory-digest',RUN/'memory-digest-candidate-v2.md','--frontier',RUN/'candidate-frontier-v2.json')
fixed_integrated()
print('Actual own candidate review frontier/shadow passed; global SGB unchanged.',flush=True)
