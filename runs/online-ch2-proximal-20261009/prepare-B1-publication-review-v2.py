from common import *
fixed()
assert sha(ROOT/'Tests/OnlineProximalComparisonCanary.lean')==load(RUN/'canary-B1-repair-inspected-v2.json')['test_sha256']
paths=[PUBLIC,ROOT/'Tests/OnlineProximalComparisonCanary.lean']+[p for p in RUN.iterdir() if p.is_file() and p.name not in ['lifecycle-state.json','lifecycle-sessions.jsonl','own-artifact-journal.md','trials.jsonl']]+list(CONTRACT.glob('*'))
write(RUN/'canary-B1-publication-review-inputs-v2.json',dict(rows=rows(paths),allowed_new_outputs=['canary-BODY-publication-review-v2.md','canary-BODY-publication-review-v2.json'],no_existing_inputs_changed=True))
print('B1actual repaired numeric values and5future exact publication changes frozen for distinct review.')
