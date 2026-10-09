from publication_guard_v3 import *
fixed()
assert (RUN/'candidate-stage-v2.json').exists() and load(RUN/'candidate-stage-v2.json')['actual_exit']==0
assert not (RUN/'baseline-v2.json').exists()
assert not (RUN/'candidate-full-diff-check-v2.json').exists()
write(RUN/'stage-runner-failure-repair-v4.json',dict(failed_command=[sys.executable,'-B','-X','utf8','runs/online-ch2-prescient-cumulative-20261009/prepare-stage-v3.py'],actual_tool_process_exit=1,failure='FileNotFoundError baseline-v2.json after successful scoped git add; overly broad helper filename replacement changed a pinned baseline reference. No full diff-check ran in this attempt.',preserved_failed_helper_sha256=sha(RUN/'prepare-stage-v3.py'),successful_preceding_git_add_receipt_sha256=sha(RUN/'candidate-stage-v2.json'),repair='New explicit stage-v4 helper uses exact baseline-v1, unchanged plan-v2/full-harness-v1/guard-v3, and fresh v3 receipt labels. No baseline regeneration, source/header/body/pin change.',whole_Goal_status='ACTIVE'))
s=(RUN/'commit-and-build-site-v2.py').read_text(encoding='utf8').replace('candidate-diff-audit-v1.json','candidate-diff-audit-v3.json').replace('candidate-stage-plan-v1.json','candidate-stage-plan-v3.json')
write(RUN/'commit-and-build-site-v4.py',s)
fixed()
print('Exact unexecuted staging failure retained; corrected stage-v4/commit-site-v4 prepared.')
