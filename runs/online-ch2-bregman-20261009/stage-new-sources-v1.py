from common import *
fixed()
c=load(RUN/'complete-candidate-inspected-v1.json')
p=ROOT/'Tests/OnlineBregmanProximalCanary.lean'
assert sha(PUBLIC)==c['production_sha256'] and sha(p)==c['test_sha256']
paths=[PUBLIC.relative_to(ROOT).as_posix(),p.relative_to(ROOT).as_posix()]
capture('new-source-stage-v1','git','add',*paths)
tracked=set(subprocess.check_output(['git','ls-files','--',*paths],encoding='utf8').splitlines())
assert tracked==set(paths)
write(RUN/'pre-harness-input-tracking-v1.json',dict(actual_staged_paths=paths,reason='Required full-harness allowlisted source inventory uses git ls-files; earlier PR208 untracked-source failure is known and retained there. Stage only current two scoped new source files before current full harness, without changing tests/rules/semantics.',actual_source_byte_changes=False,prior_PR208_failure_not_current_failure=True,commit_performed=False))
fixed()
