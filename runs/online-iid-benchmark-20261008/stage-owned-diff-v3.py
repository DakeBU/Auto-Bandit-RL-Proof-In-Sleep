from common_integrated_v2 import *
fixed_integrated()
assert load(RUN/'combined-gates-v2.json')['status'].startswith('Actual combined')
for label in ['combined-root-v2','combined-Tests-v2','full-harness-v2']:
    assert load(RUN/(label+'-exit.json'))['exit_code']==0
source=(RUN/'stage-owned-diff-v2.py').read_text(encoding='utf8')
source=source.replace('scope-before-staging-v2','scope-before-staging-v3').replace('before-staging-v2','before-staging-v3')
source=source.replace('pre-source-full-diff-v2','pre-source-full-diff-v3')
exec(compile(source,'stage-owned-stable-completed-evidence-v3','exec'))
