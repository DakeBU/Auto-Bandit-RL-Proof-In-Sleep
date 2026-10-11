from common import *
canary = ROOT/'Tests/OnlineAdaptivePotentialCanary.lean'
assert sha(canary) == sha(RUN/'potential-canary-body-attempt-v1.lean.txt')
failed = load(RUN/'potential-canary-focused-build-v1.json')
assert failed['actual_exit'] == 1
write(RUN/'potential-canary-proof-repair-v2.json', dict(
    failed_receipt_sha256=sha(RUN/'potential-canary-focused-build-v1.json'),
    exact_target='Second complete conjunction; selected T1 public-call premise terminal t<=1 for t<1',
    error='No goals to be solved inside one-line have h := by omega; outer terminal t<=1 remained unsolved',
    failure_class='Lean tactic sequencing, not false mathematical premise',
    missing_regularity=False, possible_counterexample=False,
    route='unchanged four-public-call route; split local have/subst/norm_num onto explicit lines',
    frozen_context_and_headers_unchanged=True, actual_exit=1))
capture('potential-canary-failed-trial-v1', sys.executable, '-B', '-X', 'utf8', RUN/'native-scoped.py',
    'trial-log', '--task', TASK, '--role', 'lower', '--kind', 'attempt', '--status', 'failed',
    '--attempt-id', 'potential-canary-body-v1', '--harness', 'hierarchical',
    '--progress-class', 'diagnostic', '--obligations-before', '2', '--obligations-after', '2',
    '--verifier-evidence', RUN/'potential-canary-focused-build-v1.json',
    '--error-signature', 'one-line-have-tactic-sequencing',
    '--notes', 'Actual Lean failure retained; two frozen full canary propositions unchanged; split have/subst lines only.')
old = b'    (by intro t ht; have h : t = 0 := by omega; subst t; norm_num [terminal])'
new = b'''    (by
      intro t ht
      have h : t = 0 := by omega
      subst t
      norm_num [terminal])'''
raw = canary.read_bytes()
assert raw.count(old) == 1
canary.write_bytes(raw.replace(old, new))
write(RUN/'potential-canary-body-attempt-v2.lean.txt', canary.read_bytes())
code, out = capture('potential-canary-focused-build-v2', 'lake', 'build',
    'Tests.OnlineAdaptivePotentialCanary', required=False)
print(out)
sys.exit(code)
