from common import *
import re
sys.path.insert(0, str(ROOT))
from tools.abrl_lifecycle import statement_hash, lean_declaration_header
fixed()
TEST = ROOT / 'Tests/OnlinePrescientBregmanCanary.lean'
d = load(CONTRACT / 'canary-stabilized-v1.json')
assert sha(PUBLIC) == d['production_sha256']
assert load(RUN / 'run-canaries-attempt-result-v1.json')['actual_exit'] == 1
write(RUN / 'before-run-canaries-repair-v2.lean', TEST.read_bytes())
write(RUN / 'prospective-projection-preparation-deferred-v1.md', '''The prospective helper prepare-run-body-projections-v1.py was invoked after the asynchronous audit/select runner had already materialized both run bodies. Its initial absence assertion failed (tool chunk43b67e, actual1), before any write or proof/native mutation. Therefore no prepared body replacement, snapshot or success receipt exists from that helper. The current ordinary v2 proof repair makes the component-projection change against the actual preserved failed Test bytes instead. Prior package numeric-tail audit already established why opaque conjunction cases obstruct isolating the terminal; this is preventive evidence preparation, not a newly passed numeric-tail audit.
''')
event('run-canaries-repair-native-v2', 'repair', dict(
    failed_command='focused-run-canaries-v1', actual_exit=1,
    diagnosis='Three IsMinOn comparisons remain set-membership presentations under simp; explicitly change each to its actual point-value inequality before EReal order rewriting.',
    additional_local_body_change='Use exact old theorem component projections instead of conjunction obtain, preserving all mathematical facts while permitting separate numeric-tail inspection. Remove unnecessary derivative tactic sequencing.',
    production_fixed=True, all4_statements_unchanged=True, no_numeric_audit_success_claim=True))
s = TEST.read_text(encoding='utf8')
boundary_prefix = s.split('theorem two_distinct_current_losses', 1)[0]
for old, base, indices in [
    ('  obtain \u27e8hf0, hs0, _, _, _, hstrict, hm0, hnondiff, hD10, hD01, _, _\u27e9 :=\n    BanditRL.OnlineBregmanExtendedCanary.restricted_absolute_nonquadratic\n',
     'BanditRL.OnlineBregmanExtendedCanary.restricted_absolute_nonquadratic',
     [('hf0', 1), ('hs0', 2), ('hstrict', 6), ('hm0', 7), ('hnondiff', 8), ('hD10', 9), ('hD01', 10)]),
    ('  obtain \u27e8hf, hs, htop, hout, _, _, hstrict, hm, hmove, _, _\u27e9 :=\n    BanditRL.OnlineBregmanExtendedCanary.restricted_linear_outside_center\n',
     'BanditRL.OnlineBregmanExtendedCanary.restricted_linear_outside_center',
     [('hf', 1), ('hs', 2), ('htop', 3), ('hout', 4), ('hstrict', 7), ('hm', 8), ('hmove', 9)])]:
    assert s.count(old) == 1
    s = s.replace(old, ''.join('  have ' + var + ' := ' + base + '.2' * (i - 1) + '.1\n' for var, i in indices))
replacements = [
    ('      have hh := hm hzero\n',
     '      have hh := hm hzero\n      change f0 p + ((divergence \u03c8 p (1 / 2) : \u211d) : EReal) \u2264\n        f0 0 + ((divergence \u03c8 0 (1 / 2) : \u211d) : EReal) at hh\n'),
    ('      have hh := hm hhalf\n',
     '      have hh := hm hhalf\n      change f1 p + ((divergence \u03c8 p 0 : \u211d) : EReal) \u2264\n        f1 (1 / 2) + ((divergence \u03c8 (1 / 2) 0 : \u211d) : EReal) at hh\n'),
    ('      have hh := hmin hz\n',
     '      have hh := hmin hz\n      change f p + ((divergence \u03c8 p (-1) : \u211d) : EReal) \u2264\n        f 0 + ((divergence \u03c8 0 (-1) : \u211d) : EReal) at hh\n'),
    ('    convert ((hasDerivAt_id z).pow 2).div_const 2 using 1 <;> dsimp [\u03c8, id] <;> ring\n',
     '    convert ((hasDerivAt_id z).pow 2).div_const 2 using 1\n    dsimp [\u03c8, id]\n    ring\n')]
for old, new in replacements:
    assert s.count(old) == 1, old
    s = s.replace(old, new)
assert s.startswith(boundary_prefix)
TEST.write_bytes(s.encode('utf8'))
for t in d['targets']:
    assert statement_hash(lean_declaration_header(TEST, t['declaration'])) == t['statement_hash']
write(RUN / 'run-canaries-attempt-v2.lean', TEST.read_bytes())
rc, out = capture('focused-run-canaries-v2', 'lake', 'build', 'Tests.OnlinePrescientBregmanCanary', required=False)
print(out[-5000:], flush=True)
jobs = re.findall(r'Build completed successfully \((\d+) jobs\)', out)
write(RUN / 'run-canaries-attempt-result-v2.json', dict(actual_exit=rc,
    compiled=rc == 0 and bool(jobs), actual_cached_inclusive_build_jobs=jobs,
    test_sha256=sha(TEST), production_sha256=sha(PUBLIC), frozen_headers_unchanged=True,
    all4_canaries_materialized=True, prior_boundary_bodies_unchanged=True,
    canary_BODY_PENDING=True, selected_numeric_audit_PENDING=True,
    combined_gates_PENDING=True, source_container_closed=False,
    chapter_complete=False, whole_Goal_status='ACTIVE'))
fixed()
