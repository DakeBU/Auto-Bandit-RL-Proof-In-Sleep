from common import *
sys.path.insert(0, str(ROOT))
from tools.abrl_lifecycle import statement_hash, lean_declaration_header
fixed()
p = ROOT / 'Tests/OnlineBregmanExtendedCanary.lean'
d = load(CONTRACT / 'canary-stabilized-v1.json')
assert load(RUN / 'focused-canary-build-v2.json')['actual_exit'] == 1
write(RUN / 'canary-implementation-repair-v3.json', dict(
    failed_attempt_sha256=sha(RUN / 'canary-attempt-v2.lean'),
    failed_build_sha256=sha(RUN / 'focused-canary-build-v2.json'), actual_build_exit=1,
    repaired_minimum_errors_no_longer_reported=True,
    remaining_error='Uninstantiated RCLike rewrite cannot match scalar real inner product.',
    repair='Use the definitional scalar-real inner formula, as in accepted absolute-support proofs.',
    all_frozen_types_unchanged=True, production_unchanged=True, target_revision=False,
    retained_style_warnings='Polynomial derivative tactic sequence warnings retained; no suppression.',
    package_accepted=False, chapter_complete=False, whole_Goal_status='ACTIVE'))
event('canary-repair-native-v3', 'repair', dict(
    evidence_sha256=sha(RUN / 'canary-implementation-repair-v3.json'),
    target_revision=False, scope='One scalar real inner expression only',
    chapter_complete=False, goal_complete=False))
s = p.read_text(encoding='utf8')
assert s.count("      rw [RCLike.inner_apply', one_mul]") == 1
s = s.replace("      rw [RCLike.inner_apply', one_mul]", '      change z + (y - z) * (1 : ℝ) ≤ y')
p.write_bytes(s.encode('utf8'))
for t in d['targets']:
    assert statement_hash(lean_declaration_header(p, t['declaration'])) == t['statement_hash']
assert sha(PUBLIC) == d['production_sha256']
write(RUN / 'canary-attempt-v3.lean', p.read_bytes())
rc, out = capture('focused-canary-build-v3', 'lake', 'build', 'Tests.OnlineBregmanExtendedCanary', required=False)
print(out[-12000:], flush=True)
fixed()
