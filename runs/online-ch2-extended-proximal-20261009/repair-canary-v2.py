from common import *
sys.path.insert(0, str(ROOT))
from tools.abrl_lifecycle import statement_hash, lean_declaration_header
fixed()
p = ROOT / 'Tests/OnlineBregmanExtendedCanary.lean'
d = load(CONTRACT / 'canary-stabilized-v1.json')
assert load(RUN / 'focused-canary-build-v1.json')['actual_exit'] == 1
for t in d['targets']:
    assert statement_hash(lean_declaration_header(p, t['declaration'])) == t['statement_hash']
write(RUN / 'canary-implementation-repair-v2.json', dict(
    failed_attempt_sha256=sha(RUN / 'canary-first-attempt-v1.lean'),
    failed_build_sha256=sha(RUN / 'focused-canary-build-v1.json'), actual_build_exit=1,
    failures=['Two IsMinOn set-membership presentations block point-specific if rewriting',
      'One unnecessary simplification in an inner-product identity makes no progress'],
    repair='Explicit pointwise inequality changes for minimum goals and evidence; direct RCLike inner rewrite.',
    all_frozen_types_unchanged=True, production_unchanged=True, target_revision=False,
    package_accepted=False, chapter_complete=False, whole_Goal_status='ACTIVE'))
event('canary-repair-native-v2', 'repair', dict(
    evidence_sha256=sha(RUN / 'canary-implementation-repair-v2.json'),
    target_revision=False, scope='Local canary proof repair only; no weakening of two frozen types',
    chapter_complete=False, goal_complete=False))
s = p.read_text(encoding='utf8')
s = s.replace('''    simpa only [f, if_pos hp, if_pos hz, EReal.toReal_coe, inv_one, one_mul] using
      hmin (mem_univ z)''', '''    change (f 0).toReal + (1 : ℝ)⁻¹ * divergence ψ 0 (1 / 2) ≤
      (f z).toReal + (1 : ℝ)⁻¹ * divergence ψ z (1 / 2)
    have hh : |(0 : ℝ)| + divergence ψ 0 (1 / 2) ≤ |z| + divergence ψ z (1 / 2) :=
      hmin (mem_univ z)
    simpa only [f, if_pos hp, if_pos hz, EReal.toReal_coe, inv_one, one_mul] using hh''')
s = s.replace("      rw [show inner ℝ (1 : ℝ) (y - z) = y - z from by simp [RCLike.inner_apply']]",
    "      rw [RCLike.inner_apply', one_mul]")
s = s.replace('''    have hh := hmin hz
    simpa only [f, if_pos hp, if_pos hz, EReal.toReal_coe, inv_one, one_mul,''', '''    change (f 0).toReal + (1 : ℝ)⁻¹ * divergence ψ 0 (-1) ≤
      (f z).toReal + (1 : ℝ)⁻¹ * divergence ψ z (-1)
    have hh : |(0 : ℝ)| + divergence ψ 0 (-1) ≤ |z| + divergence ψ z (-1) := hmin hz
    simpa only [f, if_pos hp, if_pos hz, EReal.toReal_coe, inv_one, one_mul,''')
assert s != p.read_text(encoding='utf8')
p.write_bytes(s.encode('utf8'))
for t in d['targets']:
    assert statement_hash(lean_declaration_header(p, t['declaration'])) == t['statement_hash']
write(RUN / 'canary-attempt-v2.lean', p.read_bytes())
rc, out = capture('focused-canary-build-v2', 'lake', 'build', 'Tests.OnlineBregmanExtendedCanary', required=False)
print(out[-13000:], flush=True)
fixed()
