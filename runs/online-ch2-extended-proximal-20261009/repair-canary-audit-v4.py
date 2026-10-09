from common import *
sys.path.insert(0, str(ROOT))
from tools.abrl_lifecycle import statement_hash, lean_declaration_header
fixed()
p = ROOT / 'Tests/OnlineBregmanExtendedCanary.lean'
d = load(CONTRACT / 'canary-stabilized-v1.json')
assert load(RUN / 'focused-canary-build-v3.json')['actual_exit'] == 0
assert all(r['selected_tail_head'] == 'And.casesOn' for r in load(RUN / 'numeric-tail-data-v2.json')['rows'])
write(RUN / 'canary-audit-repair-v4.json', dict(
    actual_previous_focused_build_exit=0, actual_candidate_validator_v2_exit=1,
    raw_selector_output_sha256=sha(RUN / 'numeric-tail-data-v2.json'),
    compiled_Test_before_sha256=sha(p),
    cause='Destructuring old public conjunction creates And.casesOn around the entire new conjunction. The selector cannot isolate the final numeric branch without unfolding that old theorem.',
    repair='Replace destructuring by exact projections of the same already accepted public conjunction. Keep numeric proof Eq.mp unchanged; no theorem unfolding or target weakening.',
    all_frozen_types_unchanged=True, production_unchanged=True, target_revision=False,
    no_numeric_tail_claim_from_v1_or_v2=True, package_accepted=False, chapter_complete=False,
    whole_Goal_status='ACTIVE'))
event('canary-audit-repair-native-v4', 'repair', dict(
    evidence_sha256=sha(RUN / 'canary-audit-repair-v4.json'), target_revision=False,
    scope='Replace old conjunction destructuring by explicit identical projections so the numeric tail can be selected without theorem unfolding.',
    chapter_complete=False, goal_complete=False))
s = p.read_text(encoding='utf8')
a = '''  obtain ⟨hstrict, hmin, hnondiff, hv, hmoving, _, _⟩ :=
    BanditRL.OnlineBregmanCanary.nonquadratic_nonsmooth'''
b = '''  have hstrict := BanditRL.OnlineBregmanCanary.nonquadratic_nonsmooth.1
  have hmin := BanditRL.OnlineBregmanCanary.nonquadratic_nonsmooth.2.1
  have hnondiff := BanditRL.OnlineBregmanCanary.nonquadratic_nonsmooth.2.2.1
  have hv := BanditRL.OnlineBregmanCanary.nonquadratic_nonsmooth.2.2.2.1
  have hmoving := BanditRL.OnlineBregmanCanary.nonquadratic_nonsmooth.2.2.2.2.1'''
assert s.count(a) == 1
s = s.replace(a, b)
a = '''  obtain ⟨hstrict, _, hmin, hmoving, _, _⟩ :=
    BanditRL.OnlineBregmanCanary.boundary_outside_initial'''
b = '''  have hstrict := BanditRL.OnlineBregmanCanary.boundary_outside_initial.1
  have hmin := BanditRL.OnlineBregmanCanary.boundary_outside_initial.2.2.1
  have hmoving := BanditRL.OnlineBregmanCanary.boundary_outside_initial.2.2.2.1'''
assert s.count(a) == 1
s = s.replace(a, b)
p.write_bytes(s.encode('utf8'))
for t in d['targets']:
    assert statement_hash(lean_declaration_header(p, t['declaration'])) == t['statement_hash']
assert sha(PUBLIC) == d['production_sha256']
write(RUN / 'canary-attempt-v4.lean', p.read_bytes())
rc, out = capture('focused-canary-build-v4', 'lake', 'build', 'Tests.OnlineBregmanExtendedCanary', required=False)
print(out[-10000:], flush=True)
fixed()
