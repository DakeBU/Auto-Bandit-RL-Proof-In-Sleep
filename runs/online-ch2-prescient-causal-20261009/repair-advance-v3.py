from common import *
import re
sys.path.insert(0, str(ROOT))
from tools.abrl_lifecycle import statement_hash, lean_declaration_header
fixed()
d = load(CONTRACT / 'stabilized-v1.json')
assert load(RUN / 'advance-attempt-result-v2.json')['actual_exit'] == 1
write(RUN / 'before-advance-repair-v3.lean', PUBLIC.read_bytes())
event('advance-body-repair-native-v3', 'repair', dict(
    failed_command='focused-advance-v2', actual_exit=1,
    diagnosis='Inline by-cases inside tuple consumed the following comma; use an explicit Iff constructor and nested tactic bullets.',
    allowed_change='Only advance_none_iff proof body; all headers, definitions and previous proofs fixed.',
    statement_changes=False, source_container_closed=False, chapter_complete=False))
s = PUBLIC.read_text(encoding='utf8')
old = '''  \u00b7 exact \u27e8fun h => by cases h, fun h => (h hatt).elim\u27e9
  \u00b7 exact \u27e8fun _ => hatt, fun _ => rfl\u27e9
'''
new = '''  \u00b7 constructor
    \u00b7 intro h
      cases h
    \u00b7 intro h
      exact (h hatt).elim
  \u00b7 exact \u27e8fun _ => hatt, fun _ => rfl\u27e9
'''
assert s.count(old) == 1
s = s.replace(old, new)
PUBLIC.write_bytes(s.encode('utf8'))
assert PUBLIC.read_bytes().startswith((RUN / 'before-advance-selection-v1.lean').read_bytes())
for t in d['targets'][:3]:
    assert statement_hash(lean_declaration_header(PUBLIC, t['declaration'])) == t['statement_hash']
for x in d['definitions']:
    assert x['exact_definition'] in s
write(RUN / 'advance-attempt-v3.lean', PUBLIC.read_bytes())
rc, out = capture('focused-advance-v3', 'lake', 'build', 'BanditRLProof.OnlinePrescientBregman', required=False)
print(out[-2500:], flush=True)
jobs = re.findall(r'Build completed successfully \((\d+) jobs\)', out)
write(RUN / 'advance-attempt-result-v3.json', dict(actual_exit=rc,
    production_sha256=sha(PUBLIC), compiled=rc == 0 and bool(jobs),
    actual_cached_inclusive_build_jobs=jobs, frozen_hashes_unchanged=True,
    definition_bodies_unchanged=True, first_leaf_exact_prefix_unchanged=True,
    selected_proofs=2, total_materialized_proofs=3, materialized_definitions=2,
    other_proofs_pending=5, source_container_closed=False, chapter_complete=False,
    whole_Goal_status='ACTIVE'))
fixed()
