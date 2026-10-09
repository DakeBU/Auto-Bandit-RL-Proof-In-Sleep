from common import *
import re
sys.path.insert(0, str(ROOT))
from tools.abrl_lifecycle import statement_hash, lean_declaration_header
fixed()
d = load(CONTRACT / 'stabilized-v1.json')
assert load(RUN / 'first-leaf-inspected-v2.json')['production_sha256'] == sha(PUBLIC)
assert load(RUN / 'first-leaf-inspected-v2.json')['compiled']
before = PUBLIC.read_bytes()
write(RUN / 'before-advance-selection-v1.lean', before)
selected = d['targets'][1:3]
event('advance-selected-native-v1', 'proving', dict(selected_leaves=[dict(declaration=t['declaration'], statement_hash=t['statement_hash']) for t in selected], definitions=d['definitions'], first_locality_compiled=True, source_container_closed=False, chapter_complete=False, goal_complete=False))
capture('advance-running-trial-v1', sys.executable, '-B', '-X', 'utf8', RUN / 'native-scoped.py', 'trial-log', '--task', TASK, '--role', 'lower', '--kind', 'attempt', '--status', 'running', '--attempt-id', 'PC002-current-minimum-specs-v1', '--run-id', RUN.name, '--lean', PUBLIC.relative_to(ROOT).as_posix(), '--statement-hash', selected[0]['statement_hash'], '--obligations-before', '2', '--obligations-after', '2', '--notes', 'Only two exact partial definitions plus successful-minimum and missing-minimum specs selected. First locality compiled; causal recursion proofs and actual same-transition terminal still pending. No universal attainment/interiority/source/chapter closure.')
prefix = '\nnamespace BanditRL.OnlinePrescientBregman\nopen BanditRL.OnlineBregman\nvariable {E : Type*} [NormedAddCommGroup E] [NormedSpace \u211d E]\n\n'
addition = prefix + '\n\n'.join(x['exact_definition'] for x in d['definitions']) + '\n\n'
body_some = ''' := by
  classical
  unfold advance at h
  split_ifs at h with hatt
  \u00b7 have he := Option.some.inj h
    exact he \u25b8 Classical.choose_spec hatt
  \u00b7 cases h
'''
body_none = ''' := by
  classical
  unfold advance
  split_ifs with hatt <;> simp [hatt]
'''
addition += selected[0]['exact_proposed_header'] + body_some + '\n'
addition += selected[1]['exact_proposed_header'] + body_none + '\nend BanditRL.OnlinePrescientBregman\n'
PUBLIC.write_bytes(before + addition.encode('utf8'))
assert PUBLIC.read_bytes().startswith(before)
for t in d['targets'][:3]:
    assert statement_hash(lean_declaration_header(PUBLIC, t['declaration'])) == t['statement_hash']
for x in d['definitions']:
    assert x['exact_definition'] in PUBLIC.read_text(encoding='utf8')
    assert hashlib.sha256(x['exact_definition'].encode('utf8')).hexdigest() == x['exact_definition_UTF8_sha256']
write(RUN / 'advance-attempt-v1.lean', PUBLIC.read_bytes())
rc, out = capture('focused-advance-v1', 'lake', 'build', 'BanditRLProof.OnlinePrescientBregman', required=False)
print(out[-3500:], flush=True)
jobs = re.findall(r'Build completed successfully \((\d+) jobs\)', out)
write(RUN / 'advance-attempt-result-v1.json', dict(actual_exit=rc, production_sha256=sha(PUBLIC), compiled=rc == 0 and bool(jobs), actual_cached_inclusive_build_jobs=jobs, selected_proofs=2, total_materialized_proofs=3, materialized_definitions=2, other_proofs_pending=5, frozen_hashes_unchanged=True, first_leaf_exact_prefix_unchanged=True, source_container_closed=False, chapter_complete=False, whole_Goal_status='ACTIVE'))
fixed()
