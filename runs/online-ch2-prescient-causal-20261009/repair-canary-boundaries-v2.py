from common import *
import re
sys.path.insert(0, str(ROOT))
from tools.abrl_lifecycle import statement_hash, lean_declaration_header
fixed()
TEST = ROOT / 'Tests/OnlinePrescientBregmanCanary.lean'
d = load(CONTRACT / 'canary-stabilized-v1.json')
assert sha(PUBLIC) == d['production_sha256']
assert load(RUN / 'canary-boundaries-attempt-result-v1.json')['actual_exit'] == 1
write(RUN / 'before-canary-boundaries-repair-v2.lean', TEST.read_bytes())
event('canary-boundaries-repair-native-v2', 'repair', dict(
    failed_command='focused-canary-boundaries-v1', actual_exit=1,
    diagnosis='Conjunction membership numeral did not elaborate from bare le_rfl; use explicit real interval normalization. Remove unnecessary tactic sequencing from local polynomial derivative proof.',
    statement_change=False, production_fixed=True, canary_BODY_accepted=False))
s = TEST.read_text(encoding='utf8')
old = '  refine \u27e8\u27e80, le_rfl\u27e9, isClosed_Iic, convex_Iic 0, le_rfl, hf, hs, hc,\n'
new = '  refine \u27e8\u27e80, by norm_num [V]\u27e9, isClosed_Iic, convex_Iic 0, by norm_num [V], hf, hs, hc,\n'
assert s.count(old) == 1
s = s.replace(old, new)
old = '    convert ((hasDerivAt_id z).pow 2).add (hasDerivAt_id z) using 1 <;>\n      dsimp [\u03c8, id] <;> ring\n'
new = '    convert ((hasDerivAt_id z).pow 2).add (hasDerivAt_id z) using 1\n    dsimp [\u03c8, id]\n    ring\n'
assert s.count(old) == 1
s = s.replace(old, new)
TEST.write_bytes(s.encode('utf8'))
for t in d['targets'][2:]:
    assert statement_hash(lean_declaration_header(TEST, t['declaration'])) == t['statement_hash']
write(RUN / 'canary-boundaries-attempt-v2.lean', TEST.read_bytes())
rc, out = capture('focused-canary-boundaries-v2', 'lake', 'build', 'Tests.OnlinePrescientBregmanCanary', required=False)
print(out[-3000:], flush=True)
jobs = re.findall(r'Build completed successfully \((\d+) jobs\)', out)
write(RUN / 'canary-boundaries-attempt-result-v2.json', dict(actual_exit=rc,
    compiled=rc == 0 and bool(jobs), actual_cached_inclusive_build_jobs=jobs,
    test_sha256=sha(TEST), production_sha256=sha(PUBLIC), frozen_headers_unchanged=True,
    selected_canaries=2, two_run_canaries_pending=True, canary_BODY_PENDING=True,
    combined_gates_PENDING=True, source_container_closed=False,
    chapter_complete=False, whole_Goal_status='ACTIVE'))
fixed()
