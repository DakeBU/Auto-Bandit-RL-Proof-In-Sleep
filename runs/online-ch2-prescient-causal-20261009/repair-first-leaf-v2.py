from common import *
import re
sys.path.insert(0, str(ROOT))
from tools.abrl_lifecycle import statement_hash, lean_declaration_header
fixed()
t = load(CONTRACT / 'stabilized-v1.json')['targets'][0]
assert load(RUN / 'first-leaf-attempt-result-v1.json')['actual_exit'] == 1
assert PUBLIC.read_bytes() == (RUN / 'first-leaf-attempt-v1.lean').read_bytes()
old = '  have he : Filter.EventuallyEq \u03c8 \u03c6 (nhds b) :=\n    (mem_interior_iff_mem_nhds.mp hb).mono fun z hz => hEq hz\n'
new = '  have hX : Filter.Eventually (fun z => z \u2208 X) (nhds b) :=\n    mem_interior_iff_mem_nhds.mp hb\n  have he : Filter.EventuallyEq (nhds b) \u03c8 \u03c6 :=\n    hX.mono fun z hz => hEq hz\n'
s = PUBLIC.read_text(encoding='utf8')
assert s.count(old) == 1
PUBLIC.write_bytes(s.replace(old, new).encode('utf8'))
assert statement_hash(lean_declaration_header(PUBLIC, t['declaration'])) == t['statement_hash']
write(RUN / 'first-leaf-repair-v2.md', 'Actual first focused build exit1: EventuallyEq takes filter first (actual Defs.lean297), and raw neighborhood membership needs explicit Filter.Eventually typing before mono. Only body repaired; original first attempt/log/result retained. Frozen normalized header/context unchanged. No mathematical assumption/target weakening, no new named helper or suppression. Existing parent warnings retained. New current hX is a local proof variable, not a public declaration.\n')
event('first-leaf-repair-native-v2', 'repair', dict(declaration=t['declaration'], statement_hash=t['statement_hash'], failure_evidence_sha256=sha(RUN / 'focused-first-leaf-v1.json'), body_only=True, header_context_unchanged=True, source_container_closed=False, chapter_complete=False, goal_complete=False))
write(RUN / 'first-leaf-attempt-v2.lean', PUBLIC.read_bytes())
rc, out = capture('focused-first-leaf-v2', 'lake', 'build', 'BanditRLProof.OnlinePrescientBregman', required=False)
print(out[-3000:], flush=True)
jobs = re.findall(r'Build completed successfully \((\d+) jobs\)', out)
write(RUN / 'first-leaf-attempt-result-v2.json', dict(actual_exit=rc, production_sha256=sha(PUBLIC), compiled=rc == 0 and bool(jobs), actual_cached_inclusive_build_jobs=jobs, selected_proofs=1, other_frozen_proofs_pending=7, definitions_not_yet_materialized=2, statement_hash_unchanged=True, prior_failure_retained=True, source_container_closed=False, chapter_complete=False, whole_Goal_status='ACTIVE'))
fixed()
