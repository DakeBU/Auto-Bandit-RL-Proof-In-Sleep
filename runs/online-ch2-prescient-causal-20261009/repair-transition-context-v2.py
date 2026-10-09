from common import *
import re
sys.path.insert(0, str(ROOT))
from tools.abrl_lifecycle import statement_hash, lean_declaration_header
fixed()
d = load(CONTRACT / 'stabilized-v1.json')
assert load(RUN / 'transition-attempt-result-v1.json')['actual_exit'] == 1
write(RUN / 'before-transition-context-repair-v2.lean', PUBLIC.read_bytes())
event('transition-context-repair-native-v2', 'repair', dict(
    failed_command='focused-transition-v1', actual_exit=1,
    diagnosis='A section inherited the earlier standalone NormedSpace, producing a second scalar-action instance beside InnerProductSpace.toNormedSpace. This was an implementation scope error against the frozen context, not a missing source assumption.',
    allowed_change='Close and reopen the namespace so the eighth theorem has exactly its frozen complete real inner-product context. Preserve the eight headers, both exact definitions and all proof bodies.',
    restores_frozen_context=True, semantic_target_change=False,
    source_container_closed=False, chapter_complete=False))
s = PUBLIC.read_text(encoding='utf8')
old = '\nsection InnerProduct\nvariable [InnerProductSpace \u211d E] [CompleteSpace E]\n\n'
new = '\nend BanditRL.OnlinePrescientBregman\n\nnamespace BanditRL.OnlinePrescientBregman\nopen BanditRL.OnlineBregman\nvariable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace \u211d E] [CompleteSpace E]\n\n'
assert s.count(old) == 1 and s.count('\nend InnerProduct\n') == 1
s = s.replace(old, new).replace('\nend InnerProduct\n', '\n')
PUBLIC.write_bytes(s.encode('utf8'))
for t in d['targets']:
    assert statement_hash(lean_declaration_header(PUBLIC, t['declaration'])) == t['statement_hash']
for x in d['definitions']:
    assert x['exact_definition'] in s
write(RUN / 'transition-attempt-v2.lean', PUBLIC.read_bytes())
rc, out = capture('focused-transition-v2', 'lake', 'build', 'BanditRLProof.OnlinePrescientBregman', required=False)
print(out[-2500:], flush=True)
jobs = re.findall(r'Build completed successfully \((\d+) jobs\)', out)
write(RUN / 'transition-attempt-result-v2.json', dict(actual_exit=rc,
    production_sha256=sha(PUBLIC), compiled=rc == 0 and bool(jobs),
    actual_cached_inclusive_build_jobs=jobs, selected_proofs=1,
    total_materialized_proofs=8, materialized_definitions=2,
    frozen_hashes_unchanged=True, frozen_context_restored=True,
    proof_bodies_unchanged=True, source_container_closed=False,
    chapter_complete=False, whole_Goal_status='ACTIVE'))
fixed()
