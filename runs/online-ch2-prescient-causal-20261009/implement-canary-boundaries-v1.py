from common import *
import re
sys.path.insert(0, str(ROOT))
from tools.abrl_lifecycle import statement_hash, lean_declaration_header
fixed()
TEST = ROOT / 'Tests/OnlinePrescientBregmanCanary.lean'
d = load(CONTRACT / 'canary-stabilized-v1.json')
assert sha(PUBLIC) == d['production_sha256'] and not TEST.exists()
capture('canary-boundaries-running-v1', sys.executable, '-B', '-X', 'utf8', RUN / 'native-scoped.py', 'trial-log', '--task', TASK, '--role', 'lower', '--kind', 'attempt', '--status', 'running', '--attempt-id', 'PC005-concrete-boundary-audits-v1', '--run-id', RUN.name, '--lean', TEST.relative_to(ROOT).as_posix(), '--statement-hash', d['targets'][2]['statement_hash'], '--obligations-before', '2', '--obligations-after', '2', '--notes', 'Exact frozen exponential nonattainment/absorbing Option failure and halfline extension/boundary examples only. Two actual run canaries not yet materialized; all source cumulative/container/combined/publication gates remain open.')
text = (RUN / 'canary-neutral-types-v1.txt').read_text(encoding='utf8').split('theorem ', 1)[0]
for t, name in zip(d['targets'][2:], ['canary-missing-minimum-body-v1.txt', 'canary-extension-body-v1.txt']):
    text += t['exact_proposed_header'] + (RUN / name).read_text(encoding='utf8') + '\n'
text += 'end BanditRL.OnlinePrescientBregmanCanary\n'
write(TEST, text)
for t in d['targets'][2:]:
    assert statement_hash(lean_declaration_header(TEST, t['declaration'])) == t['statement_hash']
write(RUN / 'canary-boundaries-attempt-v1.lean', TEST.read_bytes())
rc, out = capture('focused-canary-boundaries-v1', 'lake', 'build', 'Tests.OnlinePrescientBregmanCanary', required=False)
print(out[-4500:], flush=True)
jobs = re.findall(r'Build completed successfully \((\d+) jobs\)', out)
write(RUN / 'canary-boundaries-attempt-result-v1.json', dict(actual_exit=rc,
    compiled=rc == 0 and bool(jobs), actual_cached_inclusive_build_jobs=jobs,
    test_sha256=sha(TEST), production_sha256=sha(PUBLIC), frozen_headers_unchanged=True,
    selected_canaries=2, two_run_canaries_pending=True, canary_BODY_PENDING=True,
    combined_gates_PENDING=True, source_container_closed=False,
    chapter_complete=False, whole_Goal_status='ACTIVE'))
fixed()
