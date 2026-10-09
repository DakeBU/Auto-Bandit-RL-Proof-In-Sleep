from common import *
import re
sys.path.insert(0, str(ROOT))
from tools.abrl_lifecycle import statement_hash, lean_declaration_header
fixed()
TEST = ROOT / 'Tests/OnlinePrescientBregmanCanary.lean'
d = load(CONTRACT / 'canary-stabilized-v1.json')
r = load(RUN / 'canary-boundaries-attempt-result-v2.json')
assert r['compiled'] and r['test_sha256'] == sha(TEST) and sha(PUBLIC) == d['production_sha256']
probe = 'import Tests.OnlinePrescientBregmanCanary\nopen Set BanditRL.OnlineConvex BanditRL.OnlineBregman BanditRL.OnlinePrescientBregman\nnamespace PrescientBoundaryAudit\n'
for t in d['targets'][2:]:
    name = t['declaration'].split('.')[-1]
    probe += t['exact_proposed_header'].replace('theorem ' + name, 'theorem public_VALUE_' + name)
    probe += ' :=\n  ' + t['declaration'] + '\n#print ' + t['declaration']
    probe += '\n#print axioms ' + t['declaration'] + '\n#print axioms public_VALUE_' + name + '\n'
probe += 'end PrescientBoundaryAudit\n'
write(RUN / 'CanaryBoundaryPublicAPIProbeV1.lean', probe)
_, out = capture('canary-boundaries-public-VALUE-v1', 'lake', 'env', 'lean', RUN / 'CanaryBoundaryPublicAPIProbeV1.lean')
axioms = re.findall(r'depends on axioms:\s*\[([^]]*)\]', out)
assert len(axioms) == 4 and 'sorryAx' not in out
assert all(set(x.strip() for x in a.split(',') if x.strip()) <= {'propext', 'Classical.choice', 'Quot.sound'} for a in axioms)
for i, t in enumerate(d['targets'][2:]):
    fence = (CONTRACT / ('canary-boundary-fence-' + str(i) + '-v1.json')).relative_to(ROOT).as_posix()
    capture('canary-boundary-fence-command-' + str(i) + '-v1', sys.executable, '-B', '-X', 'utf8', RUN / 'native-scoped.py', 'statement-fence', '--declaration', t['declaration'], '--file', TEST.relative_to(ROOT).as_posix(), '--output', fence)
    capture('canary-boundary-safe-verify-' + str(i) + '-v1', sys.executable, '-B', '-X', 'utf8', RUN / 'native-scoped.py', 'safe-verify', '--fence', fence, '--lean-file', TEST.relative_to(ROOT).as_posix())
    assert load(ROOT / fence)['statement_hash'] == t['statement_hash']
write(RUN / 'canary-boundaries-inspected-v1.json', dict(compiled=True,
    test_sha256=sha(TEST), production_sha256=sha(PUBLIC), full_conjunction_public_VALUE=2,
    standard_only_axiom_outputs=axioms, frozen_hashes_unchanged=True,
    canary_BODY_PENDING=True, two_run_canaries_pending=True,
    source_container_closed=False, chapter_complete=False, whole_Goal_status='ACTIVE'))
capture('canary-boundaries-compiled-v1', sys.executable, '-B', '-X', 'utf8', RUN / 'native-scoped.py', 'trial-log', '--task', TASK, '--role', 'lower', '--kind', 'attempt', '--status', 'compiled', '--attempt-id', 'PC005-concrete-boundary-audits-v1', '--run-id', RUN.name, '--lean', TEST.relative_to(ROOT).as_posix(), '--statement-hash', d['targets'][2]['statement_hash'], '--obligations-before', '2', '--obligations-after', '0', '--verifier-evidence', RUN / 'canary-boundaries-inspected-v1.json', '--notes', 'Two complete concrete boundary/nonattainment conjunctions focused/public-VALUE/standard axioms/fences compiled; no canaryBODY/combined/package/source/chapter acceptance. Two actual run canaries selected next.')
write(RUN / 'before-run-canaries-selection-v1.lean', TEST.read_bytes())
event('run-canaries-selected-native-v1', 'proving', dict(selected=[dict(declaration=t['declaration'], statement_hash=t['statement_hash']) for t in d['targets'][:2]], production_fixed=True, scope='Only two remaining frozen run canary bodies, local have/let helpers; prior boundary canary bodies fixed.', source_container_closed=False, chapter_complete=False))
capture('run-canaries-running-v1', sys.executable, '-B', '-X', 'utf8', RUN / 'native-scoped.py', 'trial-log', '--task', TASK, '--role', 'lower', '--kind', 'attempt', '--status', 'running', '--attempt-id', 'PC006-two-actual-selected-runs-v1', '--run-id', RUN.name, '--lean', TEST.relative_to(ROOT).as_posix(), '--statement-hash', d['targets'][0]['statement_hash'], '--obligations-before', '2', '--obligations-after', '2', '--notes', 'Actual selected two distinct-loss transitions and boundary outside-center run; minima/uniqueness/conditional completion and new actual one-step APIs used, numeric tails by equality transport. No source cumulative container closure.')
s = TEST.read_text(encoding='utf8')
end = 'end BanditRL.OnlinePrescientBregmanCanary\n'
assert s.endswith(end)
prefix = s[:-len(end)]
s = prefix
for t, body in zip(d['targets'][:2], ['canary-two-round-body-v1.txt', 'canary-outside-run-body-v1.txt']):
    s += t['exact_proposed_header'] + (RUN / body).read_text(encoding='utf8') + '\n'
s += end
TEST.write_bytes(s.encode('utf8'))
assert s.startswith(prefix)
for t in d['targets']:
    assert statement_hash(lean_declaration_header(TEST, t['declaration'])) == t['statement_hash']
write(RUN / 'run-canaries-attempt-v1.lean', TEST.read_bytes())
rc, out = capture('focused-run-canaries-v1', 'lake', 'build', 'Tests.OnlinePrescientBregmanCanary', required=False)
print(out[-6500:], flush=True)
jobs = re.findall(r'Build completed successfully \((\d+) jobs\)', out)
write(RUN / 'run-canaries-attempt-result-v1.json', dict(actual_exit=rc,
    compiled=rc == 0 and bool(jobs), actual_cached_inclusive_build_jobs=jobs,
    test_sha256=sha(TEST), production_sha256=sha(PUBLIC), frozen_headers_unchanged=True,
    all4_canaries_materialized=True, canary_BODY_PENDING=True, combined_gates_PENDING=True,
    source_container_closed=False, chapter_complete=False, whole_Goal_status='ACTIVE'))
fixed()
