from common import *
import re
sys.path.insert(0, str(ROOT))
from tools.abrl_lifecycle import statement_hash, lean_declaration_header
fixed()
p = ROOT / 'Tests/OnlineBregmanExtendedCanary.lean'
d = load(CONTRACT / 'canary-stabilized-v1.json')
build = load(RUN / 'focused-canary-build-v3.json')
out = base64.b64decode(build['stdout_base64']).decode('utf8')
assert build['actual_exit'] == 0 and 'Build completed successfully' in out
assert sha(PUBLIC) == d['production_sha256']
for i in [1, 2]:
    capture('canary-failed-trial-v' + str(i), sys.executable, '-B', '-X', 'utf8', RUN / 'native-scoped.py',
        'trial-log', '--task', TASK, '--role', 'lower', '--kind', 'attempt', '--status', 'failed',
        '--attempt-id', 'EP003-infinity-canaries-v' + str(i), '--run-id', RUN.name,
        '--lean', p.relative_to(ROOT).as_posix(), '--obligations-before', '2', '--obligations-after', '2',
        '--verifier-evidence', RUN / ('focused-canary-build-v' + str(i) + '.json'),
        '--progress-class', 'diagnostic', '--notes',
        'Actual failed focused build retained with exact attempt snapshot; local proof repair, no target revision. Recorded after observation, not a prospective start.')
probe = 'import Tests.OnlineBregmanExtendedCanary\nopen Set BanditRL.OnlineConvex BanditRL.OnlineBregman\nnamespace ExtendedCanaryAudit\n'
for i, t in enumerate(d['targets']):
    assert statement_hash(lean_declaration_header(p, t['declaration'])) == t['statement_hash']
    assert hashlib.sha256(t['exact_proposed_header'].encode('utf8')).hexdigest() == t['header_raw_sha256']
    short = t['declaration'].rsplit('.', 1)[1]
    probe += t['exact_proposed_header'].replace('theorem ' + short, 'theorem public_value_' + str(i))
    probe += ' :=\n  ' + t['declaration'] + '\n'
    probe += '#check ' + t['declaration'] + '\n#print axioms ' + t['declaration'] + '\n#print axioms public_value_' + str(i) + '\n'
probe += 'end ExtendedCanaryAudit\n'
write(RUN / 'CanaryPublicValues.lean', probe)
rc, out = capture('canary-public-VALUE-kernel-v1', 'lake', 'env', 'lean', RUN / 'CanaryPublicValues.lean')
axioms = re.findall(r'depends on axioms:\s*\[([^]]*)\]', out)
assert len(axioms) == 4 and 'sorryAx' not in out
assert all(set(x.strip() for x in a.split(',') if x.strip()) <= {'propext', 'Classical.choice', 'Quot.sound'} for a in axioms)
for i, t in enumerate(d['targets']):
    fence = CONTRACT / ('canary-fence-' + str(i) + '-v1.json')
    capture('canary-fence-' + str(i) + '-v1', sys.executable, '-B', '-X', 'utf8', RUN / 'native-scoped.py',
        'statement-fence', '--declaration', t['declaration'], '--file', p.relative_to(ROOT).as_posix(), '--output', fence.relative_to(ROOT).as_posix())
    capture('canary-safe-' + str(i) + '-v1', sys.executable, '-B', '-X', 'utf8', RUN / 'native-scoped.py',
        'safe-verify', '--fence', fence.relative_to(ROOT).as_posix(), '--lean-file', p.relative_to(ROOT).as_posix())
    assert load(fence)['statement_hash'] == t['statement_hash']
old = (ROOT / 'runs/online-ch2-bregman-20261009/audit-numeric-tail-v1.lean').read_text(encoding='utf8')
old = old.replace('Tests.OnlineBregmanProximalCanary', 'Tests.OnlineBregmanExtendedCanary')
old = old.replace('BanditRL.OnlineBregmanCanary.nonquadratic_nonsmooth', d['targets'][0]['declaration'])
old = old.replace('BanditRL.OnlineBregmanCanary.boundary_outside_initial', d['targets'][1]['declaration'])
old = old.replace('BanditRL.OnlineBregman.proximal_one_step', 'BanditRL.OnlineBregman.proximal_one_step_extended')
write(RUN / 'audit-numeric-tail-v1.lean', old)
capture('numeric-tail-command-v1', 'lake', 'env', 'lean', '--run', RUN / 'audit-numeric-tail-v1.lean', RUN / 'numeric-tail-data-v1.json')
tails = load(RUN / 'numeric-tail-data-v1.json')
assert len(tails['rows']) == 2
assert all(t['public_helper_in_selected_tail'] and t['selected_tail_head'] == 'Eq.mp' for t in tails['rows'])
old = (RUN / 'export-production-dependencies-v1.lean').read_text(encoding='utf8')
old = old.replace('import BanditRLProof.OnlineBregmanExtended\n', 'import BanditRLProof.OnlineBregmanExtended\nimport Tests.OnlineBregmanExtendedCanary\n', 1)
old = old.replace('`BanditRL.OnlineBregman.proximal_one_step_extended]',
    '`BanditRL.OnlineBregman.proximal_one_step_extended,\n' + ',\n'.join('`' + t['declaration'] for t in d['targets']) + ']')
old = old.replace('#[{ module := `BanditRLProof.OnlineBregmanExtended }]',
    '#[{ module := `BanditRLProof.OnlineBregmanExtended }, { module := `Tests.OnlineBregmanExtendedCanary }]')
old = old.replace('dep.toString.startsWith "_private.BanditRLProof.OnlineBregmanExtended."',
    '(dep.toString.startsWith "_private.BanditRLProof.OnlineBregmanExtended." || dep.toString.startsWith "_private.Tests.OnlineBregmanExtendedCanary.")')
old = old.replace('Three frozen EReal finite-domain bridge proofs, no Test nodes yet.',
    'Three frozen EReal finite-domain bridge proofs and two full public infinity-domain canary conjunctions.')
write(RUN / 'export-selected-dependencies-v1.lean', old)
capture('selected-dependency-command-v1', 'lake', 'env', 'lean', '--run', RUN / 'export-selected-dependencies-v1.lean', RUN / 'selected-dependency-data-v1.json')
graph = load(RUN / 'selected-dependency-data-v1.json')
nodes = {n['name']: n for n in graph['nodes']}
pairs = load(RUN / 'production-dependency-inspected-v1.json')['required_actual_VALUE_pairs']
pairs += [[t['declaration'], 'BanditRL.OnlineBregman.' + n] for t in d['targets']
    for n in ['finitePart_convex_of_subdifferentiable', 'proximal_finitePart_minimizer_iff', 'proximal_one_step_extended']]
assert len(nodes) == 5 and len(pairs) == 12
for a, b in pairs:
    assert b in nodes[a]['value_dependencies'], (a, b)
write(RUN / 'complete-candidate-inspected-v1.json', dict(
    production_sha256=sha(PUBLIC), test_sha256=sha(p), actual_focused_canary_exit=build['actual_exit'],
    actual_cached_inclusive_jobs=list(map(int, re.findall(r'Build completed successfully \((\d+) jobs\)', base64.b64decode(build['stdout_base64']).decode('utf8')))),
    all_five_frozen_headers_unchanged=True, actual_canary_public_VALUEs=2, standard_only=True,
    actual_canary_axiom_outputs=axioms, selected_nodes=len(nodes), selected_graph_sha256=sha(RUN / 'selected-dependency-data-v1.json'),
    coalesced_direct_TYPE_VALUE_presences=len(graph['edges']), required_actual_VALUE_pairs=pairs,
    numeric_tail_sha256=sha(RUN / 'numeric-tail-data-v1.json'), both_selected_numeric_tails_retain_public_helper=True,
    warning_boundary='Four local style warning messages across two polynomial derivative lines, plus existing dependency warnings, retained without suppression.',
    failed_focused_attempts_retained=2, source_container_closed=False, package_accepted=False, chapter_complete=False, whole_Goal_status='ACTIVE'))
capture('canary-compiled-trial-v3', sys.executable, '-B', '-X', 'utf8', RUN / 'native-scoped.py',
    'trial-log', '--task', TASK, '--role', 'lower', '--kind', 'attempt', '--status', 'compiled',
    '--attempt-id', 'EP003-infinity-canaries-v3', '--run-id', RUN.name, '--lean', p.relative_to(ROOT).as_posix(),
    '--obligations-before', '2', '--obligations-after', '0', '--progress-class', 'compiled-leaf',
    '--verifier-evidence', RUN / 'complete-candidate-inspected-v1.json', '--notes',
    'Two full infinity canary types compiled; public VALUEs/standard axioms/fences and individual Eq.mp numeric-tail helper dependencies inspected. BODY/publication/combined acceptance pending.')
event('canary-candidate-native-v1', 'candidate', dict(
    evidence_sha256=sha(RUN / 'complete-candidate-inspected-v1.json'),
    scope='Three production proofs plus two full canaries; only compiled candidate, no full source closure',
    BODY_PENDING=True, combined_PENDING=True, source_container_closed=False, chapter_complete=False, goal_complete=False))
fixed()
print('Actual two public canary VALUEs/four standard axiom outputs/two individual Eq.mp helper tails/five-node graph inspected.')
