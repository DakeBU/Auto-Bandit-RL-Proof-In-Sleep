from common import *
import re
sys.path.insert(0, str(ROOT))
from tools.abrl_lifecycle import statement_hash, lean_declaration_header
fixed()
p = ROOT / 'Tests/OnlineBregmanExtendedCanary.lean'
d = load(CONTRACT / 'canary-stabilized-v1.json')
build = load(RUN / 'focused-canary-build-v4.json')
stdout = base64.b64decode(build['stdout_base64']).decode('utf8')
assert build['actual_exit'] == 0 and 'Built Tests.OnlineBregmanExtendedCanary' in stdout
assert sha(PUBLIC) == d['production_sha256']
for t in d['targets']:
    assert statement_hash(lean_declaration_header(p, t['declaration'])) == t['statement_hash']
rc, out = capture('canary-public-VALUE-kernel-v2', 'lake', 'env', 'lean', RUN / 'CanaryPublicValues.lean')
axioms = re.findall(r'depends on axioms:\s*\[([^]]*)\]', out)
assert len(axioms) == 4 and 'sorryAx' not in out
assert all(set(x.strip() for x in a.split(',') if x.strip()) <= {'propext', 'Classical.choice', 'Quot.sound'} for a in axioms)
for i, t in enumerate(d['targets']):
    fence = CONTRACT / ('canary-fence-' + str(i) + '-v1.json')
    assert load(fence)['statement_hash'] == t['statement_hash']
    capture('canary-safe-' + str(i) + '-v2', sys.executable, '-B', '-X', 'utf8', RUN / 'native-scoped.py',
        'safe-verify', '--fence', fence.relative_to(ROOT).as_posix(), '--lean-file', p.relative_to(ROOT).as_posix())
capture('numeric-tail-command-v3', 'lake', 'env', 'lean', '--run', RUN / 'audit-numeric-tail-v2.lean', RUN / 'numeric-tail-data-v3.json')
tails = load(RUN / 'numeric-tail-data-v3.json')
assert len(tails['rows']) == 2
assert all(t['public_helper_in_selected_tail'] and t['selected_tail_head'] == 'Eq.mp' for t in tails['rows'])
s = (RUN / 'export-production-dependencies-v1.lean').read_text(encoding='utf8')
s = s.replace('import BanditRLProof.OnlineBregmanExtended\n', 'import BanditRLProof.OnlineBregmanExtended\nimport Tests.OnlineBregmanExtendedCanary\n', 1)
s = s.replace('`BanditRL.OnlineBregman.proximal_one_step_extended]',
    '`BanditRL.OnlineBregman.proximal_one_step_extended,\n' + ',\n'.join('`' + t['declaration'] for t in d['targets']) + ']')
s = s.replace('#[{ module := `BanditRLProof.OnlineBregmanExtended }]',
    '#[{ module := `BanditRLProof.OnlineBregmanExtended }, { module := `Tests.OnlineBregmanExtendedCanary }]')
s = s.replace('dep.toString.startsWith "_private.BanditRLProof.OnlineBregmanExtended."',
    '(dep.toString.startsWith "_private.BanditRLProof.OnlineBregmanExtended." || dep.toString.startsWith "_private.Tests.OnlineBregmanExtendedCanary." || dep.toString.startsWith "BanditRL.OnlineBregmanExtendedCanary.")')
s = s.replace('Three frozen EReal finite-domain bridge proofs, no Test nodes yet.',
    'Three frozen EReal finite-domain bridge proofs, two full public infinity canaries and their referenced generated Test auxiliaries.')
write(RUN / 'export-selected-dependencies-v1.lean', s)
capture('selected-dependency-command-v1', 'lake', 'env', 'lean', '--run', RUN / 'export-selected-dependencies-v1.lean', RUN / 'selected-dependency-data-v1.json')
graph = load(RUN / 'selected-dependency-data-v1.json')
nodes = {n['name']: n for n in graph['nodes']}
pairs = load(RUN / 'production-dependency-inspected-v1.json')['required_actual_VALUE_pairs']
pairs += [[t['declaration'], 'BanditRL.OnlineBregman.' + n] for t in d['targets']
    for n in ['finitePart_convex_of_subdifferentiable', 'proximal_finitePart_minimizer_iff', 'proximal_one_step_extended']]
assert len(nodes) >= 5 and len(pairs) == 12
for a, b in pairs:
    assert b in nodes[a]['value_dependencies'], (a, b)
generated = [n for n in nodes if n.startswith('BanditRL.OnlineBregmanExtendedCanary.') and n not in {t['declaration'] for t in d['targets']}]
write(RUN / 'complete-candidate-inspected-v1.json', dict(
    production_sha256=sha(PUBLIC), test_sha256=sha(p), actual_focused_canary_exit=build['actual_exit'],
    actual_cached_inclusive_jobs=list(map(int, re.findall(r'Build completed successfully \((\d+) jobs\)', stdout))),
    all_five_frozen_headers_unchanged=True, actual_canary_public_VALUEs=2, actual_canary_axiom_outputs=axioms,
    standard_only=True, selected_nodes=len(nodes), generated_Test_auxiliaries=generated,
    selected_graph_sha256=sha(RUN / 'selected-dependency-data-v1.json'),
    coalesced_direct_TYPE_VALUE_presences=len(graph['edges']), required_actual_VALUE_pairs=pairs,
    numeric_tail_sha256=sha(RUN / 'numeric-tail-data-v3.json'), numeric_tail_selection_tool_sha256=sha(RUN / 'audit-numeric-tail-v2.lean'),
    both_selected_numeric_tails_retain_public_helper=True, both_selected_numeric_tail_heads='Eq.mp',
    warning_boundary='Four local style warnings across two polynomial derivative lines, plus old dependency warnings, retained without suppression.',
    failed_focused_attempts_retained=2, compiled_audit_repair_attempts_retained=1, failed_numeric_selectors_retained=2,
    extra_explicit_named_Test_helpers=[], source_container_closed=False, package_accepted=False,
    chapter_complete=False, whole_Goal_status='ACTIVE'))
capture('canary-compiled-trial-v4', sys.executable, '-B', '-X', 'utf8', RUN / 'native-scoped.py',
    'trial-log', '--task', TASK, '--role', 'lower', '--kind', 'attempt', '--status', 'compiled',
    '--attempt-id', 'EP003-infinity-canaries-v4', '--run-id', RUN.name, '--lean', p.relative_to(ROOT).as_posix(),
    '--obligations-before', '2', '--obligations-after', '0', '--progress-class', 'compiled-leaf',
    '--verifier-evidence', RUN / 'complete-candidate-inspected-v1.json', '--notes',
    'Two full infinity canaries compiled; public VALUEs/standard axioms/fences and individual Eq.mp numeric-tail helper dependencies inspected. Generated Test auxiliaries separately listed. BODY/publication/combined acceptance pending.')
event('canary-candidate-native-v1', 'candidate', dict(
    evidence_sha256=sha(RUN / 'complete-candidate-inspected-v1.json'),
    scope='Three production proofs, two full public infinity canaries and separately listed generated Test auxiliaries; compiled candidate only.',
    BODY_PENDING=True, combined_PENDING=True, source_container_closed=False, chapter_complete=False, goal_complete=False))
fixed()
print('Inspected graph:', len(nodes), 'nodes,', len(graph['edges']), 'coalesced direct presences;', len(pairs), 'required VALUE pairs.')
print('Both individually selected numeric tails have Eq.mp heads and retain proximal_one_step_extended.')
