from common import *
import re
sys.path.insert(0, str(ROOT))
from tools.abrl_lifecycle import statement_hash, lean_declaration_header
fixed()
TEST = ROOT / 'Tests/OnlinePrescientBregmanCanary.lean'
d = load(CONTRACT / 'canary-stabilized-v1.json')
r = load(RUN / 'run-canaries-attempt-result-v2.json')
assert r['compiled'] and r['test_sha256'] == sha(TEST) and sha(PUBLIC) == d['production_sha256']
receipt = load(RUN / 'complete-canary-public-VALUE-v1.json')
out = base64.b64decode(receipt['stdout_base64']).decode('utf8')
axioms = re.findall(r'depends on axioms:\s*\[([^]]*)\]', out)
assert len(axioms) == 8 and 'sorryAx' not in out
assert all(set(x.strip() for x in a.split(',') if x.strip()) <= {'propext', 'Classical.choice', 'Quot.sound'} for a in axioms)
capture('complete-canary-lookup-help-v2', sys.executable, '-B', '-X', 'utf8', 'tools/bandit.py', 'list-lean-decls', '--help')
_, out = capture('complete-canary-public-lookup-v2', sys.executable, '-B', '-X', 'utf8', 'tools/bandit.py', 'list-lean-decls', 'OnlinePrescientBregmanCanary', '--include-tests', '--statement')
for t in d['targets']:
    assert t['declaration'] in out
    assert statement_hash(lean_declaration_header(TEST, t['declaration'])) == t['statement_hash']
for i, t in enumerate(d['targets'][:2]):
    fence = (CONTRACT / ('canary-run-fence-' + str(i) + '-v1.json')).relative_to(ROOT).as_posix()
    capture('canary-run-fence-command-' + str(i) + '-v1', sys.executable, '-B', '-X', 'utf8', RUN / 'native-scoped.py', 'statement-fence', '--declaration', t['declaration'], '--file', TEST.relative_to(ROOT).as_posix(), '--output', fence)
    capture('canary-run-safe-verify-' + str(i) + '-v1', sys.executable, '-B', '-X', 'utf8', RUN / 'native-scoped.py', 'safe-verify', '--fence', fence, '--lean-file', TEST.relative_to(ROOT).as_posix())
    assert load(ROOT / fence)['statement_hash'] == t['statement_hash']
old = (ROOT / 'runs/online-ch2-extended-proximal-20261009/audit-numeric-tail-v2.lean').read_text(encoding='utf8')
old = old.replace('Tests.OnlineBregmanExtendedCanary', 'Tests.OnlinePrescientBregmanCanary')
old = old.replace('BanditRL.OnlineBregmanExtendedCanary.restricted_absolute_nonquadratic', d['targets'][0]['declaration'])
old = old.replace('BanditRL.OnlineBregmanExtendedCanary.restricted_linear_outside_center', d['targets'][1]['declaration'])
old = old.replace('BanditRL.OnlineBregman.proximal_one_step_extended', 'BanditRL.OnlinePrescientBregman.iterate_one_step')
write(RUN / 'audit-numeric-tail-v1.lean', old)
capture('selected-numeric-tail-command-v1', 'lake', 'env', 'lean', '--run', RUN / 'audit-numeric-tail-v1.lean', RUN / 'selected-numeric-tail-data-v1.json')
tails = load(RUN / 'selected-numeric-tail-data-v1.json')['rows']
assert len(tails) == 2
assert all(x['selected_tail_head'] == 'Eq.mp' and x['public_helper_in_selected_tail'] for x in tails)
prod = load(CONTRACT / 'stabilized-v1.json')
names = [x['declaration'] for x in prod['targets'] + prod['definitions'] + d['targets']]
old = (RUN / 'export-production-dependencies-v2.lean').read_text(encoding='utf8')
start = old.index('def targets : Array Name := #[')
end = old.index('\n\ndef moduleName', start)
text = old[:start] + 'def targets : Array Name := #[\n' + ',\n'.join('`' + n for n in names) + ']' + old[end:]
text = text.replace('BanditRLProof.OnlinePrescientBregman', 'Tests.OnlinePrescientBregmanCanary')
text = text.replace('Eight frozen partial-causal/locality/actual-transition proofs and two exact definitions, no Test nodes yet.', 'Eight frozen production proofs/two exact definitions and four complete concrete Test conjunctions plus referenced compiler-generated Test auxiliaries.')
write(RUN / 'export-selected-dependencies-v1.lean', text)
capture('selected-dependency-command-v1', 'lake', 'env', 'lean', '--run', RUN / 'export-selected-dependencies-v1.lean', RUN / 'selected-dependency-data-v1.json')
graph = load(RUN / 'selected-dependency-data-v1.json')
nodes = {n['name']: n for n in graph['nodes']}
assert set(names) <= set(nodes) and all(n['has_value'] for n in nodes.values())
ps = 'BanditRL.OnlinePrescientBregman.'
pairs = [[d['targets'][0]['declaration'], ps + x] for x in ['advance_some_spec', 'advance_none_iff', 'iterate_prefix', 'iterate_complete_of_step_attained', 'iterate_succ_some_spec', 'iterate_one_step']]
pairs += [[d['targets'][1]['declaration'], ps + x] for x in ['advance_some_spec', 'advance_none_iff', 'iterate_one_step']]
pairs += [[d['targets'][2]['declaration'], ps + x] for x in ['advance_none_iff', 'iterate_no_recovery']]
pairs += [[d['targets'][3]['declaration'], 'BanditRL.OnlineBregman.divergence_extension_eq']]
for a, b in pairs:
    assert b in nodes[a]['value_dependencies'], (a, b)
write(RUN / 'complete-candidate-inspected-v1.json', dict(compiled=True,
    production_sha256=sha(PUBLIC), test_sha256=sha(TEST), total_production_proofs=8,
    exact_definitions=2, complete_concrete_public_canaries=4, full_conjunction_public_VALUE=4,
    standard_only_axiom_outputs=axioms, both_selected_numeric_tails_retain_new_actual_transition=True,
    selected_numeric_heads=[x['selected_tail_head'] for x in tails],
    selected_nodes=len(nodes), requested_canonical_production_nodes=10, public_Test_nodes=4,
    additional_compiler_nodes=sorted(set(nodes) - set(names)),
    coalesced_direct_TYPE_VALUE_presences=len(graph['edges']), required_actual_canary_VALUE_pairs=pairs,
    graph_sha256=sha(RUN / 'selected-dependency-data-v1.json'),
    native_frozen_headers_unchanged=True, canary_BODY_PENDING=True,
    combined_gates_PENDING=True, source_container_closed=False, chapter_complete=False,
    whole_Goal_status='ACTIVE'))
capture('run-canaries-compiled-v1', sys.executable, '-B', '-X', 'utf8', RUN / 'native-scoped.py', 'trial-log', '--task', TASK, '--role', 'lower', '--kind', 'attempt', '--status', 'compiled', '--attempt-id', 'PC006-two-actual-selected-runs-v1', '--run-id', RUN.name, '--lean', TEST.relative_to(ROOT).as_posix(), '--statement-hash', d['targets'][0]['statement_hash'], '--obligations-before', '2', '--obligations-after', '0', '--verifier-evidence', RUN / 'complete-candidate-inspected-v1.json', '--notes', 'Both complete actual run conjunctions focused/public-VALUE/axioms/fences compiled; BOTH individually selected numeric Eq.mp tails retain new iterate_one_step, actual directVALUE graph inspected. Canary BODY and all combined/publication/site/FINAL/native/package/source/chapter gates pending; Goal ACTIVE.')
event('production-canaries-candidate-native-v1', 'candidate', dict(
    evidence_sha256=sha(RUN / 'complete-candidate-inspected-v1.json'),
    production_sha256=sha(PUBLIC), test_sha256=sha(TEST), bounded_proofs=8,
    definitions=2, canaries=4, canary_BODY_PENDING=True, combined_gates_PENDING=True,
    source_container_closed=False, chapter_complete=False, goal_complete=False))
fixed()
print('Actual bounded candidate compiled/API/axiom/frozen/numeric-tail/selected-graph evidence inspected; acceptance gates remain pending.')
