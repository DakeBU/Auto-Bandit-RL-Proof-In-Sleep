from common_reviewed_v1 import *
import re

headers_fixed(6)
assert load(RUN / 'public-canary-focused-build-v1-exit.json')['exit_code'] == 0
sys.path.insert(0, str(ROOT))
from tools.abrl_lifecycle import lean_declaration_header
PRE = 'BanditRL.OnlineLearning.'
TEST = 'Tests.OnlineSquareMinimum.'
targets = load(CONTRACT / 'targets-v1.json')['rows']
actual = []
for row in targets:
    header = lean_declaration_header(PUBLIC, row['name'].rsplit('.', 1)[1])
    assert header == ' '.join(row['header'].split())
    actual.append(dict(name=row['name'], path=PUBLIC.as_posix(), header=header,
        raw_header=row['header'], raw_header_sha256=row['header_sha256']))
text = CANARY.read_text(encoding='utf8')
for short in re.findall(r'(?m)^theorem (\w+)\b', text):
    start = text.index('theorem ' + short)
    raw = text[start:text.index(':=', start)].strip()
    header = lean_declaration_header(CANARY, short)
    assert header == ' '.join(raw.split())
    actual.append(dict(name=TEST + short, path=CANARY.as_posix(), header=header,
        raw_header=raw, raw_header_sha256=hashlib.sha256(raw.encode('utf8')).hexdigest()))
assert len(actual) == 26
write(RUN / 'actual-public-canary-headers-v1.json', actual)
write(RUN / 'public-candidate-v1.lean.raw', PUBLIC.read_bytes())
write(RUN / 'canary-candidate-v1.lean.raw', CANARY.read_bytes())
reuse = [PRE + x for x in ['empiricalMean_mem', 'empiricalMean_minimizes', 'empiricalMean_unique',
    'theorem_1_3', 'meanPredict_regret_refined', 'meanPredict_prefix']]
definitions = ([PRE + x for x in ['squaredBestRegret', 'empiricalMean', 'meanPredict', 'comparatorRegret']] +
    [TEST + x for x in ['alternating', 'quarters']])
names = [x['name'] for x in actual] + reuse + definitions
assert len(names) == len(set(names)) == 38
write(RUN / 'leaves' / 'all-axioms-v1.lean', 'import Tests.OnlineSquareMinimumCanary\n' +
    '\n'.join('#check ' + n + '\n#print axioms ' + n for n in names))
gate('all-axioms-v1', 'lake', 'env', 'lean', RUN / 'leaves' / 'all-axioms-v1.lean')
log = (RUN / 'all-axioms-v1.log').read_text(encoding='utf8')
assert 'sorryAx' not in log
matched = re.findall(r"(?:^|\n)'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", log)
assert len(matched) == 38
axioms = {n: [a for a in re.sub(r'\s+', '', s).split(',') if a] for n, s in matched}
assert set(axioms) == set(names)
assert all(set(a) <= {'propext', 'Classical.choice', 'Quot.sound'} for a in axioms.values())
write(RUN / 'axiom-bindings-v1.json', dict(names=names, axioms=axioms, count=38,
    public_sha256=sha(PUBLIC), canary_sha256=sha(CANARY)))

# Import the actual public module, remove only the draft's inlined proposed definition/context.
s = (RUN / 'draft-neutral-identities-v1.lean').read_text(encoding='utf8')
context = '\n'.join(line for line in (CONTRACT / 'public-context-v1.lean').read_text(encoding='utf8').splitlines()
    if not line.startswith('import ')).strip()
assert s.count(context) == 1
s = 'import Tests.OnlineSquareMinimumCanary\n' + s.replace(context, '', 1)
s += '\nnamespace ActualTypeVerification\ndef propositionOf {P : Prop} (_ : P) : Prop := P\n'
for i, row in enumerate(targets, 1):
    s += 'example : DraftMinimum.Q%03d = propositionOf (@%s) := by rfl\n' % (i, row['name'])
s += 'open Tests.OnlineSquareMinimum\n'
def closed_type(raw):
    short = raw.split()[1]
    tail = raw[len('theorem ' + short):].strip()
    depth = 0
    for pos, char in enumerate(tail):
        if char in '([{': depth += 1
        elif char in ')]}': depth -= 1
        elif char == ':' and depth == 0:
            params, result = tail[:pos].strip(), tail[pos + 1:].strip()
            return ('∀ ' + params + ',\n' if params else '') + result
    raise AssertionError('No top-level terminal separator: ' + raw)
for i, row in enumerate(actual[6:], 1):
    s += '\ndef C%03d : Prop := %s\nexample : C%03d = propositionOf (@%s) := by rfl\n' % (
        i, closed_type(row['raw_header']), i, row['name'])
s += '''
noncomputable def alternatingFixture (t : ℕ) : ℝ := if t % 2 = 0 then 0 else 1
noncomputable def quartersFixture (t : ℕ) : ℝ := if t % 2 = 0 then 1 / 4 else 3 / 4
example : alternatingFixture = Tests.OnlineSquareMinimum.alternating := by rfl
example : quartersFixture = Tests.OnlineSquareMinimum.quarters := by rfl
end ActualTypeVerification
'''
write(RUN / 'leaves' / 'all-exact-types-v1.lean', s)
gate('all-exact-types-v1', 'lake', 'env', 'lean', RUN / 'leaves' / 'all-exact-types-v1.lean')

template_path = Path('runs/online-regret-domains-20261007/leaves/export-actual-dependencies-v1.lean')
template = template_path.read_text(encoding='utf8')
start = template.index('def targets : Array Name := #[')
end = template.index(']\n', start) + 1
template = template[:start] + 'def targets : Array Name := #[\n' + ',\n'.join('`' + n for n in names) + ']' + template[end:]
template = template.replace('Tests.OnlineLearningRegretDomainsCanary', 'Tests.OnlineSquareMinimumCanary')
old_scope = 'Existing2shared Regret proofs/2definitions plus8named validation proofs/8fixturedefinitions. Selected20compiled nodes with direct type/VALUE references; zero new production nodes; not the full shared registry or source inventory.'
assert old_scope in template
template = template.replace(old_scope, 'Six new square-minimum proofs, six actually reused mean/FTL/causality proofs, four complete scoped definitions, twenty named canaries and two time-only fixtures. Selected38 compiled nodes; direct TYPE and VALUE constant occurrences, not a source inventory or full shared registry.')
write(RUN / 'leaves' / 'export-actual-dependencies-v1.lean', template)
gate('compiled-value-graph-v1', 'lake', 'env', 'lean', '--run', RUN / 'leaves' / 'export-actual-dependencies-v1.lean',
    RUN / 'compiled-value-graph-v1.json')
graph = load(RUN / 'compiled-value-graph-v1.json')
assert len(graph['nodes']) == 38 and all(x['has_value'] for x in graph['nodes'])
assert sum(x['kind'] == 'theorem' for x in graph['nodes']) == 32
assert sum(x['kind'] == 'definition' for x in graph['nodes']) == 6
required = [
    (PRE + 'guessing_prefix_minimum', PRE + 'empiricalMean_mem'),
    (PRE + 'guessing_prefix_minimum', PRE + 'empiricalMean_minimizes'),
    (PRE + 'squaredLoss_minimum_eq', PRE + 'guessing_prefix_minimum'),
    (PRE + 'squaredLoss_minimum_eq', 'IsLeast.csInf_eq'),
    (PRE + 'squaredBestRegret_eq_comparatorRegret', PRE + 'squaredLoss_minimum_eq'),
    (PRE + 'comparatorRegret_le_squaredBestRegret', PRE + 'guessing_prefix_minimum'),
    (PRE + 'comparatorRegret_le_squaredBestRegret', PRE + 'squaredBestRegret_eq_comparatorRegret'),
    (PRE + 'meanPredict_bestRegret_bound', PRE + 'squaredBestRegret_eq_comparatorRegret'),
    (PRE + 'meanPredict_bestRegret_bound', PRE + 'theorem_1_3'),
    (PRE + 'meanPredict_bestRegret_refined', PRE + 'squaredBestRegret_eq_comparatorRegret'),
    (PRE + 'meanPredict_bestRegret_refined', PRE + 'meanPredict_regret_refined'),
    (TEST + 'alternating_unique', PRE + 'empiricalMean_unique'),
    (TEST + 'actual_causality', PRE + 'meanPredict_prefix'),
    (TEST + 'signed_alternating', PRE + 'squaredBestRegret_eq_comparatorRegret'),
    (TEST + 'actual_bound', PRE + 'meanPredict_bestRegret_bound'),
    (TEST + 'actual_refined', PRE + 'meanPredict_bestRegret_refined')]
edges = {(e['source'], e['target']) for e in graph['edges'] if e['kind'] == 'value' or e['also_in_value']}
for pair in required: assert pair in edges, pair
write(RUN / 'required-value-pairs-v1.json', dict(required_pairs=required,
    meaning='Actual compiled proof/definition direct constant occurrences, not teaching or source-coverage graph',
    exporter_template=template_path.as_posix(), exporter_template_sha256=sha(template_path)))
fences = []
for row in actual:
    short = row['name'].rsplit('.', 1)[1]
    label = ('public-' if Path(row['path']) == PUBLIC else 'canary-') + short
    fence = RUN / 'full-header-fences-v1' / (label + '.json')
    native('full-fence-' + label + '-v1', 'statement-fence', '--declaration', row['name'], '--file', row['path'],
        '--source-assumption', row['header'], '--output', fence)
    native('full-safe-' + label + '-v1', 'safe-verify', '--fence', fence, '--lean-file', row['path'])
    assert load(fence)['statement'] == row['header']
    fences.append(dict(name=row['name'], path=fence.as_posix(), sha256=sha(fence), statement_hash=load(fence)['statement_hash']))
write(RUN / 'full-fence-bindings-v1.json', fences)
native('actual-public-lookup-v1', 'list-lean-decls', '--statement', PRE + 'squared')
native('actual-endpoint-lookup-v1', 'list-lean-decls', '--statement', PRE + 'bestRegret')
native('actual-canary-lookup-v1', 'list-lean-decls', '--include-tests', '--statement', TEST)
write(RUN / 'body-bindings-v1.json', dict(public_sha256=sha(PUBLIC), canary_sha256=sha(CANARY),
    frozen_targets=6, new_public_proofs=6, new_public_definitions=1, actual_reused_proofs=6,
    named_canary_proofs=20, test_definitions=2, named_kernel_checks=38,
    neutral_to_draft_Prop_identities=6, draft_to_actual_public_Prop_identities=6,
    actual_canary_Prop_identities=20, whole_scoped_and_fixture_definition_identities=6,
    axioms=axioms, selected_compiled_nodes=38, required_value_pairs=required, full_native_proof_fences=26,
    safe_verify_scope='Header/substring/forbidden-token scan only; actual Lean compilation is separate.',
    BODY_review='pending', combined_reader_FINAL_native_PR='pending', package_accepted=False, chapter_complete=False, goal_complete=False))
native('candidate-event-v1', 'lifecycle-event', '--session', TASK, '--event', 'candidate', '--payload-json',
    json.dumps(dict(run_id=RUN.name, body_bindings=(RUN / 'body-bindings-v1.json').as_posix(),
        contract_version=1, package_accepted=False, chapter_complete=False, goal_complete=False)))
headers_fixed(6)
print('38 actual kernel nodes, exact public/canary/context identities and 16 VALUE pairs; BODY source review pending.')
