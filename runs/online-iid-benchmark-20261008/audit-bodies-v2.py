from common_reviewed_v2 import *
headers_fixed(8)
assert load(RUN / 'causal-canary-focused-build-v6-exit.json')['exit_code'] == 0
sys.path.insert(0, str(ROOT))
from tools.abrl_lifecycle import lean_declaration_header
TEST = 'Tests.OnlineGuessingIIDBenchmark.'
targets = load(CONTRACT / 'targets-v2.json')['rows']
actual = []
for row in targets:
    header = lean_declaration_header(PUBLIC, row['name'].rsplit('.',1)[1])
    assert header == ' '.join(row['header'].split())
    actual.append(dict(name=row['name'], path=PUBLIC.as_posix(), header=header,
        raw_header=row['header'], raw_header_sha256=row['header_sha256']))
text = CANARY.read_text(encoding='utf8')
for short in re.findall(r'(?m)^theorem (\w+)\b', text):
    start = text.index('theorem ' + short)
    raw = text[start:text.index(':=',start)].strip()
    header = lean_declaration_header(CANARY, short)
    assert header == ' '.join(raw.split())
    actual.append(dict(name=TEST+short, path=CANARY.as_posix(), header=header,
        raw_header=raw, raw_header_sha256=hashlib.sha256(raw.encode('utf8')).hexdigest()))
assert len(actual) == 36
write(RUN / 'actual-public-canary-headers-v2.json', actual)
write(RUN / 'public-candidate-v2.lean.raw', PUBLIC.read_bytes())
write(RUN / 'canary-candidate-v6.lean.raw', CANARY.read_bytes())
reuse = [PRE+x for x in ['expected_square_decomposition', 'independent_prediction_square',
    'history_policy_independent', 'meanPredict_independent', 'meanPredict_measurable', 'meanPredict_mem']]
definitions = [PRE+x for x in ['expectedFixedMinimum', 'expectedFixedRegret', 'empiricalMean', 'meanPredict']] + \
    [TEST+x for x in ['coinLaw','iidLaw','observation','lastPolicy','hindsightMinimum']]
instances = [TEST+x for x in ['coinLaw_probability','iidLaw_probability']]
names = [r['name'] for r in actual]+reuse+definitions+instances
assert len(names) == len(set(names)) == 53
write(RUN / 'leaves' / 'all-axioms-v2.lean', 'import Tests.OnlineGuessingIIDBenchmarkCanary\n' +
    '\n'.join('#check '+n+'\n#print axioms '+n for n in names))
gate('all-axioms-v2', 'lake','env','lean', RUN / 'leaves' / 'all-axioms-v2.lean')
log = (RUN / 'all-axioms-v2.log').read_text(encoding='utf8')
assert 'sorryAx' not in log
matched = re.findall(r"(?:^|\n)'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",log)
assert len(matched) == 53
axioms = {n:[a for a in re.sub(r'\s+','',s).split(',') if a] for n,s in matched}
assert set(axioms) == set(names)
assert all(set(a) <= {'propext','Classical.choice','Quot.sound'} for a in axioms.values())
write(RUN / 'axiom-bindings-v2.json',dict(names=names,axioms=axioms,count=53,
    public_sha256=sha(PUBLIC),canary_sha256=sha(CANARY)))
s = (RUN / 'draft-neutral-identities-v2.lean').read_text(encoding='utf8')
context = '\n'.join(line for line in (CONTRACT / 'public-context-v1.lean').read_text(encoding='utf8').splitlines()
    if not line.startswith('import ')).strip()
assert s.count(context) == 1
s = 'import Tests.OnlineGuessingIIDBenchmarkCanary\n' + s.replace(context,'',1)
s += '\nnamespace ActualTypeVerification\ndef propositionOf {P : Prop} (_ : P) : Prop := P\n'
for i,row in enumerate(targets,1):
    s += 'example : DraftExpected.Q%03d.{u} = propositionOf (@%s.{u}) := by rfl\n' % (i,row['name'])
s += 'open Tests.OnlineGuessingIIDBenchmark\n'
def closed_type(raw):
    short = raw.split()[1]
    tail = raw[len('theorem '+short):].strip()
    depth = 0
    for pos,char in enumerate(tail):
        if char in '([{': depth += 1
        elif char in ')]}': depth -= 1
        elif char == ':' and depth == 0:
            params,result = tail[:pos].strip(),tail[pos+1:].strip()
            return ('∀ '+params+',\n' if params else '') + result
    raise AssertionError(raw)
for i,row in enumerate(actual[8:],1):
    s += '\ndef C%03d : Prop := %s\nexample : C%03d = propositionOf (@%s) := by rfl\n' % (i,closed_type(row['raw_header']),i,row['name'])
for short in ['coinLaw','iidLaw','observation','lastPolicy','hindsightMinimum']:
    start = text.index('def '+short+' ')
    raw = text[start:text.index('\n\n',start)].replace('def '+short+' ', 'def '+short+'Fixture ',1)
    s += '\n'+raw+'\nexample : @'+short+'Fixture = @'+TEST+short+' := by rfl\n'
s += 'end ActualTypeVerification\n'
write(RUN / 'leaves' / 'all-exact-types-v2.lean',s)
gate('all-exact-types-v2','lake','env','lean', RUN / 'leaves' / 'all-exact-types-v2.lean')
template_path = Path('runs/online-regret-domains-20261007/leaves/export-actual-dependencies-v1.lean')
template = template_path.read_text(encoding='utf8')
start = template.index('def targets : Array Name := #[')
end = template.index(']\n',start)+1
template = template[:start] + 'def targets : Array Name := #[\n' + ',\n'.join('`'+n for n in names) + ']' + template[end:]
template = template.replace('Tests.OnlineLearningRegretDomainsCanary','Tests.OnlineGuessingIIDBenchmarkCanary')
scope = 'Existing2shared Regret proofs/2definitions plus8named validation proofs/8fixturedefinitions. Selected20compiled nodes with direct type/VALUE references; zero new production nodes; not the full shared registry or source inventory.'
assert scope in template
template = template.replace(scope,'Eight frozen expected-fixed/causal IID proofs, six actual reused proofs, four complete scoped definitions, twenty-eight named canary proofs, five complete real-coordinate IID/history/hindsight fixture definitions, two actual probability instances. Selected53 compiled nodes; direct TYPE/VALUE occurrences, not source coverage or full shared registry.')
write(RUN / 'leaves' / 'export-actual-dependencies-v2.lean',template)
gate('compiled-value-graph-v2','lake','env','lean','--run', RUN / 'leaves' / 'export-actual-dependencies-v2.lean', RUN / 'compiled-value-graph-v2.json')
graph = load(RUN / 'compiled-value-graph-v2.json')
assert len(graph['nodes']) == 53 and all(x['has_value'] for x in graph['nodes'])
assert sum(x['kind']=='definition' for x in graph['nodes']) == 9
required = [(PRE+a,PRE+b) for a,b in [
    ('expected_fixed_prefix_decomposition','expected_square_decomposition'),
    ('expected_fixed_prefix_minimum','expected_fixed_prefix_decomposition'),
    ('expectedFixedMinimum_eq_variance','expected_fixed_prefix_minimum'),
    ('iid_cumulative_prediction_decomposition','independent_prediction_square'),
    ('history_policy_expectedFixed_excess','expectedFixedMinimum_eq_variance'),
    ('history_policy_expectedFixed_excess','iid_cumulative_prediction_decomposition'),
    ('history_policy_expectedFixed_excess','history_policy_independent'),
    ('meanPredict_expectedFixed_excess','expectedFixedMinimum_eq_variance'),
    ('meanPredict_expectedFixed_excess','iid_cumulative_prediction_decomposition'),
    ('meanPredict_expectedFixed_excess','meanPredict_independent'),
    ('meanPredict_expectedFixed_excess','meanPredict_measurable'),
    ('meanPredict_expectedFixed_excess','meanPredict_mem'),
    ('constant_mean_expectedFixed_excess_zero','expected_fixed_prefix_minimum'),
    ('constant_mean_expectedFixed_excess_zero','expected_fixed_prefix_decomposition'),
    ('constant_mean_expectedFixed_excess_zero','expectedFixedMinimum_eq_variance'),
    ('history_policy_normalized_expectedFixed_excess','expectedFixedMinimum_eq_variance'),
    ('history_policy_normalized_expectedFixed_excess','normalized_excess')]]
required += [(PRE+'expectedFixedMinimum_eq_variance','IsLeast.csInf_eq'),
    (TEST+'observation_independent','ProbabilityTheory.iIndepFun_infinitePi'),
    (TEST+'meanPredict_two_round_excess',PRE+'meanPredict_expectedFixed_excess'),
    (TEST+'actual_history_independent',PRE+'history_policy_independent'),
    (TEST+'actual_history_nonnegative',PRE+'history_policy_expectedFixed_excess'),
    (TEST+'actual_history_normalization',PRE+'history_policy_normalized_expectedFixed_excess'),
    (TEST+'hindsight_minimum_two',PRE+'squaredLoss_minimum_eq'),
    (TEST+'min_and_expectation_do_not_commute',TEST+'hindsight_minimum_two'),
    (TEST+'min_and_expectation_do_not_commute',TEST+'two_round_fixed_minimum')]
edges={(e['source'],e['target']) for e in graph['edges'] if e['kind']=='value' or e['also_in_value']}
for pair in required: assert pair in edges,pair
write(RUN / 'required-value-pairs-v2.json',dict(required_pairs=required,scope='Actual compiled direct VALUE occurrences, not source coverage or teaching graph',exporter_template_sha256=sha(template_path)))
fences=[]
for row in actual:
    short=row['name'].rsplit('.',1)[1]
    label=('public-' if Path(row['path'])==PUBLIC else 'canary-')+short
    fence=RUN / 'full-header-fences-v2' / (label+'.json')
    native('full-fence-'+label+'-v2','statement-fence','--declaration',row['name'],'--file',row['path'],'--source-assumption',row['header'],'--output',fence)
    native('full-safe-'+label+'-v2','safe-verify','--fence',fence,'--lean-file',row['path'])
    assert load(fence)['statement']==row['header']
    fences.append(dict(name=row['name'],path=fence.as_posix(),sha256=sha(fence),statement_hash=load(fence)['statement_hash']))
write(RUN / 'full-fence-bindings-v2.json',fences)
native('actual-public-lookup-v2','list-lean-decls','--statement',PRE+'expectedFixed')
native('actual-endpoint-lookup-v2','list-lean-decls','--statement',PRE+'expectedFixed_excess')
native('actual-canary-lookup-v2','list-lean-decls','--include-tests','--statement',TEST)
write(RUN / 'body-bindings-v2.json',dict(public_sha256=sha(PUBLIC),canary_sha256=sha(CANARY),contract_version=2,
    frozen_targets=8,new_public_proofs=8,new_public_definitions=2,actual_reused_proofs=6,named_canary_proofs=28,test_definitions=5,
    probability_instances=2,named_kernel_checks=53,axioms=axioms,neutral_to_draft_Prop_identities=8,draft_to_actual_Prop_identities=8,
    arbitrary_public_universe='u',canary_Prop_identities=28,whole_definition_identities=9,required_value_pairs=required,
    full_native_header_guards=36,safe_verify_scope='Header/token scanning only; actual kernel builds recorded separately.',
    BODY_review='pending',combined_reader_FINAL_native_PR='pending',package_accepted=False,chapter_complete=False,goal_complete=False))
native('candidate-event-v2','lifecycle-event','--session',TASK,'--event','candidate','--payload-json',json.dumps(dict(
    run_id=RUN.name,contract_version=2,body_bindings=(RUN/'body-bindings-v2.json').as_posix(),package_accepted=False,chapter_complete=False,goal_complete=False)))
headers_fixed(8)
print('Actual eight bodies/28 canaries/53 kernel checks/26 VALUE pairs; BODY review pending.')
