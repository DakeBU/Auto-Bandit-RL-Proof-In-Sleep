from common_reviewed_v2 import *
import re

headers_fixed(7)
assert load(RUN/'canary-XOR-focused-build-v3-exit.json')['exit_code']==0
sys.path.insert(0,str(ROOT))
from tools.abrl_lifecycle import lean_declaration_header
TEST='Tests.OnlineGuessingRandomizedIID.'
targets=load(CONTRACT/'targets-v2.json')['rows']
actual=[]
for row in targets:
    header=lean_declaration_header(PUBLIC,row['name'].rsplit('.',1)[1])
    assert header==' '.join(row['header'].split())
    actual.append(dict(name=row['name'],path=PUBLIC.as_posix(),header=header,raw_header=row['header'],
        raw_header_sha256=row['header_sha256']))
text=CANARY.read_text(encoding='utf8')
for short in re.findall(r'(?m)^theorem (\w+)\b',text):
    start=text.index('theorem '+short)
    raw=text[start:text.index(':=',start)].strip()
    header=lean_declaration_header(CANARY,short)
    assert header==' '.join(raw.split())
    actual.append(dict(name=TEST+short,path=CANARY.as_posix(),header=header,raw_header=raw,
        raw_header_sha256=hashlib.sha256(raw.encode('utf8')).hexdigest()))
write(RUN/'actual-public-canary-headers-v2.json',actual)
write(RUN/'snapshots'/'public-body-candidate-v2.raw',PUBLIC.read_bytes())
write(RUN/'snapshots'/'canary-body-candidate-v3.raw',CANARY.read_bytes())
definitions=[PRE+'privateSeedPastInformation']+[TEST+x for x in re.findall(r'(?m)^def (\w+)\b',text)]
instances=[TEST+x for x in re.findall(r'(?m)^instance (\w+)\b',text)]
reuse=[PRE+x for x in ['expectedFixedMinimum','expectedFixedRegret','expectedFixedMinimum_eq_variance',
    'iid_cumulative_prediction_decomposition','independent_prediction_square']]
names=[r['name'] for r in actual]+definitions+instances+reuse
assert len(names)==len(set(names))
write(RUN/'requested-compiled-body-names-v2.json',dict(names=names,public_proofs=7,
    named_canary_proofs=len(actual)-7,own_information_definition=1,canary_definitions=len(definitions)-1,
    named_probability_instances=len(instances),reused_names=len(reuse),
    anonymous_measurable_instances='Enumerate actual compiler constants in the canary module.'))
template_path=Path('runs/online-regret-domains-20261007/leaves/export-actual-dependencies-v1.lean')
template=template_path.read_text(encoding='utf8')
start=template.index('def targets : Array Name := #[')
end=template.index(']\n',start)+1
template=template[:start]+'def targets : Array Name := #[\n'+',\n'.join('`'+n for n in names)+']'+template[end:]
template=template.replace('Tests.OnlineLearningRegretDomainsCanary','Tests.OnlineGuessingRandomizedIIDCanary')
old='  for n in targets do\n'
assert template.count(old)==1
template=template.replace(old,'''  let anonymous := env.constants.toList.toArray.filterMap fun (n, _) =>
    if n.toString.startsWith "Tests.OnlineGuessingRandomizedIID.instMeasurable" &&
        moduleName env n == "Tests.OnlineGuessingRandomizedIIDCanary" then some n else none
  for n in targets ++ anonymous do
''',1)
old='Existing2shared Regret proofs/2definitions plus8named validation proofs/8fixturedefinitions. Selected20compiled nodes with direct type/VALUE references; zero new production nodes; not the full shared registry or source inventory.'
assert old in template
template=template.replace(old,'Seven frozen public producer/interface proofs, actual named private-seed/infinite-IID/XOR canaries, complete information/fixture definitions, named probability instances and actual anonymous measurable instances, plus five shared reused nodes. Actual direct TYPE/VALUE occurrences, not source coverage or a whole registry.')
write(RUN/'leaves'/'export-compiled-body-graph-v2.lean',template)
gate('compiled-body-value-graph-v2','lake','env','lean','--run',RUN/'leaves/export-compiled-body-graph-v2.lean',RUN/'compiled-body-value-graph-v2.json')
graph=load(RUN/'compiled-body-value-graph-v2.json')
assert all(n['has_value'] for n in graph['nodes'])
assert {n['name'] for n in graph['nodes']}>=set(names)
anonymous=[n for n in graph['nodes'] if n['name'] not in names]
assert len(anonymous)==2,anonymous
write(RUN/'actual-compiled-kind-bindings-v2.json',dict(nodes=len(graph['nodes']),
    kinds={k:sum(n['kind']==k for n in graph['nodes']) for k in sorted({n['kind'] for n in graph['nodes']})},
    actual_anonymous_measurable_instances=anonymous,public_sha256=sha(PUBLIC),canary_sha256=sha(CANARY),
    compiled_names=[n['name'] for n in graph['nodes']],named_canary_proofs=len(actual)-7,
    coverage_count_is_not_source_progress=True,BODY='pending',chapter_complete=False,goal_complete=False))
headers_fixed(7)
print('Actual compiler graph:',len(graph['nodes']),'nodes;',len(actual)-7,'named canary proofs; exact anonymous measurable instances discovered.')
