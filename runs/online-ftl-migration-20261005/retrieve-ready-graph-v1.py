"""Reuse actual compiled graph for dependency readiness, not a fresh package gate."""
from pathlib import Path
import hashlib,json
run=Path(__file__).parent;p=Path('tmp/online-ogd-migration-full-graph.json');raw=p.read_bytes();g=json.loads(raw)
assert hashlib.sha256(raw).hexdigest()=='035630137ecb541e2680c1db4f0ce03b2380f46f322efc157227c6fc73bd9613'
ns='BanditRL.OnlineLearning.'
names=['prefixCoefficient','linearFTLPredict','failureCoefficient','prefixCoefficient_eq_sum','linearFTLPredict_prefix',
    'linearFTLPredict_mem','linearFTLPredict_minimizes','failure_prefixCoefficient','failure_prediction','example_2_10']
scope={ns+n for n in names};nodes={n['name']:n for n in g['nodes']};assert scope<=set(nodes)
edges=[e for e in g['edges'] if e['source'] in scope]
required=[('linearFTLPredict_prefix','prefixCoefficient_eq_sum'),('linearFTLPredict_minimizes','prefixCoefficient_eq_sum'),
    ('failure_prediction','failure_prefixCoefficient'),('example_2_10','failure_prediction'),
    ('failure_prefixCoefficient','prefixCoefficient'),('example_2_10','linearFTLPredict')]
for a,b in required:
    assert any(e['source']==ns+a and e['target']==ns+b and (e['kind']=='value' or e.get('also_in_value',False)) for e in edges),(a,b)
original=(run/'original-public-module.lean.txt').read_bytes()
assert original==Path('BanditRLProof/OnlineFTLFailure.lean').read_bytes()
result=dict(status='dependency-readiness-retrieved',graph_path=p.as_posix(),graph_sha256=hashlib.sha256(raw).hexdigest(),
    extraction=g['extraction'],lean_version=g['lean_version'],scope_nodes=10,actual_edges=len(edges),
    boundary_nodes=len({e['target'] for e in edges}-scope),required_actual_value_pairs=[(ns+a,ns+b) for a,b in required],
    nodes=[nodes[n] for n in sorted(scope)],edges=edges,
    current_original_module_sha256=hashlib.sha256(original).hexdigest(),public_module_bytes_unchanged=True,
    boundary='Reuses previous complete compiled shared-root export, including these retained unchanged FTL proofs; actual six value occurrences establish ready dependencies. No fresh export, source/body/current package acceptance or new-proof count is claimed.')
with (run/'ready-dependencies-v1.json').open('w',encoding='utf-8',newline='\n') as f:json.dump(result,f,indent=2);f.write('\n')
print('Ready reused compiled graph:10 FTL nodes/6 actual value pairs; fresh package gates/source acceptance remain pending.')
