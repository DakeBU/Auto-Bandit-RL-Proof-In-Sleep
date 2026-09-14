import json, hashlib
from pathlib import Path

run = Path('runs/online-guessing-ogd-20260914')
raw = Path('tmp/online-guessing-ogd-full-graph.json').read_bytes()
graph = json.loads(raw)
ns = 'BanditRL.OnlineGradientDescent.'
local = []
sources = {}
for contract, module, report in [
    ('online-guessing-ogd-v2', 'OnlineGuessingOGD', 'frozen-check.json'),
    ('online-guessing-lower-v2', 'OnlineGuessingLower', 'lower-frozen-check.json'),
]:
    local.extend(json.loads(Path('docs/contracts', contract, 'headers.json').read_text(encoding='utf-8')))
    path = Path('BanditRLProof', module + '.lean')
    digest = hashlib.sha256(path.read_text(encoding='utf-8-sig').encode()).hexdigest()
    assert digest == json.loads((run / report).read_text(encoding='utf-8-sig'))['source_lf_sha256']
    sources[str(path)] = digest
nodes = [n for n in graph['nodes'] if any(n['name'] == ns+x or n['name'].startswith(ns+x+'.') for x in local)]
names = {n['name'] for n in nodes}
assert all(ns+x in names for x in local)
edges = [e for e in graph['edges'] if e['source'] in names]
assert not any('sorryAx' in str(e) for e in edges)
required = [
    ('project_unitInterval', 'project_eq_of_variational'),
    ('square_step_clamp', 'project_unitInterval'),
    ('square_step_clamp', 'gradient_square'),
    ('gradient_square_bound', 'gradient_square'),
    ('example_2_14', 'equation_2_1'),
    ('example_2_14', 'iterate_mem'),
    ('example_2_14', 'square_regular'),
    ('example_2_14', 'gradient_square_bound'),
    ('guessing_zero_trajectory', 'square_step_clamp'),
    ('guessing_squared_horizon_lower', 'guessing_zero_trajectory'),
    ('guessing_squared_horizon_lower', 'guessing_tuned_eta_square'),
]
checks = []
for a, b in required:
    assert any(e['source'] == ns+a and e['target'] == ns+b and
               (e['kind'] == 'value' or e.get('also_in_value')) for e in edges), (a, b)
    checks.append({'source': ns+a, 'target': ns+b, 'proof_value_occurrence': True})
boundary = {e['target'] for e in edges} - names
out = {'schema_version': 1, 'scope': 'Example 2.14 upper guarantee and derived lower witness; compiled direct constant dependencies, not execution trace',
       'extraction': graph['extraction'], 'lean_version': graph['lean_version'],
       'full_export_sha256': hashlib.sha256(raw).hexdigest(), 'full_export_counts': graph['counts'],
       'required_chain_checks': checks, 'source_lf_sha256': sources,
       'nodes': nodes + [n for n in graph['nodes'] if n['name'] in boundary], 'edges': edges}
(run / 'compiled-dependencies.json').write_text(json.dumps(out, indent=2)+'\n', encoding='utf-8')
print({'scope_nodes': len(nodes), 'boundary_nodes': len(boundary), 'edges': len(edges), 'chain_checks': len(checks)})
