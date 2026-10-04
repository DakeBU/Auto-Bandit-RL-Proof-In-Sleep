"""Verify actual compiled proof-value dependencies, separate from teaching links."""
from pathlib import Path
import hashlib,json,re
run=Path(__file__).parent
export=Path('tmp/online-optimal-step-full-graph.json')
raw=export.read_bytes();graph=json.loads(raw)
ns='BanditRL.OnlineOptimalStep.'
scope={ns+n for n in re.findall(r'^(?:noncomputable )?(?:theorem|def|abbrev) (\w+)',
    Path('BanditRLProof/OnlineOptimalStep.lean').read_text(encoding='utf-8'),re.M)}
assert len(scope)==13
nodes={n['name']:n for n in graph['nodes']};assert scope<=set(nodes),scope-set(nodes)
edges=[e for e in graph['edges'] if e['source'] in scope]
required=[(ns+a,ns+b) for a,b in [
 ('lower_bound','gap_identity'),('optimal_value','gap_identity'),('optimal_value','optimal_positive'),
 ('optimal_unique','gap_identity'),('optimal_unique','optimal_value'),
 ('source_argmin','optimal_positive'),('source_argmin','optimal_value'),('source_argmin','lower_bound'),
 ('distance_energy_argmin','source_argmin'),('distance_energy_argmin','optimal_value'),
 ('diameter_argmin','distance_energy_argmin')]]
for a,b in required:
    assert any(e['source']==a and e['target']==b and
        (e['kind']=='value' or e.get('also_in_value',False)) for e in edges),(a,b)
boundary={e['target'] for e in edges}-scope
result=dict(full_export_sha256=hashlib.sha256(raw).hexdigest(),full_export_path=export.as_posix(),
    full_export_counts=graph['counts'],extraction=graph['extraction'],lean_version=graph['lean_version'],
    required_proof_value_checks=required,scope_nodes=len(scope),boundary_nodes=len(boundary),
    nodes=[nodes[n] for n in sorted(scope|boundary)],edges=edges)
with (run/'compiled-dependencies.json').open('w',encoding='utf-8',newline='\n') as f:
    json.dump(result,f,indent=2);f.write('\n')
print(json.dumps(dict(status='passed',required_proof_value_checks=len(required),scope_nodes=len(scope),
    boundary_nodes=len(boundary),edges=len(edges),full_counts=graph['counts'])))
