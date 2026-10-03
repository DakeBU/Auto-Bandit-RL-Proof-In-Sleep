import json,hashlib
from pathlib import Path
run=Path('runs/online-subgradient-differentiability-20261003')
raw=Path('tmp/online-subgradient-differentiability-full-graph.json').read_bytes()
graph=json.loads(raw)
ns='BanditRL.OnlineConvex.'
local=['SourceDifferentiableAt','affine_support_of_finite_neighborhood',
 'affine_support_of_domain_interior','affine_minorant_of_domain_interior',
 'sourceDifferentiableAt_regular','subgradient_norm_le_lipschitz_ball',
 'subgradients_locally_bounded','subgradient_limit_of_continuousAt',
 'singleton_subgradient_tendsto','singleton_subdifferential_interior',
 'singleton_subdifferential_hasGradientAt','subgradient_eq_gradient_at_interior',
 'theorem_2_22_forward','theorem_2_22','theorem_2_22_gradient']
nodes=[n for n in graph['nodes'] if any(n['name']==ns+x or n['name'].startswith(ns+x+'.') for x in local)]
names={n['name'] for n in nodes}
assert all(ns+x in names for x in local)
edges=[e for e in graph['edges'] if e['source'] in names]
assert not any('sorryAx' in str(e) for e in edges)
pairs=[('affine_support_of_domain_interior',ns+'affine_support_of_finite_neighborhood'),
 ('affine_minorant_of_domain_interior',ns+'affine_support_of_domain_interior'),
 ('theorem_2_22',ns+'singleton_subdifferential_hasGradientAt'),
 ('theorem_2_22_gradient',ns+'affine_support_of_finite_neighborhood'),
 ('theorem_2_22_gradient',ns+'theorem_2_7'),
 ('singleton_subdifferential_hasGradientAt',ns+'singleton_subdifferential_interior'),
 ('singleton_subdifferential_hasGradientAt',ns+'subgradient_exists_of_domain_interior'),
 ('singleton_subdifferential_hasGradientAt',ns+'singleton_subgradient_tendsto'),
 ('singleton_subgradient_tendsto',ns+'subgradients_locally_bounded'),
 ('singleton_subgradient_tendsto',ns+'subgradient_limit_of_continuousAt'),
 ('singleton_subgradient_tendsto','IsCompact.tendsto_nhds_of_unique_mapClusterPt'),
 ('subgradients_locally_bounded',ns+'subgradient_norm_le_lipschitz_ball')]
for a,b in pairs:
 assert any(e['source']==ns+a and e['target']==b and (e['kind']=='value' or e.get('also_in_value')) for e in edges),(a,b)
boundary={e['target'] for e in edges}-names
out={'full_export_sha256':hashlib.sha256(raw).hexdigest(),'full_export_counts':graph['counts'],
 'extraction':graph['extraction'],'lean_version':graph['lean_version'],
 'required_proof_value_checks':pairs,'scope_nodes':len(nodes),'boundary_nodes':len(boundary),
 'nodes':nodes+[n for n in graph['nodes'] if n['name'] in boundary],'edges':edges}
(run/'compiled-dependencies.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'scope_nodes':len(nodes),'boundary_nodes':len(boundary),'edges':len(edges),'proof_value_checks':len(pairs)}))
