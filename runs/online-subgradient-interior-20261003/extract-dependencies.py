import json,hashlib
from pathlib import Path
r=Path('runs/online-subgradient-interior-20261003');raw=Path('tmp/online-subgradient-interior-full-graph.json').read_bytes();g=json.loads(raw)
ns='BanditRL.OnlineConvex.';local=['affine_support_of_domain_interior','affine_minorant_of_domain_interior','subgradient_exists_of_domain_interior']
nodes=[n for n in g['nodes'] if any(n['name']==ns+x or n['name'].startswith(ns+x+'.') for x in local)];names={n['name'] for n in nodes};assert all(ns+x in names for x in local)
edges=[e for e in g['edges'] if e['source'] in names];assert not any('sorryAx' in str(e) for e in edges)
pairs=[('affine_support_of_domain_interior',ns+'supporting_functional_at_closure'),('affine_minorant_of_domain_interior',ns+'affine_support_of_domain_interior'),('subgradient_exists_of_domain_interior',ns+'affine_support_of_domain_interior'),('subgradient_exists_of_domain_interior','InnerProductSpace.toDual_symm_apply'),('subgradient_exists_of_domain_interior','EReal.coe_add')]
for a,b in pairs:assert any(e['source']==ns+a and e['target']==b and (e['kind']=='value' or e.get('also_in_value')) for e in edges),(a,b)
boundary={e['target'] for e in edges}-names
out={'full_export_sha256':hashlib.sha256(raw).hexdigest(),'full_export_counts':g['counts'],'extraction':g['extraction'],'lean_version':g['lean_version'],'required_proof_value_checks':pairs,'scope_nodes':len(nodes),'boundary_nodes':len(boundary),'nodes':nodes+[n for n in g['nodes'] if n['name'] in boundary],'edges':edges}
(r/'compiled-dependencies.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8');print({'scope_nodes':len(nodes),'boundary_nodes':len(boundary),'edges':len(edges),'proof_value_checks':len(pairs)})
