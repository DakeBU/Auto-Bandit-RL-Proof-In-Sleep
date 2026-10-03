from pathlib import Path
import json,re,hashlib
r=Path('runs/online-affine-subgradient-20261003');p=Path('tmp/online-affine-subgradient-full-graph.json');raw=p.read_bytes();g=json.loads(raw);ns='BanditRL.OnlineConvex.'
scope={ns+n for n in re.findall(r'^(?:theorem|def) (\w+)',Path('BanditRLProof/OnlineAffineSubgradient.lean').read_text(),re.M)};nodes={n['name']:n for n in g['nodes']};assert scope<=set(nodes);edges=[e for e in g['edges'] if e['source'] in scope]
required=[(ns+'theorem_2_28','ContinuousLinearMap.adjoint_inner_left'),(ns+'theorem_2_28','ContinuousLinearMap.map_sub')]
for a,b in required:assert any(e['source']==a and e['target']==b and(e['kind']=='value' or e['also_in_value']) for e in edges),(a,b)
boundary={e['target'] for e in edges}-scope
v={'full_export_sha256':hashlib.sha256(raw).hexdigest(),'full_export_counts':g['counts'],'extraction':g['extraction'],'lean_version':g['lean_version'],'required_proof_value_checks':required,'scope_nodes':len(scope),'boundary_nodes':len(boundary),'nodes':[nodes[n] for n in sorted(scope|boundary)],'edges':edges}
with (r/'compiled-dependencies.json').open('w',encoding='utf-8',newline='\n') as f:json.dump(v,f,ensure_ascii=False,indent=2);f.write('\n')
print(json.dumps({'status':'passed','required_proof_value_checks':len(required),'scope_nodes':len(scope),'boundary_nodes':len(boundary),'edges':len(edges),'full_counts':g['counts']}))
