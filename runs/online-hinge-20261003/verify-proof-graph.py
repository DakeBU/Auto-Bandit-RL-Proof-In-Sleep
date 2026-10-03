from pathlib import Path
import json,re,hashlib
r=Path('runs/online-hinge-20261003');p=Path('tmp/online-hinge-full-graph.json');raw=p.read_bytes();g=json.loads(raw);ns='BanditRL.OnlineConvex.'
scope={ns+n for n in re.findall(r'^(?:theorem|def) (\w+)',Path('BanditRLProof/OnlineHinge.lean').read_text(),re.M)};nodes={n['name']:n for n in g['nodes']};assert scope<=set(nodes);edges=[e for e in g['edges'] if e['source'] in scope]
required=[(ns+'example_2_27',ns+'hinge_subdifferential_hull'),(ns+'example_2_27',ns+'hinge_active_zero'),(ns+'example_2_27',ns+'hinge_active_negative'),(ns+'example_2_27',ns+'hinge_active_positive'),(ns+'example_2_27','convexHull_pair'),(ns+'example_2_27','segment_eq_image'),(ns+'hinge_subdifferential_hull',ns+'theorem_2_26'),(ns+'hinge_subdifferential_hull',ns+'affine_convex'),(ns+'hinge_subdifferential_hull',ns+'affine_proper'),(ns+'hinge_subdifferential_hull',ns+'affine_continuous'),(ns+'hinge_family_support',ns+'affine_subdifferential'),(ns+'affine_subdifferential','inner_self_eq_zero')]
for a,b in required:assert any(e['source']==a and e['target']==b and(e['kind']=='value' or e['also_in_value']) for e in edges),(a,b)
boundary={e['target'] for e in edges}-scope
v={'full_export_sha256':hashlib.sha256(raw).hexdigest(),'full_export_counts':g['counts'],'extraction':g['extraction'],'lean_version':g['lean_version'],'required_proof_value_checks':required,'scope_nodes':len(scope),'boundary_nodes':len(boundary),'nodes':[nodes[n] for n in sorted(scope|boundary)],'edges':edges}
with (r/'compiled-dependencies.json').open('w',encoding='utf-8',newline='\n') as f:json.dump(v,f,ensure_ascii=False,indent=2);f.write('\n')
print(json.dumps({'status':'passed','required_proof_value_checks':len(required),'scope_nodes':len(scope),'boundary_nodes':len(boundary),'edges':len(edges),'full_counts':g['counts']}))
