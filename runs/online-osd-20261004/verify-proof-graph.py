from pathlib import Path
import json,re,hashlib
r=Path('runs/online-osd-20261004');p=Path('tmp/online-osd-full-graph.json');raw=p.read_bytes();g=json.loads(raw);ns='BanditRL.OnlineSubgradientDescent.'
scope={ns+n for n in re.findall(r'^(?:theorem|def|abbrev) (\w+)',Path('BanditRLProof/OnlineSubgradientDescent.lean').read_text(encoding='utf-8'),re.M)}
nodes={n['name']:n for n in g['nodes']};assert scope<=set(nodes),scope-set(nodes)
edges=[e for e in g['edges'] if e['source'] in scope]
required=[
 (ns+'lemma_2_31','BanditRL.OnlineConvex.subgradient_point_finite'),
 (ns+'lemma_2_31','BanditRL.OnlineGradientDescent.proposition_2_11'),
 (ns+'lemma_2_31','EReal.coe_toReal'),
 (ns+'iterate_mem','BanditRL.OnlineGradientDescent.project_spec'),
 (ns+'iterate_support',ns+'currentSubgradient_mem'),
 (ns+'one_step_chain',ns+'lemma_2_31'),
 (ns+'regret_fixed',ns+'one_step_chain'),
 (ns+'regret_variable_bound',ns+'one_step'),
 (ns+'regret_variable_bound','BanditRL.OnlineGradientDescent.weighted_potential_sum'),
 (ns+'regret_variable','Metric.dist_le_diam_of_mem'),
 (ns+'regret_tuned_distance',ns+'regret_fixed'),
 (ns+'regret_tuned',ns+'regret_tuned_distance'),
]
for a,b in required:assert any(e['source']==a and e['target']==b and (e['kind']=='value' or e.get('also_in_value',False)) for e in edges),(a,b)
boundary={e['target'] for e in edges}-scope
v={'full_export_sha256':hashlib.sha256(raw).hexdigest(),'full_export_counts':g['counts'],'extraction':g['extraction'],'lean_version':g['lean_version'],'required_proof_value_checks':required,'scope_nodes':len(scope),'boundary_nodes':len(boundary),'nodes':[nodes[n] for n in sorted(scope|boundary)],'edges':edges}
with (r/'compiled-dependencies.json').open('w',encoding='utf-8',newline='\n') as f:json.dump(v,f,ensure_ascii=False,indent=2);f.write('\n')
print(json.dumps({'status':'passed','required_proof_value_checks':len(required),'scope_nodes':len(scope),'boundary_nodes':len(boundary),'edges':len(edges),'full_counts':g['counts']}))
