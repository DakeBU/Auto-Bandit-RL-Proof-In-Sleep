import json,hashlib,sys
from pathlib import Path
run=Path('runs/online-huber-20261003');raw=Path(sys.argv[1] if len(sys.argv)>1 else 'tmp/online-huber-full-graph.json').read_bytes();g=json.loads(raw)
ns='BanditRL.OnlineHuber.';ogd='BanditRL.OnlineGradientDescent.'
local=list(json.loads(Path('docs/contracts/online-huber-public-v1/headers.json').read_text(encoding='utf-8')))+['huber','fullSpace','linearLoss']
nodes=[n for n in g['nodes'] if any(n['name']==ns+x or n['name'].startswith(ns+x+'.') for x in local)]
names={n['name'] for n in nodes};assert all(ns+x in names for x in local)
edges=[e for e in g['edges'] if e['source'] in names];assert not any('sorryAx' in str(e) for e in edges)
pairs=[('hasDerivAt_join',ns+'hasDerivAt_ite_le'),('huber_hasDerivAt',ns+'hasDerivAt_join'),('huber_hasDerivAt',ns+'huber_three_pieces'),('huber_convex',ns+'huber_deriv_clamp'),('huber_linear_hasGradientAt',ns+'huber_hasDerivAt'),('huber_linear_gradient_bound',ns+'huber_deriv_bound'),('huber_linear_gradient_bound',ns+'huber_linear_hasGradientAt'),('huber_regular',ns+'huber_linear_convex'),('huber_step',ns+'project_fullSpace'),('huber_step',ns+'huber_deriv_source'),('huber_regret_fixed',ogd+'theorem_2_13_fixed'),('huber_regret_fixed',ns+'huber_regular'),('huber_regret_fixed',ns+'huber_linear_gradient_bound'),('huber_average_bound',ns+'huber_regret_fixed'),('huber_average_eventually',ns+'huber_average_bound'),('huber_average_eventually',ns+'huber_rate_tendsto')]
checks=[]
for a,b in pairs:
 assert any(e['source']==ns+a and e['target']==b and (e['kind']=='value' or e.get('also_in_value')) for e in edges),(a,b)
 checks.append({'source':ns+a,'target':b,'proof_value_occurrence':True})
source=Path('BanditRLProof/OnlineHuber.lean').read_text(encoding='utf-8-sig');digest=hashlib.sha256(source.encode()).hexdigest()
assert digest==json.loads((run/'public-frozen-check.json').read_text(encoding='utf-8-sig'))['source_lf_sha256']
boundary={e['target'] for e in edges}-names
out={'schema_version':1,'scope':'Example2.15 actual Huber OGD proof chain; direct proof constants, not an execution trace','extraction':g['extraction'],'lean_version':g['lean_version'],'full_export_sha256':hashlib.sha256(raw).hexdigest(),'full_export_counts':g['counts'],'source_lf_sha256':digest,'required_chain_checks':checks,'nodes':nodes+[n for n in g['nodes'] if n['name'] in boundary],'edges':edges}
(run/(sys.argv[2] if len(sys.argv)>2 else 'compiled-dependencies.json')).write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print({'scope_nodes':len(nodes),'boundary_nodes':len(boundary),'edges':len(edges),'chain_checks':len(checks)})
