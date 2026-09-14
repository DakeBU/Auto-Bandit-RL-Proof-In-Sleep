import json,hashlib
from pathlib import Path
p=Path('tmp/online-barycenter-graph.json');raw=p.read_bytes();graph=json.loads(raw)
ns='BanditRL.OnlineConvex.'
local=list(json.loads(Path('docs/contracts/online-barycenter-v1/headers.json').read_text(encoding='utf-8')))
nodes=[n for n in graph['nodes'] if any(n['name']==ns+x or n['name'].startswith(ns+x+'.') for x in local)]
names={n['name'] for n in nodes}
assert all(ns+x in names for x in local)
edges=[e for e in graph['edges'] if e['source'] in names]
assert not any('sorryAx' in str(e) for e in edges)
required=[('integral_mem_convex_finiteDimensional','supporting_functional_at_closure'),('integral_mem_convex_finiteDimensional','supporting_functional_ae_eq_mean')]
checks=[]
for a,b in required:
 assert any(e['source']==ns+a and e['target']==ns+b and (e['kind']=='value' or e.get('also_in_value')) for e in edges),(a,b)
 checks.append({'source':ns+a,'target':ns+b,'proof_value_occurrence':True})
for a,b in [('integral_mem_convex_finiteDimensional','Submodule.finrank_lt'),('integral_mem_convex_finiteDimensional','Convex.integral_mem'),('integral_mem_convex_finiteDimensional','ContinuousLinearMap.integral_comp_comm'),('integral_mem_convex_finiteDimensional','MeasureTheory.LipschitzWith.integrable_comp_iff_of_antilipschitz'),('supporting_functional_at_closure','geometric_hahn_banach_of_nonempty_interior_point'),('supporting_functional_at_closure','Submodule.exists_le_ker_of_lt_top'),('supporting_functional_ae_eq_mean','MeasureTheory.integral_eq_iff_of_ae_le')]:
 assert any(e['source']==ns+a and e['target']==b and (e['kind']=='value' or e.get('also_in_value')) for e in edges),(a,b)
 checks.append({'source':ns+a,'target':b,'proof_value_occurrence':True})
boundary={e['target'] for e in edges}-names
out={'schema_version':1,'scope':'Arbitrary convex barycenter compiled direct constant dependencies; not execution trace','extraction':graph['extraction'],'lean_version':graph['lean_version'],'full_export_sha256':hashlib.sha256(raw).hexdigest(),'full_export_counts':graph['counts'],'required_chain_checks':checks,'source_lf_sha256':hashlib.sha256(Path('BanditRLProof/OnlineConvexBarycenter.lean').read_text(encoding='utf-8-sig').encode()).hexdigest(),'nodes':nodes+[n for n in graph['nodes'] if n['name'] in boundary],'edges':edges}
Path('runs/online-barycenter-20260914/compiled-dependencies.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print({'scope_nodes':len(nodes),'boundary_nodes':len(boundary),'edges':len(edges),'chain_checks':len(checks)})
