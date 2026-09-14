import json,hashlib
from pathlib import Path
p=Path('tmp/online-expectation-graph.json');raw=p.read_bytes();graph=json.loads(raw)
ns='BanditRL.OnlineConvex.'
local=list(json.loads(Path('docs/contracts/online-expectation-v1/headers.json').read_text(encoding='utf-8')))
nodes=[n for n in graph['nodes'] if any(n['name']==ns+x or n['name'].startswith(ns+x+'.') for x in local)]
names={n['name'] for n in nodes}
assert all(ns+x in names for x in local)
edges=[e for e in graph['edges'] if e['source'] in names]
assert not any('sorryAx' in str(e) for e in edges)
required=[('signedExpectation_coe_integrable','positiveIntegral_coe_ne_top'),('signedExpectation_coe_integrable','negativeIntegral_coe_ne_top'),('negativeIntegral_coe_ne_top','positiveIntegral_coe_ne_top')]
checks=[]
for a,b in required:
 assert any(e['source']==ns+a and e['target']==ns+b and (e['kind']=='value' or e.get('also_in_value')) for e in edges),(a,b)
 checks.append({'source':ns+a,'target':ns+b,'proof_value_occurrence':True})
for a,b in [('signedExpectation_coe_integrable','MeasureTheory.integral_eq_lintegral_pos_part_sub_lintegral_neg_part'),('signedExpectation_eq_top','EReal.top_sub')]:
 assert any(e['source']==ns+a and e['target']==b and (e['kind']=='value' or e.get('also_in_value')) for e in edges),(a,b)
 checks.append({'source':ns+a,'target':b,'proof_value_occurrence':True})
boundary={e['target'] for e in edges}-names
out={'schema_version':1,'scope':'Extended-real convexity compiled direct constant dependencies; not execution trace','extraction':graph['extraction'],'lean_version':graph['lean_version'],'full_export_sha256':hashlib.sha256(raw).hexdigest(),'full_export_counts':graph['counts'],'required_chain_checks':checks,'source_lf_sha256':hashlib.sha256(Path('BanditRLProof/OnlineExpectation.lean').read_text(encoding='utf-8-sig').encode()).hexdigest(),'nodes':nodes+[n for n in graph['nodes'] if n['name'] in boundary],'edges':edges}
Path('runs/online-jensen-20260914/expectation-compiled-dependencies.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print({'scope_nodes':len(nodes),'boundary_nodes':len(boundary),'edges':len(edges),'chain_checks':len(checks)})
