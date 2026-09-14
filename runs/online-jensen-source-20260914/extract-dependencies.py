import json,hashlib
from pathlib import Path
p=Path('tmp/online-jensen-source-graph.json');raw=p.read_bytes();graph=json.loads(raw)
ns='BanditRL.OnlineConvex.'
local=list(json.loads(Path('docs/contracts/online-jensen-v3/headers.json').read_text(encoding='utf-8')))
nodes=[n for n in graph['nodes'] if any(n['name']==ns+x or n['name'].startswith(ns+x+'.') for x in local)]
names={n['name'] for n in nodes}
assert all(ns+x in names for x in local)
edges=[e for e in graph['edges'] if e['source'] in names]
assert not any('sorryAx' in str(e) for e in edges)
required=[('theorem_2_9',ns+'jensen_negativeIntegral_ne_top'),('theorem_2_9',ns+'integral_mem_convex_finiteDimensional'),('theorem_2_9',ns+'signedExpectation_coe_integrable'),('theorem_2_9',ns+'signedExpectation_eq_top'),('jensen_negativeIntegral_ne_top',ns+'convex_affine_minorant'),('jensen_negativeIntegral_ne_top',ns+'negativeIntegral_coe_ne_top'),('theorem_2_9','integral_pair'),('theorem_2_9','MeasureTheory.lintegral_ofReal_ne_top_iff_integrable')]
checks=[]
for a,b in required:
 assert any(e['source']==ns+a and e['target']==b and (e['kind']=='value' or e.get('also_in_value')) for e in edges),(a,b)
 checks.append({'source':ns+a,'target':b,'proof_value_occurrence':True})
boundary={e['target'] for e in edges}-names
out={'schema_version':1,'scope':'Source Jensen compiled direct constant dependencies; not execution trace','extraction':graph['extraction'],'lean_version':graph['lean_version'],'full_export_sha256':hashlib.sha256(raw).hexdigest(),'full_export_counts':graph['counts'],'required_chain_checks':checks,'source_lf_sha256':hashlib.sha256(Path('BanditRLProof/OnlineJensen.lean').read_text(encoding='utf-8-sig').encode()).hexdigest(),'nodes':nodes+[n for n in graph['nodes'] if n['name'] in boundary],'edges':edges}
Path('runs/online-jensen-source-20260914/compiled-dependencies.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print({'scope_nodes':len(nodes),'boundary_nodes':len(boundary),'edges':len(edges),'chain_checks':len(checks)})
