import json,hashlib
from pathlib import Path
p=Path('tmp/online-ch2-variable-graph.json');raw=p.read_bytes();graph=json.loads(raw)
ns='BanditRL.OnlineGradientDescent.'
local=list(json.loads(Path('docs/contracts/online-ogd-variable-v1/headers.json').read_text(encoding='utf-8')))+['iterateVariable','regretVariable']
nodes=[n for n in graph['nodes'] if any(n['name']==ns+x or n['name'].startswith(ns+x+'.') for x in local)]
names={n['name'] for n in nodes}
assert all(ns+x in names for x in local)
edges=[e for e in graph['edges'] if e['source'] in names]
assert not any('sorryAx' in str(e) for e in edges)
required=[('iterateVariable_mem','project_spec'),('variable_one_step','lemma_2_12'),('variable_one_step','iterateVariable_mem'),('theorem_2_13_variable_bound','weighted_potential_sum'),('theorem_2_13_variable_bound','variable_one_step'),('theorem_2_13_variable_bound','iterateVariable_mem'),('theorem_2_13_variable','theorem_2_13_variable_bound')]
checks=[]
for a,b in required:
 assert any(e['source']==ns+a and e['target']==ns+b and (e['kind']=='value' or e.get('also_in_value')) for e in edges),(a,b)
 checks.append({'source':ns+a,'target':ns+b,'proof_value_occurrence':True})
boundary={e['target'] for e in edges}-names
out={'schema_version':1,'scope':'Variable OGD compiled direct constant dependencies; not execution trace','extraction':graph['extraction'],'lean_version':graph['lean_version'],'full_export_sha256':hashlib.sha256(raw).hexdigest(),'full_export_counts':graph['counts'],'required_chain_checks':checks,'source_lf_sha256':hashlib.sha256(Path('BanditRLProof/OnlineGradientDescentVariable.lean').read_text(encoding='utf-8-sig').encode()).hexdigest(),'nodes':nodes+[n for n in graph['nodes'] if n['name'] in boundary],'edges':edges}
Path('runs/online-ch2-variable-20260914/compiled-dependencies.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print({'scope_nodes':len(nodes),'boundary_nodes':len(boundary),'edges':len(edges),'chain_checks':len(checks)})
