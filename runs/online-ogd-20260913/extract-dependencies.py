import json,hashlib
from pathlib import Path
p=Path('tmp/ogd-environment-graph.json');raw=p.read_bytes();d=json.loads(raw)
ns='BanditRL.OnlineGradientDescent.'
nodes=[n for n in d['nodes'] if n['name'].startswith(ns)]
names={n['name'] for n in nodes};edges=[e for e in d['edges'] if e['source'] in names]
boundary={e['target'] for e in edges}-names
assert not any('sorryAx' in str(e) for e in edges)
required=[('lemma_2_12','first_order'),('lemma_2_12','proposition_2_11'),('theorem_2_13_fixed','lemma_2_12'),('theorem_2_13_fixed','iterate_mem'),('equation_2_1_distance','theorem_2_13_fixed'),('equation_2_1','equation_2_1_distance')]
checks=[]
for a,b in required:
 matched=[e for e in edges if e['source']==ns+a and e['target']==ns+b and (e['kind']=='value' or e['also_in_value'])]
 assert matched,(a,b)
 checks.append({'source':ns+a,'target':ns+b,'proof_value_occurrence':True})
source=Path('BanditRLProof/OnlineGradientDescent.lean').read_text(encoding='utf-8-sig')
out={'schema_version':1,'scope':'OGD module declarations and their direct constant dependencies; excerpt of full root environment export','extraction':d['extraction'],'lean_version':d['lean_version'],'full_export_sha256':hashlib.sha256(raw).hexdigest(),'full_export_counts':d['counts'],'source_lf_sha256':hashlib.sha256(source.encode()).hexdigest(),'required_chain_checks':checks,'nodes':nodes+[n for n in d['nodes'] if n['name'] in boundary],'edges':edges}
Path('runs/online-ogd-20260913/compiled-dependencies.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
print({'module_nodes':len(nodes),'direct_boundary_nodes':len(boundary),'edges':len(edges),'required_chain_checks':len(checks)})
