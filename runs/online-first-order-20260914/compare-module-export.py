from pathlib import Path
import json,hashlib
r=Path('runs/online-first-order-20260914')
full_path=Path('tmp/online-first-order-graph.json')
small_path=Path('tmp/online-first-order-module-graph.json')
full_raw=full_path.read_bytes();small_raw=small_path.read_bytes()
full=json.loads(full_raw);wrapped=json.loads(small_raw)
assert wrapped['actual_import_root']=='BanditRLProof.OnlineConvexFirstOrder'
assert wrapped['scope']=='module-import-closure-not-full-project'
log=(r/'module-export-standalone.log').read_text(encoding='utf-8-sig')
assert 'PANIC' not in log and 'error:' not in log
small=wrapped['graph'];big_nodes={n['name']:n for n in full['nodes']}
node_diffs=[]
for n in small['nodes']:
 if big_nodes.get(n['name'])!=n:node_diffs.append({'name':n['name'],'small':n,'full':big_nodes.get(n['name'])})
project_names={n['name'] for n in small['nodes'] if n['scope']=='project'}
big_edges=[e for e in full['edges'] if e['source'] in project_names]
key=lambda x:json.dumps(x,sort_keys=True)
assert not node_diffs,node_diffs[:2]
assert sorted(map(key,small['edges']))==sorted(map(key,big_edges))
out={'status':'passed','scope':'This module import closure exactly matches its projection from the same compiled whole-project graph; not a whole-project export','actual_import_root':wrapped['actual_import_root'],'base_exporter':'tools/ProofGraphExport.lean','full_export_sha256':hashlib.sha256(full_raw).hexdigest(),'module_export_sha256':hashlib.sha256(small_raw).hexdigest(),'compared_nodes':len(small['nodes']),'compared_project_nodes':len(project_names),'compared_edges':len(small['edges']),'all_node_fields_equal':True,'all_direct_edges_equal':True,'rejected_experiment':'module-export.log: nested #eval emitted PANIC despite exit0; excluded','full_root_Tests_harness_still_required':True}
(r/'module-export-equivalence.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8');print(out)
