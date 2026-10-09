from common_reader_v8 import *
import gzip
fixed()
old=json.loads(gzip.decompress((RUN/'registry-baseline-v1.json.gz').read_bytes()).decode('utf8'))
current=load(SITE/'books/registry.json');manifest=load(SITE/'site-manifest.json')
assert current['lean_verified'] and manifest['lean_verified'] and current['source_commit']==manifest['source_commit']
assert current['identity']==old['identity']
ob={n['id']:n for n in old['nodes']};nb={n['id']:n for n in current['nodes']}
assert len(ob)==10977
for node_id,node in ob.items():assert nb[node_id]==node,node_id
targets=load(CONTRACT/'general-initialization-targets-stabilized-v3.json')['new_targets']
expected={'declaration:'+t['name'] for t in targets}
assert set(nb)-set(ob)==expected and len(nb)==len(ob)+4
assert all(nb[i]['identity_basis']=='source-qualified-name' for i in expected)
moduleHTML={}
for node_id in expected:
    node=nb[node_id];url=node['url'].split('#')[0];p=SITE/url;assert p.is_file();moduleHTML[url]=sha(p)
sys.path.insert(0,str(ROOT))
from tools.abrl_lifecycle import lean_declaration_header,statement_hash
for t in targets:assert statement_hash(lean_declaration_header(PUBLIC,t['name']))==t['statement_hash']
row=next(r for r in load(ROOT/'website/content/readings.json')['readings'] if r['slug']=='online-foundations')
assert len(row['source_theorems'])==21
write(RUN/'registry-v4.json',dict(source_commit=current['source_commit'],source_dirty=manifest['source_dirty'],lean_verified=True,retained_complete_old_nodes=len(ob),new_production_nodes=4,new_production_theorems=4,new_production_definitions=0,new_source_private_nodes=0,total_nodes=len(nb),identity=current['identity'],new_ids=sorted(expected),frozen_headers_unchanged=True,module_HTML_sha256=moduleHTML,source_cards=21,actual_current_registry_sha256=sha(SITE/'books/registry.json'),Test_probes_not_canonical_nodes=True,new_source_family_count=1,source_audit_objects=17,proof_total=None,deployed=False,chapter_complete=False,goal_complete=False))
fixed()
print('Complete old10977shared records unchanged plus exact4public theorem nodes; no per-Book proof tree.',flush=True)
