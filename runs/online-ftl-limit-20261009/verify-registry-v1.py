from common_body_v1 import *
import gzip
integrated_fixed()
old=json.loads(gzip.decompress((RUN/'registry-baseline-v1.json.gz').read_bytes()).decode('utf8'))
current=load(SITE/'books/registry.json')
manifest=load(SITE/'site-manifest.json')
assert current['lean_verified'] and manifest['lean_verified']
assert current['source_commit']==manifest['source_commit']
assert current['identity']==old['identity']
ob={n['id']:n for n in old['nodes']}
nb={n['id']:n for n in current['nodes']}
assert len(ob)==10959 and len(nb)==10964
for node_id,node in ob.items():
    assert nb[node_id]==node,node_id
targets=load(CONTRACT/'targets-v1.json')['targets']
expected={'declaration:'+t['name'] for t in targets}
assert set(nb)-set(ob)==expected
moduleHTML={}
for t in targets:
    node=nb['declaration:'+t['name']]
    assert node['full_name']==t['name'] if 'full_name' in node else True
    url=node['url'].split('#')[0]
    p=SITE/url
    assert p.is_file(),(url,p)
    moduleHTML[url]=sha(p)
    header=lean_declaration_header(PUBLIC,t['name'])
    assert statement_hash(header)==t['statement_hash']
readings=load(ROOT/'website/content/readings.json')['readings']
row=next(r for r in readings if r['slug']=='online-foundations')
assert len(row['source_theorems'])==19
write(RUN/'registry-v1.json',dict(source_commit=current['source_commit'],source_dirty=manifest['source_dirty'],lean_verified=True,
    retained_complete_old_nodes=10959,new_production_nodes=5,total_nodes=10964,identity=current['identity'],
    new_ids=sorted(expected),frozen_headers_unchanged=True,module_HTML_sha256=moduleHTML,source_cards=19,
    actual_current_registry_sha256=sha(SITE/'books/registry.json'),deployed=False,chapter_complete=False,goal_complete=False))
print('Actual10959 COMPLETEoldregistryrecords retained plus exactly5 newproductiontheorems.',flush=True)
