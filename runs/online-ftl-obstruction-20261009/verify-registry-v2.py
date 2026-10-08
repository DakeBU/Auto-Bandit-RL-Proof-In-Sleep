from common_body_v2 import *
import gzip
integrated_fixed()
old=json.loads(gzip.decompress((RUN/'registry-baseline-v1.json.gz').read_bytes()).decode('utf8'))
current=load(SITE/'books/registry.json');manifest=load(SITE/'site-manifest.json')
assert current['lean_verified'] and manifest['lean_verified']
assert current['source_commit']==manifest['source_commit'] and current['identity']==old['identity']
ob={n['id']:n for n in old['nodes']};nb={n['id']:n for n in current['nodes']}
assert len(ob)==10964 and len(nb)==10977
for node_id,node in ob.items():assert nb[node_id]==node,node_id
targets=load(CONTRACT/'targets-v1.json')['targets']
expected={'declaration:'+t['name'] for t in targets}|{'declaration:BanditRL.OnlineLearning.dyadicObservation'}
private_names=['dyadicObservation_binary','dyadic_pair','dyadic_prefix_pair','dyadic_high_count',
    'dyadic_low_count','dyadic_high_mean','dyadic_low_mean','dyadic_horizons_tendsto']
private_expected={'declaration:BanditRL.OnlineLearning.'+n for n in private_names}
assert set(nb)-set(ob)==expected|private_expected
assert all(nb[i]['identity_basis']=='source-qualified-name' for i in expected)
assert all(nb[i]['identity_basis']=='source-private-name' for i in private_expected)
moduleHTML={}
for node_id in expected:
    node=nb[node_id];url=node['url'].split('#')[0];p=SITE/url;assert p.is_file();moduleHTML[url]=sha(p)
for t in targets:assert statement_hash(lean_declaration_header(PUBLIC,t['name']))==t['statement_hash']
row=next(r for r in load(ROOT/'website/content/readings.json')['readings'] if r['slug']=='online-foundations')
assert len(row['source_theorems'])==20
write(RUN/'registry-v2.json',dict(source_commit=current['source_commit'],source_dirty=manifest['source_dirty'],lean_verified=True,
    retained_complete_old_nodes=10964,new_production_nodes=5,new_production_theorems=4,new_production_definitions=1,
    new_source_private_nodes=8,private_ids=sorted(private_expected),private_nodes_not_public_instantiable=True,total_nodes=10977,identity=current['identity'],new_ids=sorted(expected),frozen_headers_unchanged=True,
    module_HTML_sha256=moduleHTML,source_cards=20,actual_current_registry_sha256=sha(SITE/'books/registry.json'),
    deployed=False,chapter_complete=False,goal_complete=False))
print('Actual10964 complete old shared records plus4 PUBLIC production theorems/1 PUBLIC definition and8 source-private helpers.',flush=True)
