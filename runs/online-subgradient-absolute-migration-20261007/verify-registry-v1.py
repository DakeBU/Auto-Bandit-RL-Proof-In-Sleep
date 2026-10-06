from common import *
site=Path('tmp/online-subgradient-absolute-migration-site-v1');r=load(site/'books/registry.json');m=load(site/'site-manifest.json');old=load('tmp/online-subgradient-sum-migration-site-v2/books/registry.json')
assert r['lean_verified'] is True and m['lean_verified'] is True and m['source_dirty'] is False and r['source_commit']==m['source_commit']
nodes={n['id']:n for n in r['nodes']};oldnodes={n['id']:n for n in old['nodes']}
assert len(nodes)==len(r['nodes'])==len(oldnodes)==10811 and set(nodes)==set(oldnodes) and r['identity']==old['identity']
assert all(nodes[i]['url']==n['url'] for i,n in oldnodes.items())
f=fixed(True);checks=[]
for n,h in f['headers'].items():
 node=nodes['declaration:'+PRE+n];assert node['status']=='compiled' and node['statement_sha256']==h
 assert 'online-learning' in node['books'] and 'teaching:online-subgradient-absolute' in node['chapters']
 checks.append(dict(name=PRE+n,native_hash=h,url=node['url'],unique_canonical_node=True,new_canonical_mathproof=False))
x=next(x for x in load('website/content/readings.json')['readings'] if x['slug']==ROUTE)
assert len(x['notation'])==3 and x['teaching_route']==load(RUN/'reader-integration-v1.json')['original_four_routes_retained']
html=(site/'modules/banditrlproof-onlinesubgradientabsolute/index.html').read_text(encoding='utf-8');assert all(c['name'] in html for c in checks)
write(RUN/'registry-v1.json',dict(status='passed',source_commit=m['source_commit'],source_dirty=False,lean_verified=True,registry_path=(site/'books/registry.json').as_posix(),registry_sha256=sha(site/'books/registry.json'),identity=r['identity'],checks=checks,preserved_base_node_ids_and_urls=10811,new_registry_nodes=0,total_registry_nodes=10811,canonical_shared_nodes_not_perBookcopies=True,original_four_routes_and_three_notation_entries=True))
print('All10811 oldIDsURLs preserved; four exact sourcequalified canonical links; no new nodes.')
