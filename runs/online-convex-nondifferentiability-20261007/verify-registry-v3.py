from common_v4 import *
site=Path('tmp/online-convex-nondifferentiability-site-v1');r=load(site/'books/registry.json');m=load(site/'site-manifest.json');old=load('tmp/online-lipschitz-migration-site-v1/books/registry.json')
assert r['lean_verified'] and m['lean_verified'] and not m['source_dirty'] and r['source_commit']==m['source_commit']
nodes={n['id']:n for n in r['nodes']};base={n['id']:n for n in old['nodes']};assert len(base)==10811
assert set(base)<=set(nodes) and all(nodes[i]['url']==n['url'] for i,n in base.items()) and r['identity']==old['identity']
expected={'declaration:'+PRE+n for n in load(CONTRACT/'headers.json')};assert set(nodes)-set(base)==expected
checks=[]
for n,h in load(CONTRACT/'native-statement-fingerprints-v1.json').items():
 node=nodes['declaration:'+PRE+n];assert node['status']=='compiled' and node['statement_sha256']==h
 assert 'online-learning' in node['books'] and 'teaching:online-lipschitz' in node['chapters'];checks.append(dict(name=PRE+n,native_hash=h,url=node['url'],unique_shared_canonical_node=True))
x=next(a for a in load('website/content/readings.json')['readings'] if a['slug']==ROUTE)
assert len(x['notation'])==3 and len(x['teaching_route'])==3 and len(x['source_theorems'])==3
assert len([a for a in load('website/content/highlights.json')['highlights'] if a.get('chapter')==ROUTE])==3
html=(site/'modules/banditrlproof-onlineconvexnondifferentiability/index.html').read_text(encoding='utf-8');assert all(a['name'] in html for a in checks)
write(RUN/'registry-v2.json',dict(status='passed',source_commit=m['source_commit'],source_dirty=False,lean_verified=True,identity=r['identity'],registry_path=(site/'books/registry.json').as_posix(),registry_sha256=sha(site/'books/registry.json'),checks=checks,preserved_base_node_IDs_and_URLs=10811,new_registry_declaration_nodes=4,total_registry_nodes=len(nodes),new_module_view_separate_from_decl_only_Bookregistry=True,canonical_shared_nodes_not_perBookcopies=True,highlight_links=3,curated_links=3,notation_entries=3,source_cards=3,new_canonical_public_nodes=4))
print('All10811oldIDsURLs/fournewcompiledsourcequalifieddeclarations: total',len(nodes),'sharedregistry. 3cards/highlights/curated,3notation.')
