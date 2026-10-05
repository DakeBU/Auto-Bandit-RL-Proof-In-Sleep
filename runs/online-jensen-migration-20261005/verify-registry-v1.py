"""Bind retained canonical shared nodes and preserve every previous node ID/URL."""
from pathlib import Path
import hashlib,json
run=Path(__file__).parent;site=Path('tmp/online-jensen-migration-site-v1')
load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'))
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
registry=load(site/'books/registry.json');manifest=load(site/'site-manifest.json')
assert registry['lean_verified'] is True and manifest['source_dirty'] is False
assert manifest['source_commit']==registry['source_commit']
new={n['id']:n for n in registry['nodes']};assert len(new)==len(registry['nodes'])
freeze=load(run/'draft-freeze-v1.json');checks=[]
for n,h in freeze['headers'].items():
 full='BanditRL.OnlineConvex.'+n;node=new['declaration:'+full]
 assert node['status']=='compiled' and node['statement_sha256']==h
 assert 'online-learning' in node['books'] and 'teaching:online-jensen' in node['chapters']
 checks.append(dict(name=full,native_hash=h,unique_canonical_node=True,books=node['books'],chapters=node['chapters'],url=node['url']))
old=load('tmp/online-minorant-migration-site-v1/books/registry.json')
assert registry['identity']==old['identity'] and len(new)==len(old['nodes'])
assert all(n['id'] in new and new[n['id']]['url']==n['url'] for n in old['nodes'])
out=run/'registry-v1.json';assert not out.exists()
with out.open('w',encoding='utf-8',newline='\n') as f:
 json.dump(dict(status='passed',source_commit=manifest['source_commit'],source_dirty=False,lean_verified=True,
  registry_path=(site/'books/registry.json').as_posix(),registry_sha256=sha(site/'books/registry.json'),identity=registry['identity'],
  checks=checks,preserved_base_node_ids_and_urls=len(old['nodes']),new_registry_nodes=0),f,indent=2);f.write('\n')
print('Matched2 frozen canonical shared nodes; retained',len(old['nodes']),'old IDs/URLs; zero new nodes.')
