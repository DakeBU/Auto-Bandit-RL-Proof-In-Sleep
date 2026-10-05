"""Check two canonical shared nodes and preserve every inherited ID and URL."""
from pathlib import Path
import hashlib,json
run=Path(__file__).parent;site=Path('tmp/online-finite-loss-site-v1')
def load(p):return json.loads(Path(p).read_text(encoding='utf-8'))
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
registry=load(site/'books/registry.json');manifest=load(site/'site-manifest.json')
assert registry['lean_verified'] is True and manifest['source_dirty'] is False
assert manifest['source_commit']==registry['source_commit']
new={n['id']:n for n in registry['nodes']};assert len(new)==len(registry['nodes'])
freeze=load(run/'draft-freeze-v1.json');checks=[]
for n,h in freeze['headers'].items():
    full='BanditRL.OnlineConvex.'+n;node=new['declaration:'+full]
    assert node['status']=='compiled' and node['statement_sha256']==h
    assert 'online-learning' in node['books'] and 'teaching:online-convex' in node['chapters']
    checks.append(dict(name=full,native_hash=h,unique_canonical_node=True,books=node['books'],chapters=node['chapters'],url=node['url']))
old=load('tmp/online-convex-migration-site-final02/books/registry.json')
assert all(n['id'] in new and new[n['id']]['url']==n['url'] for n in old['nodes'])
assert registry['identity']==old['identity']
assert len(new)-len(old['nodes'])==2
out=run/'registry-v1.json';assert not out.exists()
with out.open('w',encoding='utf-8',newline='\n') as f:json.dump(dict(status='passed',source_commit=manifest['source_commit'],source_dirty=False,lean_verified=True,
    registry_path=(site/'books/registry.json').as_posix(),registry_sha256=sha(site/'books/registry.json'),identity=registry['identity'],
    checks=checks,preserved_base_node_ids_and_urls=len(old['nodes']),new_registry_nodes=2),f,indent=2);f.write('\n')
print('Two actual frozen canonical nodes matched; preserved',len(old['nodes']),'old IDs/URLs; shared Book identity unchanged.')
