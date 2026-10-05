"""Match retained shared declaration nodes to current actual native headers."""
from pathlib import Path
import hashlib,json,re,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header
run=Path(__file__).parent;site=Path('tmp/online-convex-migration-site-final01')
registry=json.loads((site/'books/registry.json').read_text(encoding='utf-8'))
freeze=json.loads((run/'draft-freeze-v1.json').read_text(encoding='utf-8'));checks=[]
for g,names in freeze['groups'].items():
    p=Path('BanditRLProof')/(g+'.lean');names=names+freeze['definitions'].get(g,[])
    route='online-convex' if g in ['OnlineConvexExtended','OnlineConvexExamples'] else 'online-convex-closures'
    for n in names:
        full='BanditRL.OnlineConvex.'+n;nodes=[x for x in registry['nodes'] if x['id']=='declaration:'+full];assert len(nodes)==1,full
        node=nodes[0];h=hashlib.sha256(lean_declaration_header(p,n).encode('utf-8')).hexdigest()
        assert node['statement_sha256']==h and node['status']=='compiled',full
        assert 'online-learning' in node['books'] and 'teaching:'+route in node['chapters'],full
        checks.append(dict(name=full,native_hash=h,unique_canonical_node=True,status=node['status'],books=node['books'],chapters=node['chapters'],matched=True))
assert len(checks)==27 and registry['lean_verified'] is True
manifest=json.loads((site/'site-manifest.json').read_text(encoding='utf-8'));assert manifest['source_dirty'] is False
assert manifest['source_commit']==registry['source_commit']
old=json.loads(Path('tmp/online-ftl-migration-site-final01/books/registry.json').read_text(encoding='utf-8'))
new={n['id']:n for n in registry['nodes']};assert len(new)==len(registry['nodes'])
assert all(n['id'] in new and new[n['id']]['url']==n['url'] for n in old['nodes'])
assert len(old['nodes'])==len(registry['nodes']) and old['identity']==registry['identity']
result=dict(status='passed',registry_path=(site/'books/registry.json').as_posix(),registry_sha256=hashlib.sha256((site/'books/registry.json').read_bytes()).hexdigest(),
    source_commit=registry['source_commit'],lean_verified=True,source_dirty=False,identity=registry['identity'],
    preserved_base_node_ids_and_urls=len(old['nodes']),new_registry_nodes=0,checks=checks)
with (run/'registry-final01.json').open('w',encoding='utf-8',newline='\n') as f:json.dump(result,f,indent=2);f.write('\n')
print('Matched27 unique actual native shared nodes; all',len(old['nodes']),'old IDs/URLs retained; zero new nodes.')
