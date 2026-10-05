"""Verify twelve theorem headers, the retained domain node, and three new nodes."""
from pathlib import Path
import hashlib,json,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header
run=Path(__file__).parent;site=Path('tmp/online-guessing-migration-site-v1')
load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'))
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
registry=load(site/'books/registry.json');manifest=load(site/'site-manifest.json')
assert registry['lean_verified'] is True and manifest['source_dirty'] is False
assert manifest['source_commit']==registry['source_commit']
nodes={n['id']:n for n in registry['nodes']};assert len(nodes)==len(registry['nodes'])
freeze=load(run/'draft-freeze-v2.json');checks=[]
for name,h in freeze['headers'].items():
 full='BanditRL.OnlineGradientDescent.'+name;node=nodes['declaration:'+full]
 assert node['status']=='compiled' and node['statement_sha256']==h
 assert 'online-learning' in node['books'] and 'teaching:online-guessing-ogd' in node['chapters']
 checks.append(dict(name=full,native_hash=h,unique_canonical_node=True,books=node['books'],chapters=node['chapters'],url=node['url']))
full='BanditRL.OnlineGradientDescent.unitInterval';node=nodes['declaration:'+full]
definition_header=lean_declaration_header(Path('BanditRLProof/OnlineGuessingOGD.lean'),'unitInterval')
assert node['status']=='compiled' and node['statement_sha256']==hashlib.sha256(definition_header.encode()).hexdigest()
assert 'online-learning' in node['books'] and 'teaching:online-guessing-ogd' in node['chapters']
checks.append(dict(name=full,native_hash=node['statement_sha256'],unique_canonical_node=True,books=node['books'],chapters=node['chapters'],url=node['url'],definition_boundary='Native parser gives short def-where header; complete domain body/context frozen by unchanged old module proof tokens, not this short hash alone.'))
old=load('tmp/online-jensen-migration-site-v1/books/registry.json');old_ids={n['id'] for n in old['nodes']}
assert registry['identity']==old['identity'] and len(old_ids)==10806
assert all(n['id'] in nodes and nodes[n['id']]['url']==n['url'] for n in old['nodes'])
new_ids=set(nodes)-old_ids
expected={'declaration:BanditRL.OnlineGradientDescent.'+name for name in freeze['planned_new_headers']}
assert new_ids==expected and len(new_ids)==3
out=run/'registry-v1.json';assert not out.exists()
with out.open('w',encoding='utf-8',newline='\n') as f:
 json.dump(dict(status='passed',source_commit=manifest['source_commit'],source_dirty=False,lean_verified=True,registry_path=(site/'books/registry.json').as_posix(),registry_sha256=sha(site/'books/registry.json'),identity=registry['identity'],checks=checks,preserved_base_node_ids_and_urls=10806,new_registry_nodes=3,new_node_ids=sorted(new_ids)),f,indent=2);f.write('\n')
print('Matched12 frozen theorem headers and1 retained domain node;10806oldIDsURLs preserved/3 new actual comparison nodes.')
