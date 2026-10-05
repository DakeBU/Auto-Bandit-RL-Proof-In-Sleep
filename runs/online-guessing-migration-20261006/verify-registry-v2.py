"""Verify twelve theorem headers, the retained domain node, and three new nodes."""
from pathlib import Path
import hashlib,json,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header, _strip_lean_comments
from website.scripts.build_site import scan_module
import re,subprocess
run=Path(__file__).parent;site=Path('tmp/online-guessing-migration-site-v1')
load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'))
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert load(run/'registry-v1-01-exit.json')['exit_code']==1
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
source_node=next(d for d in scan_module(Path('BanditRLProof/OnlineGuessingOGD.lean').resolve())['declarations'] if d['full_name']==full)
assert node['status']=='compiled' and node['statement_sha256']==hashlib.sha256(source_node['statement'].encode()).hexdigest()
old_module=(run/'original-OnlineGuessingOGD.lean.txt').read_text(encoding='utf-8')
tokens=lambda text:re.sub(r'\s+',' ',_strip_lean_comments(text)).strip()
assert tokens(Path('BanditRLProof/OnlineGuessingOGD.lean').read_text(encoding='utf-8'))==tokens(old_module)
assert 'online-learning' in node['books'] and 'teaching:online-guessing-ogd' in node['chapters']
checks.append(dict(name=full,native_hash=node['statement_sha256'],unique_canonical_node=True,books=node['books'],chapters=node['chapters'],url=node['url'],site_parser_statement=source_node['statement'],native_parser_statement=definition_header,native_parser_sha256=hashlib.sha256(definition_header.encode()).hexdigest(),definition_boundary='Two parsers produce different short headers for def-where; actual site parser hash verified, complete domain body/context frozen by unchanged old module tokens. Neither short hash alone is complete semantic contract.'))
old=load('tmp/online-jensen-migration-site-v1/books/registry.json');old_ids={n['id'] for n in old['nodes']}
assert registry['identity']==old['identity'] and len(old_ids)==10806
assert all(n['id'] in nodes and nodes[n['id']]['url']==n['url'] for n in old['nodes'])
old_domain=next(n for n in old['nodes'] if n['id']=='declaration:'+full);assert old_domain['statement_sha256']==node['statement_sha256']
new_ids=set(nodes)-old_ids
expected={'declaration:BanditRL.OnlineGradientDescent.'+name for name in freeze['planned_new_headers']}
assert new_ids==expected and len(new_ids)==3
out=run/'registry-v2.json';assert not out.exists()
with out.open('w',encoding='utf-8',newline='\n') as f:
 json.dump(dict(status='passed',source_commit=manifest['source_commit'],source_dirty=False,lean_verified=True,registry_path=(site/'books/registry.json').as_posix(),registry_sha256=sha(site/'books/registry.json'),identity=registry['identity'],checks=checks,preserved_base_node_ids_and_urls=10806,new_registry_nodes=3,new_node_ids=sorted(new_ids)),f,indent=2);f.write('\n')
print('Matched12 frozen theorem headers and1 retained domain node;10806oldIDsURLs preserved/3 new actual comparison nodes.')
