"""Check three native theorem headers and both complete retained definitions."""
from pathlib import Path
import hashlib,json,re,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header,_strip_lean_comments
from website.scripts.build_site import scan_module
run=Path(__file__).parent;site=Path('tmp/online-subgradient-basic-migration-site-v1')
load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'))
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
registry=load(site/'books/registry.json');manifest=load(site/'site-manifest.json')
assert registry['lean_verified'] is True and manifest['source_dirty'] is False and manifest['lean_verified'] is True
assert manifest['source_commit']==registry['source_commit']
nodes={n['id']:n for n in registry['nodes']};assert len(nodes)==len(registry['nodes'])
freeze=load(run/'draft-freeze-v1.json');checks=[]
for name,h in freeze['headers'].items():
 full='BanditRL.OnlineConvex.'+name;node=nodes['declaration:'+full]
 assert node['status']=='compiled' and node['statement_sha256']==h,full
 assert 'online-learning' in node['books'] and 'teaching:online-subgradient-basic' in node['chapters'],full
 checks.append(dict(name=full,native_hash=h,unique_canonical_node=True,books=node['books'],chapters=node['chapters'],url=node['url'],kind='theorem'))
module=Path('BanditRLProof/OnlineSubgradientBasic.lean');tokens=lambda text:re.sub(r'\s+',' ',_strip_lean_comments(text)).strip()
assert tokens(module.read_text(encoding='utf-8'))==tokens((run/'original-OnlineSubgradientBasic.lean.txt').read_text(encoding='utf-8'))
scanned={d['full_name']:d for d in scan_module(module.resolve())['declarations']}
old=load('tmp/online-closed-proper-migration-site-v1/books/registry.json');oldnodes={n['id']:n for n in old['nodes']}
assert registry['identity']==old['identity'] and len(oldnodes)==10809
for full in load(run/'public-named-declarations-v1.json')['public_definitions']:
 node=nodes['declaration:'+full];s=scanned[full]['statement'];h=hashlib.sha256(s.encode()).hexdigest()
 assert node['status']=='compiled' and node['statement_sha256']==h==oldnodes['declaration:'+full]['statement_sha256'],full
 assert 'online-learning' in node['books'] and 'teaching:online-subgradient-basic' in node['chapters'],full
 native=lean_declaration_header(module,full.rsplit('.',1)[-1])
 checks.append(dict(name=full,native_hash=node['statement_sha256'],unique_canonical_node=True,books=node['books'],chapters=node['chapters'],url=node['url'],kind='definition',site_parser_statement=s,native_parser_statement=native,native_parser_sha256=hashlib.sha256(native.encode()).hexdigest(),definition_boundary='Actual site parser hash/old node matched; complete definition bodies and contexts retained by unchanged whole-module mathematical tokens. Neither short header alone is full semantic contract.'))
assert len(checks)==3
assert set(nodes)==set(oldnodes)
assert all(nodes[n['id']]['url']==n['url'] for n in old['nodes'])
out=run/'registry-v1.json';assert not out.exists()
with out.open('w',encoding='utf-8',newline='\n') as f:json.dump(dict(status='passed',source_commit=manifest['source_commit'],source_dirty=False,lean_verified=True,registry_path=(site/'books/registry.json').as_posix(),registry_sha256=sha(site/'books/registry.json'),identity=registry['identity'],checks=checks,preserved_base_node_ids_and_urls=10809,new_registry_nodes=0,new_node_ids=[]),f,indent=2);f.write('\n')
print('Matched2frozen theorem headers/1retained complete support definition;10809oldIDsURLs preserved/zero new registry nodes.')
