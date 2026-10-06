"""Verify all retained differentiability nodes and preserve the entire shared registry."""
from pathlib import Path
import hashlib,json,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header
run=Path(__file__).parent;site=Path('tmp/online-subgradient-differentiability-migration-site-v1')
load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'));sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
r=load(site/'books/registry.json');m=load(site/'site-manifest.json');old=load('tmp/online-subgradient-interior-migration-site-v1/books/registry.json')
assert r['lean_verified'] is True and m['lean_verified'] is True and m['source_dirty'] is False and r['source_commit']==m['source_commit']
nodes={n['id']:n for n in r['nodes']};oldnodes={n['id']:n for n in old['nodes']}
assert len(nodes)==len(r['nodes'])==len(oldnodes)==10811 and set(nodes)==set(oldnodes) and r['identity']==old['identity']
assert all(nodes[i]['url']==n['url'] for i,n in oldnodes.items())
freeze=load(run/'draft-freeze-v1.json');module=Path('BanditRLProof/OnlineSubgradientDifferentiability.lean');pre='BanditRL.OnlineConvex.';checks=[]
for name,h in freeze['headers'].items():
 full=pre+name;node=nodes['declaration:'+full]
 assert node['status']=='compiled' and node['statement_sha256']==h
 assert 'online-learning' in node['books'] and 'teaching:online-subgradient-differentiability' in node['chapters']
 assert hashlib.sha256(lean_declaration_header(module,name).encode()).hexdigest()==h
 checks.append(dict(name=full,native_hash=h,url=node['url'],unique_canonical_node=True,new_canonical_mathproof=False,kind='theorem'))
full=pre+'SourceDifferentiableAt';node=nodes['declaration:'+full]
assert node['status']=='compiled' and node['statement_sha256']==oldnodes[node['id']]['statement_sha256']
assert 'online-learning' in node['books'] and 'teaching:online-subgradient-differentiability' in node['chapters']
checks.append(dict(name=full,native_hash=node['statement_sha256'],url=node['url'],unique_canonical_node=True,new_canonical_mathproof=False,kind='definition',boundary='Complete retained real-germ definition, not another proof or source theorem.'))
reader=next(x for x in load('website/content/readings.json')['readings'] if x['slug']=='online-subgradient-differentiability')
assert len(reader['teaching_route'])==4 and reader['teaching_route']==load(run/'reader-route-site-repair-v2.json')['newroute']
assert set(reader['teaching_route'])<={c['name'] for c in checks}
module_html=(site/'modules/banditrlproof-onlinesubgradientdifferentiability/index.html').read_text(encoding='utf-8')
assert all(c['name'] in module_html for c in checks)
assert module.read_bytes().endswith((run/'original-OnlineSubgradientDifferentiability.lean.txt').read_bytes())
assert sha(module)==load(run/'public-comment-qualification-v1.json')['qualified_sha256']
p=run/'registry-v1.json';assert not p.exists()
p.write_bytes((json.dumps(dict(status='passed',source_commit=m['source_commit'],source_dirty=False,lean_verified=True,registry_path=(site/'books/registry.json').as_posix(),registry_sha256=sha(site/'books/registry.json'),identity=r['identity'],checks=checks,preserved_base_node_ids_and_urls=10811,new_registry_nodes=0,total_registry_nodes=10811,canonical_shared_nodes_not_perBookcopies=True),indent=2)+'\n').encode('utf-8'))
print('Twelve retained source-qualified links; all10811oldIDsURLs preserved, zero new registry mathematical nodes.')
