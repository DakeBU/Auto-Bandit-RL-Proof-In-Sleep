"""Verify two canonical new proof nodes while preserving all shared registry identities."""
from pathlib import Path
import hashlib,json,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header
run=Path(__file__).parent;site=Path('tmp/online-subgradient-interior-migration-site-v1');load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'));sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
r=load(site/'books/registry.json');m=load(site/'site-manifest.json');old=load('tmp/online-subgradient-basic-migration-site-v1/books/registry.json')
assert r['lean_verified'] is True and m['lean_verified'] is True and m['source_dirty'] is False and r['source_commit']==m['source_commit']
nodes={n['id']:n for n in r['nodes']};oldnodes={n['id']:n for n in old['nodes']};assert len(oldnodes)==10809 and len(nodes)==len(r['nodes'])==10811 and r['identity']==old['identity']
pre='BanditRL.OnlineConvex.';newnames=[pre+'affine_support_of_relative_domain_interior',pre+'subgradient_exists_of_relative_domain_interior'];newids={'declaration:'+n for n in newnames};assert set(nodes)-set(oldnodes)==newids and set(oldnodes)<=set(nodes)
assert all(nodes[i]['url']==n['url'] for i,n in oldnodes.items())
freeze=load(run/'draft-freeze-v1.json');module=Path('BanditRLProof/OnlineSubgradientInterior.lean');checks=[]
for name,h in freeze['headers'].items():
 full=pre+name;node=nodes['declaration:'+full];assert node['status']=='compiled' and node['statement_sha256']==h and node['kind']=='theorem',full
 assert 'online-learning' in node['books'] and 'teaching:online-subgradient-interior' in node['chapters'],full
 assert hashlib.sha256(lean_declaration_header(module,name).encode()).hexdigest()==h
 checks.append(dict(name=full,native_hash=h,unique_canonical_node=True,new_canonical_mathproof=full in newnames,books=node['books'],chapters=node['chapters'],url=node['url'],kind='theorem'))
full=pre+'affine_support_of_domain_interior';node=nodes['declaration:'+full];oldnode=oldnodes['declaration:'+full];assert node['statement_sha256']==oldnode['statement_sha256'] and node['url']==oldnode['url'] and 'online-learning' in node['books'] and 'teaching:online-subgradient-interior' in node['chapters'];checks.append(dict(name=full,native_hash=node['statement_sha256'],unique_canonical_node=True,new_canonical_mathproof=False,books=node['books'],chapters=node['chapters'],url=node['url'],kind='theorem',boundary='Accepted shared contact dependency reused; not a new proof/source theorem.'))
assert len(checks)==4 and (run/'original-OnlineSubgradientInterior.lean.txt').read_bytes() in module.read_bytes()
assert sha(module)==load(run/'public-actual-bindings-v1.json')['module_sha256']
p=run/'registry-v1.json';assert not p.exists();p.write_text(json.dumps(dict(status='passed',source_commit=m['source_commit'],source_dirty=False,lean_verified=True,registry_path=(site/'books/registry.json').as_posix(),registry_sha256=sha(site/'books/registry.json'),identity=r['identity'],checks=checks,preserved_base_node_ids_and_urls=10809,new_registry_nodes=2,new_node_ids=sorted(newids),total_registry_nodes=10811,canonical_shared_nodes_not_perBookcopies=True),indent=2)+'\n',encoding='utf-8')
print('Four source-qualified canonical links; all10809oldIDsURLs preserved, exactly2new mathproofnodes, same shared registry.')
