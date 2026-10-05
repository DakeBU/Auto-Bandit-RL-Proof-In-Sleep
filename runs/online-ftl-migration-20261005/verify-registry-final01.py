"""Match each canonical source-qualified node to its actual native header."""
from pathlib import Path
import hashlib, json, re, sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header

run=Path(__file__).parent
path=Path('tmp/online-ftl-migration-site-final01/books/registry.json')
raw=path.read_bytes();registry=json.loads(raw)
public=Path('BanditRLProof/OnlineFTLFailure.lean')
ns='BanditRL.OnlineLearning.'
names=re.findall(r'^(?:noncomputable )?(?:theorem|def|abbrev) (\w+)',public.read_text(encoding='utf-8'),re.M)
assert len(names)==10
checks=[]
for name in names:
    full=ns+name
    nodes=[n for n in registry['nodes'] if n['id']=='declaration:'+full]
    assert len(nodes)==1,(full,len(nodes))
    node=nodes[0]
    header=lean_declaration_header(public,name)
    fingerprint=hashlib.sha256(header.encode('utf-8')).hexdigest()
    assert fingerprint==node['statement_sha256'],(full,fingerprint,node['statement_sha256'])
    assert node['status']=='compiled',node
    assert 'online-learning' in node['books'],node
    assert 'teaching:online-ftl-failure' in node['chapters'],node
    checks.append({'name':full,'native_hash':fingerprint,'unique_canonical_node':True,
        'status':node['status'],'books':node['books'],'chapters':node['chapters'],'matched':True})
assert registry['lean_verified'] is True
manifest=json.loads(Path('tmp/online-ftl-migration-site-final01/site-manifest.json').read_text(encoding='utf-8'))
assert manifest['source_dirty'] is False
assert manifest['source_commit']==registry['source_commit']
old=json.loads(Path('tmp/online-ogd-migration-site-final02/books/registry.json').read_text(encoding='utf-8'))
newnodes={n['id']:n for n in registry['nodes']}
assert all(n['id'] in newnodes and newnodes[n['id']]['url']==n['url'] for n in old['nodes'])
assert registry['identity']==old['identity']
result={'status':'passed','registry_path':str(path),'registry_sha256':hashlib.sha256(raw).hexdigest(),
 'source_commit':registry['source_commit'],'lean_verified':registry['lean_verified'],
 'identity':registry['identity'],'preserved_base_node_ids_and_urls':len(old['nodes']),'source_dirty':manifest['source_dirty'],'checks':checks}
with (run/'registry-final01.json').open('w',encoding='utf-8',newline='\n') as f:
    json.dump(result,f,ensure_ascii=False,indent=2);f.write('\n')
print('matched',len(checks),'unique shared canonical nodes and actual native statement hashes')
