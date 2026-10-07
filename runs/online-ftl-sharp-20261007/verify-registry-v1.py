from common_v1 import *
from html.parser import HTMLParser
fixed(proving=True,integrated=True)
site=Path('tmp/online-ftl-sharp-site-v1');r=load(site/'books/registry.json');m=load(site/'site-manifest.json');old=load(RUN/'registry-base-snapshot-v1.json')
assert r['lean_verified'] and m['lean_verified'] and not m['source_dirty'] and r['source_commit']==m['source_commit']
nodes={n['id']:n for n in r['nodes']};base={n['id']:n for n in old['nodes']};expected={'declaration:'+PRE+n for n in load(CONTRACT/'new-public-headers-v1.json')}
assert len(nodes)==10823 and len(base)==10821 and set(nodes)-set(base)==expected and set(base)<=set(nodes) and r['identity']==old['identity']
assert all(nodes[i]['url']==n['url'] and nodes[i].get('statement_sha256')==n.get('statement_sha256') for i,n in base.items())
bindings={x['name']:x for x in load(RUN/'full-fence-bindings-v1.json')};new=[]
for key in expected:
 node=nodes[key];assert node['status']=='compiled' and node['statement_sha256']==bindings[key[len('declaration:'):]]['statement_hash']
 assert 'online-learning' in node['books'] and 'teaching:'+ROUTE in node['chapters'];new.append(dict(id=key,url=node['url'],statement_sha256=node['statement_sha256']))
x=next(a for a in load('website/content/readings.json')['readings'] if a['slug']==ROUTE)
assert len(x['source_theorems'])==6 and len(x['teaching_route'])==4
class ReaderText(HTMLParser):
 def __init__(self):super().__init__();self.text=[];self.hrefs=[]
 def handle_data(self,data):self.text.append(data)
 def handle_starttag(self,tag,attrs):
  if tag=='a':self.hrefs.extend(v for k,v in attrs if k=='href')
parsed=ReaderText();html=site/'chapters/online-foundations/index.html';parsed.feed(html.read_text(encoding='utf-8'));text=''.join(parsed.text)
for name in x['teaching_route']+[PRE+n for n in load(CONTRACT/'new-public-headers-v1.json')]:assert name in text and '../../'+nodes['declaration:'+name]['url'] in parsed.hrefs,name
for phrase in ['Only the first target','Positive horizon T','strict past','range(T-1)','9/4','general initial predictions','logarithmic lower-bound','Chapter 1 remains open']:assert phrase in text,phrase
module=site/'modules/banditrlproof-onlinelearningftl/index.html';q=ReaderText();q.feed(module.read_text(encoding='utf-8'));mt=''.join(q.text)
for name in load(CONTRACT/'new-public-headers-v1.json'):assert PRE+name in mt,name
assert '(hy :' in mt and '(T - 1)' in mt and '(hT : 0 < T)' in mt
write(RUN/'registry-v1.json',dict(status='passed',source_commit=m['source_commit'],source_dirty=False,lean_verified=True,registry_sha256=sha(site/'books/registry.json'),registry_path=(site/'books/registry.json').as_posix(),identity=r['identity'],preserved_base_node_IDs_URLs_and_hashes=10821,new_registry_nodes=2,total_registry_nodes=10823,new_nodes=new,source_cards=6,updated_source_cards=1,new_source_cards=2,new_public_notes=2,curated_links_preserved=4,source_route_HTML_sha256=sha(html),module_HTML_sha256=sha(module),same_shared_registry=True,new_named_validation_proofs=6,new_public_math=2,chapter_complete=False,goal_complete=False))
print('Same10821 IDsURLs/nativehashes plus2new source proofnodes, shared total10823 PASS.')
