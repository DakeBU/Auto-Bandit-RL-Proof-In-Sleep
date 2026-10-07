"""Same canonical declaration-only graph, zero new nodes, actual current source hashes."""
from common_v2 import *
site=Path('tmp/online-osd-public-site-v2');r=load(site/'books/registry.json');m=load(site/'site-manifest.json');old=load(RUN/'registry-base-snapshot-v1.json')
assert r['lean_verified'] and m['lean_verified'] and not m['source_dirty'] and r['source_commit']==m['source_commit']
nodes={n['id']:n for n in r['nodes']};base={n['id']:n for n in old['nodes']};assert len(base)==len(nodes)==10817 and set(base)==set(nodes) and r['identity']==old['identity']
assert all(nodes[i]['url']==n['url'] for i,n in base.items())
checks=[]
for n,h in load(CONTRACT/'native-statement-fingerprints-v1.json').items():
 node=nodes['declaration:'+PRE+n];assert node['status']=='compiled' and node['statement_sha256']==h
 assert 'online-learning' in node['books'] and 'teaching:online-osd' in node['chapters'];checks.append(dict(name=PRE+n,native_hash=h,url=node['url']))
x=next(a for a in load('website/content/readings.json')['readings'] if a['slug']==ROUTE)
assert [len(x[k]) for k in ['notation','teaching_route','source_theorems']]==[3,4,6] and len(x['proof_bridge']['steps'])==4
assert len([a for a in load('website/content/highlights.json')['highlights'] if a.get('chapter')==ROUTE])==15
html=(site/'modules/banditrlproof-onlinesubgradientdescent/index.html').read_text(encoding='utf-8');assert all(a['name'] in html for a in checks)
from html.parser import HTMLParser
class ReaderText(HTMLParser):
 def __init__(self):super().__init__();self.text=[];self.hrefs=[]
 def handle_data(self,data):self.text.append(data)
 def handle_starttag(self,tag,attrs):
  if tag=='a':self.hrefs.extend(v for k,v in attrs if k=='href')
parsed=ReaderText();parsed.feed((site/'chapters/online-osd/index.html').read_text(encoding='utf-8'))
for name in x['teaching_route']:
 assert name in ''.join(parsed.text);assert '../../'+nodes['declaration:'+name]['url'] in parsed.hrefs
write(RUN/'registry-v2.json',dict(status='passed',source_commit=m['source_commit'],source_dirty=False,lean_verified=True,identity=r['identity'],registry_path=(site/'books/registry.json').as_posix(),registry_sha256=sha(site/'books/registry.json'),checks=checks,preserved_base_node_IDs_and_URLs=10817,new_registry_declaration_nodes=0,total_registry_nodes=10817,canonical_shared_nodes_not_perBook_copies=True,highlight_links=15,curated_links=4,notation_entries=3,source_cards=6,proofbridge_steps=4))
print('All10817 old IDsURLs and15 unchanged sourcequalified native hashes; zero new nodes, six sourcecards.')
