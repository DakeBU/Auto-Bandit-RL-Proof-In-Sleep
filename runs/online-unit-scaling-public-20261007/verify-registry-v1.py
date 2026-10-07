from common_v1 import *
fixed(True);site=Path('tmp/online-unit-scaling-public-site-v1');r=load(site/'books/registry.json');m=load(site/'site-manifest.json');old=load(RUN/'registry-base-snapshot-v1.json')
assert r['lean_verified'] and m['lean_verified'] and not m['source_dirty'] and r['source_commit']==m['source_commit']
nodes={n['id']:n for n in r['nodes']};base={n['id']:n for n in old['nodes']}
assert len(nodes)==len(base)==10821 and set(nodes)==set(base) and r['identity']==old['identity'];assert all(nodes[i]['url']==n['url'] for i,n in base.items())
checks=[]
for n,h in load(CONTRACT/'native-statement-fingerprints-v1.json').items():
 node=nodes['declaration:'+PRE+n];assert node['status']=='compiled' and node['statement_sha256']==h and 'online-learning' in node['books'] and 'teaching:'+ROUTE in node['chapters'];checks.append(dict(name=PRE+n,native_hash=h,url=node['url']))
x=next(a for a in load('website/content/readings.json')['readings'] if a['slug']==ROUTE);assert [len(x[k]) for k in ['notation','teaching_route','source_theorems']]==[3,4,2] and len(x['proof_bridge']['steps'])==5
hi=[a for a in load('website/content/highlights.json')['highlights'] if a.get('chapter')==ROUTE];assert len(hi)==22
html=(site/'modules/banditrlproof-onlineunitscaling/index.html').read_text(encoding='utf-8');assert all(a['name'] in html for a in checks)
from html.parser import HTMLParser
class ReaderText(HTMLParser):
 def __init__(self):super().__init__();self.text=[];self.hrefs=[]
 def handle_data(self,data):self.text.append(data)
 def handle_starttag(self,tag,attrs):
  if tag=='a':self.hrefs.extend(v for k,v in attrs if k=='href')
parsed=ReaderText();parsed.feed((site/'chapters/online-unit-scaling/index.html').read_text(encoding='utf-8'))
for name in x['teaching_route']+[a['full_name'] for a in hi]:assert name in ''.join(parsed.text) and '../../'+nodes['declaration:'+name]['url'] in parsed.hrefs
write(RUN/'registry-v1.json',dict(status='passed',source_commit=m['source_commit'],source_dirty=False,lean_verified=True,identity=r['identity'],registry_path=(site/'books/registry.json').as_posix(),registry_sha256=sha(site/'books/registry.json'),checks=checks,preserved_base_node_IDs_and_URLs=10821,new_registry_nodes=0,total_registry_nodes=10821,source_cards=2,highlight_links=22,curated_links=4,notation_entries=3,proofbridge_steps=5,same_shared_registry=True))
print('Same10821 shared IDsURLs, zero new nodes,22frozen native hashes,2cards22notes4curatedlinks PASS.')
