"""Actual single shared registry, exactly four new proofs and retained old IDs/URLs."""
from common_v1 import *
headers();site=Path('tmp/online-guessing-osd-policy-site-v1');r=load(site/'books/registry.json');m=load(site/'site-manifest.json');old=load(RUN/'registry-base-snapshot-v1.json')
assert r['lean_verified'] and m['lean_verified'] and not m['source_dirty'] and r['source_commit']==m['source_commit']
nodes={n['id']:n for n in r['nodes']};base={n['id']:n for n in old['nodes']};PRE='BanditRL.OnlineGuessingSubgradientPolicy.';ROUTE='online-guessing-osd'
expected={'declaration:'+PRE+n for n in load(CONTRACT/'headers-v1.json')}
assert len(nodes)==10821 and len(base)==10817 and set(nodes)-set(base)==expected and set(base)<=set(nodes) and r['identity']==old['identity']
assert all(nodes[i]['url']==n['url'] for i,n in base.items())
checks=[]
for n in load(CONTRACT/'headers-v1.json'):
 h=load(RUN/'native-public-fences'/(n+'-full-v1.json'))['statement_hash'];node=nodes['declaration:'+PRE+n]
 assert node['status']=='compiled' and node['statement_sha256']==h
 assert 'online-learning' in node['books'] and 'teaching:'+ROUTE in node['chapters'];checks.append(dict(name=PRE+n,native_hash=h,url=node['url']))
x=next(a for a in load('website/content/readings.json')['readings'] if a['slug']==ROUTE)
assert [len(x[k]) for k in ['notation','teaching_route','source_theorems']]==[5,8,6] and len(x['proof_bridge']['steps'])==6
assert len([a for a in load('website/content/highlights.json')['highlights'] if a.get('chapter')==ROUTE])==16
html=(site/'modules/banditrlproof-onlineguessingsubgradientpolicy/index.html').read_text(encoding='utf-8');assert all(a['name'] in html for a in checks)
from html.parser import HTMLParser
class ReaderText(HTMLParser):
 def __init__(self):super().__init__();self.text=[];self.hrefs=[]
 def handle_data(self,data):self.text.append(data)
 def handle_starttag(self,tag,attrs):
  if tag=='a':self.hrefs.extend(v for k,v in attrs if k=='href')
parsed=ReaderText();parsed.feed((site/'chapters/online-guessing-osd/index.html').read_text(encoding='utf-8'))
for name in x['teaching_route']:
 assert name in ''.join(parsed.text);assert '../../'+nodes['declaration:'+name]['url'] in parsed.hrefs
write(RUN/'registry-v1.json',dict(status='passed',source_commit=m['source_commit'],source_dirty=False,lean_verified=True,identity=r['identity'],registry_path=(site/'books/registry.json').as_posix(),registry_sha256=sha(site/'books/registry.json'),checks=checks,preserved_base_node_IDs_and_URLs=10817,new_registry_nodes=4,total_registry_nodes=10821,canonical_shared_nodes_not_perBook_copies=True,highlight_links=16,curated_links=8,notation_entries=5,source_cards=6,proofbridge_steps=6))
print('All10817 old IDsURLs preserved; exactly4 new proofs /4 frozen native hashes in single10821 registry.')
