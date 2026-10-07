from common_v2 import *
site=Path('tmp/online-convex-uncountability-site-v1');r=load(site/'books/registry.json');m=load(site/'site-manifest.json')
old=load('tmp/online-convex-nondifferentiability-site-v1/books/registry.json')
assert r['lean_verified'] and m['lean_verified'] and not m['source_dirty'] and r['source_commit']==m['source_commit']
nodes={n['id']:n for n in r['nodes']};base={n['id']:n for n in old['nodes']};assert len(base)==10815
assert set(base)<=set(nodes) and all(nodes[i]['url']==n['url'] for i,n in base.items()) and r['identity']==old['identity']
expected={'declaration:'+PRE+n for n in load(CONTRACT/'headers.json')};assert set(nodes)-set(base)==expected
checks=[]
for n,h in load(CONTRACT/'native-statement-fingerprints-v1.json').items():
 node=nodes['declaration:'+PRE+n];assert node['status']=='compiled' and node['statement_sha256']==h
 assert 'online-learning' in node['books'] and 'teaching:online-lipschitz' in node['chapters']
 checks.append(dict(name=PRE+n,native_hash=h,url=node['url'],unique_shared_canonical_node=True))
x=next(a for a in load('website/content/readings.json')['readings'] if a['slug']==ROUTE)
assert len(x['notation'])==3 and len(x['teaching_route'])==4 and len(x['source_theorems'])==4 and len(x['proof_bridge']['steps'])==5
before=load(RUN/'snapshots/before-website--content--readings.json.txt');prior=next(a for a in before['readings'] if a['slug']==ROUTE)
assert x['source_theorems'][:3]==prior['source_theorems'] and x['notation']==prior['notation']
assert len([a for a in load('website/content/highlights.json')['highlights'] if a.get('chapter')==ROUTE])==4
html=(site/'modules/banditrlproof-onlineconvexuncountability/index.html').read_text(encoding='utf-8');assert all(a['name'] in html for a in checks)
from html.parser import HTMLParser
class ReaderText(HTMLParser):
 def __init__(self):super().__init__();self.text=[];self.hrefs=[]
 def handle_data(self,data):self.text.append(data)
 def handle_starttag(self,tag,attrs):
  if tag=='a':self.hrefs.extend(v for k,v in attrs if k=='href')
route=(site/'chapters/online-lipschitz/index.html').read_text(encoding='utf-8')
parsed=ReaderText();parsed.feed(route)
assert PRE+'convex_uncountable_nondifferentiability' in ''.join(parsed.text)
assert '../../'+nodes['declaration:'+PRE+'convex_uncountable_nondifferentiability']['url'] in parsed.hrefs
write(RUN/'registry-v2.json',dict(status='passed',source_commit=m['source_commit'],source_dirty=False,lean_verified=True,identity=r['identity'],registry_path=(site/'books/registry.json').as_posix(),registry_sha256=sha(site/'books/registry.json'),checks=checks,preserved_base_node_IDs_and_URLs=10815,new_registry_declaration_nodes=2,total_registry_nodes=len(nodes),new_module_view_separate_from_decl_only_registry=True,canonical_shared_nodes_not_perBook_copies=True,highlight_links=4,curated_links=4,notation_entries=3,source_cards=4,proofbridge_steps=5,preserved_old_sourcecards=3))
print('All10815oldIDsURLs/two new compiled sourcequalified theorem nodes:',len(nodes),'sharedregistry; four cards/highlights/curated, three notes/five bridge steps.')
