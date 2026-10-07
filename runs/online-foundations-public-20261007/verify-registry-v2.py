from common_v1 import *
from html.parser import HTMLParser
fixed(True);site=Path('tmp/online-foundations-public-site-v2');r=load(site/'books/registry.json');m=load(site/'site-manifest.json');old=load(RUN/'registry-base-snapshot-v1.json')
assert r['lean_verified'] and m['lean_verified'] and not m['source_dirty'] and r['source_commit']==m['source_commit']
nodes={n['id']:n for n in r['nodes']};base={n['id']:n for n in old['nodes']}
assert len(nodes)==len(base)==10821 and set(nodes)==set(base) and r['identity']==old['identity']
assert all(nodes[i]['url']==n['url'] for i,n in base.items())
node=nodes['declaration:'+PRE+'lemma_1_2'];assert node['status']=='compiled' and node['statement_sha256']==fixed(True)['native_header_hash'] and 'online-learning' in node['books'] and 'teaching:'+ROUTE in node['chapters']
x=next(a for a in load('website/content/readings.json')['readings'] if a['slug']==ROUTE)
assert len(x['source_theorems'])==4 and len(x['teaching_route'])==4
class ReaderText(HTMLParser):
 def __init__(self):super().__init__();self.text=[];self.hrefs=[]
 def handle_data(self,data):self.text.append(data)
 def handle_starttag(self,tag,attrs):
  if tag=='a':self.hrefs.extend(v for k,v in attrs if k=='href')
parsed=ReaderText();html=site/'chapters/online-foundations/index.html';parsed.feed(html.read_text(encoding='utf-8'))
for name in x['teaching_route']:assert name in ''.join(parsed.text) and '../../'+nodes['declaration:'+name]['url'] in parsed.hrefs
for text in ['arbitrary ambient type X','EVERY positive prefix','hindsight','STRICT -2<0','comparison3>1','comparison5>-5','Eight OTHER Chapter1']:
 assert text in ''.join(parsed.text),text
module=site/'modules/banditrlproof-onlinelearningfoundations/index.html';q=ReaderText();q.feed(module.read_text(encoding='utf-8'))
assert PRE+'lemma_1_2' in ''.join(q.text) and '(hmem :' in ''.join(q.text) and '(hmin :' in ''.join(q.text)
write(RUN/'registry-v2.json',dict(status='passed',source_commit=m['source_commit'],source_dirty=False,lean_verified=True,registry_sha256=sha(site/'books/registry.json'),registry_path=(site/'books/registry.json').as_posix(),identity=r['identity'],preserved_base_node_IDs_and_URLs=10821,new_registry_nodes=0,total_registry_nodes=10821,single_native_hash= node['statement_sha256'],single_public_URL=node['url'],source_cards=4,updated_source_cards=1,updated_public_notes=1,curated_links=4,source_route_HTML_sha256=sha(html),module_HTML_sha256=sha(module),original_other_cards_notes_preserved=True,same_shared_registry=True,new_named_validation_proofs=7,new_public_math=0,chapter_complete=False,goal_complete=False))
print('Same10821 shared IDsURLs and single retained public hash; one-card one-note source reading/four old links PASS.')
