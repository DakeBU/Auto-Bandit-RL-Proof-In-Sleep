from common_v1 import *
from html.parser import HTMLParser
fixed(integrated=True)
site=Path('tmp/online-regret-domains-site-v1');r=load(site/'books/registry.json');m=load(site/'site-manifest.json');old=load(RUN/'registry-base-snapshot-v1.json')
assert r['lean_verified'] and m['lean_verified'] and not m['source_dirty'] and r['source_commit']==m['source_commit']
nodes={n['id']:n for n in r['nodes']};base={n['id']:n for n in old['nodes']}
assert len(nodes)==len(base)==10835 and set(nodes)==set(base) and r['identity']==old['identity']
assert all(nodes[i]['url']==n['url'] and nodes[i].get('statement_sha256')==n.get('statement_sha256') for i,n in base.items())
bindings={x['name']:x for x in load(RUN/'full-fence-bindings-v1.json')}
for n in load(CONTRACT/'existing-public-headers-v1.json'):
 node=nodes['declaration:'+PRE+n];assert node['statement_sha256']==bindings[PRE+n]['statement_hash'] and node['status']=='compiled'
 assert 'online-learning' in node['books'] and 'teaching:online-foundations' in node['chapters']
assert not any(TEST in n['id'] for n in r['nodes'])
class ReaderText(HTMLParser):
 def __init__(self):super().__init__();self.text=[];self.hrefs=[]
 def handle_data(self,data):self.text.append(data)
 def handle_starttag(self,tag,attrs):
  if tag=='a':self.hrefs.extend(v for k,v in attrs if k=='href')
reader=site/'chapters/online-foundations/index.html';parsed=ReaderText();parsed.feed(reader.read_text(encoding='utf-8'));text=''.join(parsed.text)
reading=next(x for x in load('website/content/readings.json')['readings'] if x['slug']==ROUTE)
assert len(reading['source_theorems'])==8 and len(reading['teaching_route'])==4
for n in reading['teaching_route']+[PRE+n for n in load(CONTRACT/'existing-public-headers-v1.json')]:assert n in text and '../../'+nodes['declaration:'+n]['url'] in parsed.hrefs,n
for phrase in ['Losses are defined on W','predictions belong to W','fixed comparators belong to V','Footnote1','ordinary limit existence','threshold may depend on u and epsilon','V-only loss','loss_t(x)=-x','regret -4 against0 and -2 against1','tests, not source results','Chapter 1 remains open']:assert phrase in text,phrase
module=site/'modules/banditrlproof-onlinelearningregret/index.html';parsed=ReaderText();parsed.feed(module.read_text(encoding='utf-8'));mt=''.join(parsed.text)
for n in ['comparatorRegret','NoRegret',*load(CONTRACT/'existing-public-headers-v1.json')]:assert PRE+n in mt,n
for phrase in ['(hb : ∀ u ∈ V','(hl : ∀ u ∈ V']:
 assert phrase in mt,phrase
# Catalogue exposes exact statement plus source link; teaching disclosure
# exposes the complete exact proof. Check the complete bodies on that page.
source=PUBLIC.read_text(encoding='utf-8')
for n in load(CONTRACT/'existing-public-headers-v1.json'):
 start=source.index('theorem '+n+' ')
 ends=[j for marker in ['\n/--','\nend BanditRL.OnlineLearning'] for j in [source.find(marker,start)] if j>=0]
 segment=source[start:min(ends)].strip()
 assert ' := by' in segment and ' '.join(segment.split()) in ' '.join(text.split()),n
for phrase in ['Finset.sum_sub_distrib','bound u T < ε','tendsto_order']:
 assert phrase in text,phrase
write(RUN/'registry-v2.json',dict(status='passed',source_commit=m['source_commit'],source_dirty=False,lean_verified=True,registry_sha256=sha(site/'books/registry.json'),registry_path=(site/'books/registry.json').as_posix(),identity=r['identity'],preserved_base_node_IDs_URLs_and_hashes=10835,new_registry_nodes=0,total_registry_nodes=10835,source_cards=8,new_source_cards=1,new_public_notes=2,curated_links_preserved=4,source_route_HTML_sha256=sha(reader),module_HTML_sha256=sha(module),same_shared_registry=True,named_validation_proofs=8,new_production_math=0,module_catalogue_exact_types_present=True,reader_disclosure_full_exact_proofs_present=True,chapter_complete=False,goal_complete=False))
print('All10835 existing shared IDsURLs/source hashes preserved;0newproduction nodes; source reader and module complete.')
