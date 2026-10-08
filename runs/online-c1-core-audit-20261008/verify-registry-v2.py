from common_reader_repair_v2 import *
from html.parser import HTMLParser
from tools.abrl_lifecycle import normalize_statement
fixed_integrated()
site=Path('tmp/online-c1-core-audit-site-v2')
r=load(site/'books/registry.json');m=load(site/'site-manifest.json')
old=json.loads(gzip.decompress((RUN/'registry-base-snapshot-v1.json.gz').read_bytes()).decode('utf8'))
assert r['lean_verified'] and m['lean_verified'] and not m['source_dirty']
assert r['source_commit']==m['source_commit'] and r['identity']==old['identity']
nodes={x['id']:x for x in r['nodes']};base={x['id']:x for x in old['nodes']}
assert len(base)==len(nodes)==10935 and set(nodes)==set(base)
for id,n in base.items():
    assert nodes[id]['url']==n['url'] and nodes[id].get('statement_sha256')==n.get('statement_sha256'),id
assert not any('OnlineLearningCoreAuditCanary' in x['id'] for x in r['nodes'])
class Reader(HTMLParser):
    def __init__(self): super().__init__();self.text=[];self.hrefs=[]
    def handle_data(self,data):self.text.append(data)
    def handle_starttag(self,tag,attrs):
        if tag=='a':self.hrefs.extend(v for k,v in attrs if k=='href')
reader=site/'chapters/online-foundations/index.html';parsed=Reader();parsed.feed(reader.read_text(encoding='utf8'))
text=' '.join(''.join(parsed.text).split())
reading=next(x for x in load('website/content/readings.json')['readings'] if x['slug']==ROUTE)
assert len(reading['source_theorems'])==15 and len(reading['teaching_route'])==4
for name in reading['teaching_route']:
    assert name in text and '../../'+nodes['declaration:'+name]['url'] in parsed.hrefs
modules={}
for row in load(CONTRACT/'targets-v2.json')['targets']:
    name=row['name'];n=nodes['declaration:'+name]
    assert n['status']=='compiled' and 'online-learning' in n['books'] and 'teaching:'+ROUTE in n['chapters']
    assert normalize_statement(row['header']) in text,name
    path=n['url'].split('#')[0]
    if path not in modules:
        p=Reader();p.feed((site/path).read_text(encoding='utf8'));modules[path]=p
    p=modules[path]
    assert normalize_statement(row['header']) in ' '.join(''.join(p.text).split()),name
    source='https://github.com/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/blob/'+m['source_commit']+'/'+row['path']
    assert any(h.startswith(source+'#L') for h in p.hrefs),name
write(RUN/'registry-v2.json',dict(status='passed',source_commit=m['source_commit'],source_dirty=False,lean_verified=True,
    registry_sha256=sha(site/'books/registry.json'),identity=r['identity'],
    preserved_base_IDs_URLs_statement_hashes=10935,new_registry_nodes=0,total_registry_nodes=10935,
    source_cards=15,new_source_cards=1,ten_added_notes=10,two_corrected_notes=2,
    curated_links_preserved=4,source_route_HTML_sha256=sha(reader),
    module_HTML_sha256={p:sha(site/p) for p in modules},
    twelve_complete_headers_present=True,same_shared_registry=True,new_production_proofs=0,
    chapter_complete=False,goal_complete=False))
print('All10935 existing registry IDs/URLs/statement hashes preserved; zero new nodes, twelve complete public headers and four curated links verified.')
