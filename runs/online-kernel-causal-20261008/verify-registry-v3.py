from common_body_v2 import *
from tools.abrl_lifecycle import normalize_statement
from html.parser import HTMLParser
import gzip

fixed_integrated()
site = ROOT/'tmp/online-kernel-causal-site-v1'
r = load(site/'books/registry.json')
m = load(site/'site-manifest.json')
old = json.loads(gzip.decompress((RUN/'registry-base-snapshot-v1.json.gz').read_bytes()).decode('utf8'))
assert r['lean_verified'] and m['lean_verified'] and not m['source_dirty']
assert r['source_commit'] == m['source_commit'] and r['identity'] == old['identity']
nodes = {x['id']:x for x in r['nodes']}
base = {x['id']:x for x in old['nodes']}
assert set(base) <= set(nodes)
for id,n in base.items():
    assert nodes[id] == n, id
targets = load(CONTRACT/'targets-v2.json')['targets']
new = set(nodes)-set(base)
required = {'declaration:'+t['name'] for t in targets}
support = load(RUN/'registry-expectation-repair-proposal-v1.json')['support_records']
assert new == required | {x['id'] for x in support}, new
for x in support: assert nodes[x['id']] == x
assert len(required) == 5 and len(support) == 12
assert not any('OnlineGuessingKernelCausalCanary' in n for n in nodes)
class Reader(HTMLParser):
    def __init__(self):
        super().__init__()
        self.text = []
        self.hrefs = []
    def handle_data(self,data):
        self.text.append(data)
    def handle_starttag(self,tag,attrs):
        if tag == 'a':
            self.hrefs.extend(v for k,v in attrs if k == 'href')
reader = site/'chapters/online-foundations/index.html'
p = Reader()
p.feed(reader.read_text(encoding='utf8'))
text = ' '.join(''.join(p.text).split())
reading = next(x for x in load(ROOT/'website/content/readings.json')['readings'] if x['slug'] == ROUTE)
old_reading = next(x for x in json.loads(baseline('website/content/readings.json').decode('utf8'))['readings'] if x['slug'] == ROUTE)
assert reading['source_theorems'] == old_reading['source_theorems']+[load(RUN/'reader-proposal-v1.json')['card']]
assert reading['teaching_route'] == old_reading['teaching_route']
for name in reading['teaching_route']:
    assert name in text and '../../'+nodes['declaration:'+name]['url'] in p.hrefs
modules = {}
for t in targets:
    n = nodes['declaration:'+t['name']]
    assert n['status'] == 'compiled' and 'online-learning' in n['books'] and 'teaching:'+ROUTE in n['chapters']
    assert normalize_statement(t['header']) in text, t['name']
    path = n['url'].split('#')[0]
    if path not in modules:
        q = Reader()
        q.feed((site/path).read_text(encoding='utf8'))
        modules[path] = q
    q = modules[path]
    assert normalize_statement(t['header']) in ' '.join(''.join(q.text).split()), t['name']
    source = 'https://github.com/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/blob/'+m['source_commit']+'/'+PUBLIC.relative_to(ROOT).as_posix()
    assert any(h.startswith(source+'#L') for h in q.hrefs), t['name']
write(RUN/'registry-v2.json',dict(status='passed',source_commit=m['source_commit'],source_dirty=False,lean_verified=True,
    registry_sha256=sha(site/'books/registry.json'),identity=r['identity'],
    preserved_complete_base_node_records=len(base),preserved_base_IDs_URLs_statement_hashes=len(base),
    new_registry_nodes=len(new),new_registry_IDs=sorted(new),new_public_declarations=len(required),support_registry_nodes=len(support),support_registry_IDs=[x['id'] for x in support],total_registry_nodes=len(nodes),
    old_source_cards_preserved=len(old_reading['source_theorems']),source_cards=len(reading['source_theorems']),
    new_source_cards=1,new_notes=5,curated_links_preserved=len(reading['teaching_route']),source_route_HTML_sha256=sha(reader),
    module_HTML_sha256={x:sha(site/x) for x in modules},five_complete_headers_present=True,
    same_shared_registry=True,chapter_complete=False,goal_complete=False))
print('Actual shared registry',len(base),'complete old nodes preserved;',len(new),'new module nodes: 5 terminal theorems and12 supporting definitions/private helpers.',flush=True)
