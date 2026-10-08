from common_integrated_v2 import *
from html.parser import HTMLParser

fixed_integrated()
site = Path('tmp/online-iid-success-site-v1')
r, m, old = load(site/'books/registry.json'), load(site/'site-manifest.json'), load(RUN/'registry-base-snapshot-v1.json')
assert r['lean_verified'] and m['lean_verified'] and not m['source_dirty']
assert r['source_commit'] == m['source_commit']
nodes, base = {x['id']:x for x in r['nodes']}, {x['id']:x for x in old['nodes']}
assert len(base) == 10931 and r['identity'] == old['identity']
assert all(i in nodes and nodes[i]['url'] == n['url'] and nodes[i].get('statement_sha256') == n.get('statement_sha256') for i,n in base.items())
production = load(MANIFEST)['declarations']
assert len(production) == 4 and len(nodes) == 10935
assert set(nodes)-set(base) == {'declaration:'+n for n in production}
assert not any('OnlineGuessingIIDSuccessCanary' in n['id'] for n in r['nodes'])
for name in production:
    n = nodes['declaration:'+name]
    assert n['status'] == 'compiled' and 'online-learning' in n['books'] and 'teaching:online-foundations' in n['chapters'], name

class Reader(HTMLParser):
    def __init__(self): super().__init__(); self.text=[]; self.hrefs=[]
    def handle_data(self, data): self.text.append(data)
    def handle_starttag(self, tag, attrs):
        if tag == 'a': self.hrefs.extend(v for k,v in attrs if k == 'href')

reader = site/'chapters/online-foundations/index.html'
parsed = Reader(); parsed.feed(reader.read_text(encoding='utf8')); text=''.join(parsed.text)
reading = next(x for x in load('website/content/readings.json')['readings'] if x['slug'] == ROUTE)
assert len(reading['source_theorems']) == 14 and len(reading['teaching_route']) == 4
for name in reading['teaching_route']+production:
    assert name in text and '../../'+nodes['declaration:'+name]['url'] in parsed.hrefs, name
module_path = nodes['declaration:'+production[0]]['url'].split('#')[0]
module = site/module_path
p = Reader(); p.feed(module.read_text(encoding='utf8')); module_text=''.join(p.text)
sys.path.insert(0, str(ROOT))
from tools.abrl_lifecycle import normalize_statement
for target in load(CONTRACT/'targets-v1.json')['targets']:
    header = normalize_statement(target['header'])
    assert header in ' '.join(module_text.split()), target['name']
    assert header in ' '.join(text.split()), target['name']
source_url='https://github.com/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/blob/'+m['source_commit']+'/'+PUBLIC.as_posix()
assert any(h.startswith(source_url+'#L') for h in p.hrefs)
write(RUN/'registry-v1.json', dict(status='passed', source_commit=m['source_commit'], source_dirty=False, lean_verified=True,
    registry_sha256=sha(site/'books/registry.json'), registry_path=(site/'books/registry.json').as_posix(), identity=r['identity'],
    preserved_base_IDs_URLs_statement_hashes=10931, new_registry_nodes=4, total_registry_nodes=10935,
    source_cards=14, new_source_cards=1, new_proof_notes=4, curated_links_preserved=4,
    source_route_HTML_sha256=sha(reader), module_HTML_sha256=sha(module), module_path=module_path,
    four_complete_headers_present=True, same_shared_registry=True, named_canaries=14,
    chapter_complete=False, goal_complete=False))
print('All 10931 prior registry IDs/URLs/statement hashes preserved; exactly four new shared nodes and complete headers.')
