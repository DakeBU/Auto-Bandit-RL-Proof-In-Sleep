from common_integrated_v2 import *
from html.parser import HTMLParser

fixed_integrated()
site = Path('tmp/online-iid-benchmark-site-v9')
r, m, old = load(site / 'books/registry.json'), load(site / 'site-manifest.json'), load(RUN / 'registry-base-snapshot-v2.json')
assert r['lean_verified'] and m['lean_verified'] and not m['source_dirty']
assert r['source_commit'] == m['source_commit']
nodes = {x['id']:x for x in r['nodes']}; base = {x['id']:x for x in old['nodes']}
assert len(base) == 10913 and r['identity'] == old['identity']
assert all(i in nodes and nodes[i]['url'] == n['url'] and nodes[i].get('statement_sha256') == n.get('statement_sha256') for i,n in base.items())
production = load(MANIFEST)['reuse_plan']['new_shared_declarations']
assert len(production) == 10
assert set(nodes) - set(base) == {'declaration:' + n for n in production}
assert len(nodes) == 10923
bindings = {x['name']:x for x in load(RUN / 'full-fence-bindings-v2.json')}
for name in production:
    node = nodes['declaration:' + name]
    assert node['status'] == 'compiled' and 'online-learning' in node['books'] and 'teaching:online-foundations' in node['chapters'], name
    if name in bindings: assert node['statement_sha256'] == bindings[name]['statement_hash'], name
assert not any(TEST in node['id'] for node in r['nodes'])
class ReaderText(HTMLParser):
    def __init__(self): super().__init__(); self.text=[]; self.hrefs=[]
    def handle_data(self, data): self.text.append(data)
    def handle_starttag(self, tag, attrs):
        if tag == 'a': self.hrefs.extend(v for k,v in attrs if k == 'href')
reader = site / 'chapters/online-foundations/index.html'
parsed = ReaderText(); parsed.feed(reader.read_text(encoding='utf8')); text = ''.join(parsed.text)
reading = next(x for x in load('website/content/readings.json')['readings'] if x['slug'] == ROUTE)
assert len(reading['source_theorems']) == 12 and len(reading['teaching_route']) == 4
notes = [x for x in load('website/content/highlights.json')['highlights'] if x['full_name'] in production]
assert len(notes) == 8
for name in reading['teaching_route'] + [x['full_name'] for x in notes]:
    assert name in text and '../../' + nodes['declaration:' + name]['url'] in parsed.hrefs, name
for phrase in ['expectation stays inside that minimization', 'not eight printed theorems', 'Generally infinite', 'BEFORE', 'a.s.', 'only on legal unit tuples', 'consumer only', 'starts at1/2', 'distribution-known oracle', 'T>0', 'asymptotic-success equivalence', 'randomization/general filtration', 'five older main-relative', 'unknown(null)', 'totalGoalACTIVE', 'not main/live', 'Safe-verify itself does not compile', 'future-aware']:
    assert phrase in text, phrase
module_path = nodes['declaration:' + PRE + 'meanPredict_expectedFixed_excess']['url'].split('#')[0]
module = site / module_path
parsed = ReaderText(); parsed.feed(module.read_text(encoding='utf8')); module_text = ''.join(parsed.text)
for name in production: assert name in module_text, name
sys.path.insert(0, str(ROOT)); from tools.abrl_lifecycle import normalize_statement
headers = {x['name']:x['header'] for x in load(RUN / 'actual-public-canary-headers-v2.json') if x['path'] == PUBLIC.as_posix()}
assert len(headers) == 8
for name, header in headers.items(): assert normalize_statement(header) in ' '.join(module_text.split()), name
for name in production[:8]: assert normalize_statement(headers[name]) in ' '.join(text.split()), name
source_url = 'https://github.com/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/blob/' + m['source_commit'] + '/' + PUBLIC.as_posix()
assert any(href.startswith(source_url + '#L') for href in parsed.hrefs)
write(RUN / 'registry-v9.json', dict(status='passed', source_commit=m['source_commit'], source_dirty=False, lean_verified=True,
    registry_sha256=sha(site / 'books/registry.json'), registry_path=(site / 'books/registry.json').as_posix(), identity=r['identity'],
    preserved_base_IDs_URLs_statement_hashes=10913, new_registry_nodes=10, total_registry_nodes=10923,
    new_public_proofs=8, new_public_definitions=2, source_cards=12, new_source_cards=1, new_proof_notes=8,
    curated_links_preserved=4, source_route_HTML_sha256=sha(reader), module_HTML_sha256=sha(module), module_path=module_path,
    eight_actual_headers_present=True, same_shared_registry=True, named_canaries=28,
    deterministic_expected_fixed_core_closed=True, randomized_and_asymptotic_source_coverage_required=True, chapter_complete=False, goal_complete=False))
print('10913old registry IDs/URLs/hashes preserved;10new shared production nodes; eight exact source-note/catalog headers checked.')
