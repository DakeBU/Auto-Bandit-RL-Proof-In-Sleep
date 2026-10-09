from publication_guard_v1 import *
import gzip
fixed()
b = load(RUN / 'registry-baseline-binding-v1.json')
compressed = (RUN / 'registry-baseline-v1.json.gz').read_bytes()
assert hashlib.sha256(compressed).hexdigest() == b['compressed_snapshot_sha256']
raw = gzip.decompress(compressed)
assert hashlib.sha256(raw).hexdigest() == b['prior_complete_raw_sha256']
old = json.loads(raw.decode('utf8'))
current = load(SITE / 'books/registry.json')
manifest = load(SITE / 'site-manifest.json')
head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], encoding='utf8').strip()
assert current['lean_verified'] and manifest['lean_verified'] and not manifest['source_dirty']
assert current['source_commit'] == manifest['source_commit'] == head
assert current['identity'] == old['identity'] == b['identity']
ob = {n['id']: n for n in old['nodes']}
nb = {n['id']: n for n in current['nodes']}
assert len(ob) == len(old['nodes']) == 11005 and len(nb) == len(current['nodes'])
for node_id, node in ob.items():
    assert nb[node_id] == node, node_id
expected = set(b['expected_new_canonical_ids'])
assert set(nb) - set(ob) == expected and len(expected) == 10 and len(nb) == 11015
module_html = {}
for node_id in expected:
    n = nb[node_id]
    assert n['identity_basis'] == 'source-qualified-name'
    url = n['url'].split('#')[0]
    p = SITE / url
    assert p.is_file()
    module_html[url] = sha(p)
assert not any(n.startswith('declaration:BanditRL.OnlinePrescientBregmanCanary.') for n in nb)
reading = next(r for r in load(ROOT / 'website/content/readings.json')['readings'] if r['slug'] == 'online-ogd')
assert len(reading['source_theorems']) == 10
write(RUN / 'registry-inspected-v1.json', dict(source_commit=head, source_dirty=False, lean_verified=True,
    retained_complete_old_nodes=11005, new_production_nodes=10, new_production_theorems=8, new_production_definitions=2,
    total_nodes=11015, identity=current['identity'], new_ids=sorted(expected), module_HTML_sha256=module_html,
    source_cards=10, actual_current_registry_sha256=sha(SITE / 'books/registry.json'),
    Test_probes_and_generated_Test_auxiliary_not_canonical_nodes=True, source_container_closed=False,
    chapter_proof_total=None, deployed=False, chapter_complete=False, whole_Goal_status='ACTIVE'))
fixed()
print('All11005 complete old registry records preserved; exactly10 new shared production nodes(8proofs/2defs).')
