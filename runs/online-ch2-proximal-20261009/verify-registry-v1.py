from publication_guard_v2 import *
import gzip
fixed();binding=load(RUN/'registry-baseline-binding-v1.json')
compressed=(RUN/'registry-baseline-v1.json.gz').read_bytes();assert hashlib.sha256(compressed).hexdigest()==binding['compressed_snapshot_sha256']
raw=gzip.decompress(compressed);assert hashlib.sha256(raw).hexdigest()==binding['prior_complete_raw_sha256']
old=json.loads(raw.decode('utf8'));current=load(SITE/'books/registry.json');manifest=load(SITE/'site-manifest.json')
head=subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf8').strip()
assert current['lean_verified'] and manifest['lean_verified'] and not manifest['source_dirty']
assert current['source_commit']==manifest['source_commit']==head
assert current['identity']==old['identity']==binding['identity']
ob={n['id']:n for n in old['nodes']};nb={n['id']:n for n in current['nodes']}
assert len(ob)==len(old['nodes'])==10995 and len(nb)==len(current['nodes'])
for node_id,node in ob.items():assert nb[node_id]==node,node_id
expected=set(binding['expected_new_canonical_ids']);assert set(nb)-set(ob)==expected and len(expected)==1 and len(nb)==10996
moduleHTML={}
for node_id in expected:
    n=nb[node_id];assert n['identity_basis']=='source-qualified-name'
    url=n['url'].split('#')[0];p=SITE/url;assert p.is_file();moduleHTML[url]=sha(p)
assert not any(n.startswith('declaration:BanditRL.OnlineProximalCanary.') for n in nb)
reading=next(r for r in load(ROOT/'website/content/readings.json')['readings'] if r['slug']=='online-ogd');assert len(reading['source_theorems'])==7
write(RUN/'registry-inspected-v1.json',dict(source_commit=head,source_dirty=False,lean_verified=True,retained_complete_old_nodes=10995,new_production_nodes=1,new_production_theorems=1,total_nodes=10996,identity=current['identity'],new_ids=sorted(expected),frozen_headers_unchanged=True,module_HTML_sha256=moduleHTML,source_cards=7,actual_current_registry_sha256=sha(SITE/'books/registry.json'),Test_probes_not_canonical_nodes=True,source_container_closed=False,chapter_proof_total=None,deployed=False,chapter_complete=False,whole_Goal_status='ACTIVE'))
fixed();print('All10995 complete old records preserved; exactly1new shared source-qualified proof node.')
