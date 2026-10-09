from publication_guard_v1 import *
import gzip
fixed()
b=load(RUN/'registry-baseline-binding-v1.json')
compressed=(RUN/'registry-baseline-v1.json.gz').read_bytes()
assert hashlib.sha256(compressed).hexdigest()==b['compressed_snapshot_sha256']
raw=gzip.decompress(compressed)
assert hashlib.sha256(raw).hexdigest()==b['prior_complete_raw_sha256']
old=json.loads(raw.decode('utf8'));current=load(SITE/'books/registry.json');manifest=load(SITE/'site-manifest.json')
head=subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf8').strip()
assert current['lean_verified'] and manifest['lean_verified'] and not manifest['source_dirty']
assert current['source_commit']==manifest['source_commit']==head
assert current['identity']==old['identity']==b['identity']
ob={n['id']:n for n in old['nodes']};nb={n['id']:n for n in current['nodes']}
assert len(ob)==len(old['nodes'])==10996 and len(nb)==len(current['nodes'])
for node_id,node in ob.items():assert nb[node_id]==node,node_id
expected=set(b['expected_new_canonical_ids'])
assert set(nb)-set(ob)==expected and len(expected)==6 and len(nb)==11002
moduleHTML={}
for node_id in expected:
    n=nb[node_id];assert n['identity_basis']=='source-qualified-name'
    url=n['url'].split('#')[0];p=SITE/url;assert p.is_file();moduleHTML[url]=sha(p)
assert not any(n.startswith('declaration:BanditRL.OnlineBregmanCanary.') for n in nb)
reading=next(r for r in load(ROOT/'website/content/readings.json')['readings'] if r['slug']=='online-ogd')
assert len(reading['source_theorems'])==8
write(RUN/'registry-inspected-v1.json',dict(source_commit=head,source_dirty=False,lean_verified=True,retained_complete_old_nodes=10996,new_production_nodes=6,new_production_theorems=5,new_production_definitions=1,total_nodes=11002,identity=current['identity'],new_ids=sorted(expected),module_HTML_sha256=moduleHTML,source_cards=8,actual_current_registry_sha256=sha(SITE/'books/registry.json'),Test_probes_not_canonical_nodes=True,source_container_closed=False,chapter_proof_total=None,deployed=False,chapter_complete=False,whole_Goal_status='ACTIVE'))
fixed()
print('All10996 complete old records preserved; exactly6 new shared source-qualified production nodes.')
