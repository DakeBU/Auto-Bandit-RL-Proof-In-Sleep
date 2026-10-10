from common import *
import gzip

SITE=ROOT/'tmp/online-ch2-adaptive-energy-site-v1'
b=load(RUN/'registry-baseline-binding-v1.json')
compressed=(RUN/'registry-baseline-v1.json.gz').read_bytes()
assert hashlib.sha256(compressed).hexdigest()==b['snapshot_sha256']
raw=gzip.decompress(compressed)
prior=next(x for x in b['prior'] if x['path'].endswith('/books/registry.json'))
assert hashlib.sha256(raw).hexdigest()==prior['sha256']
old=json.loads(raw.decode('utf8'));current=load(SITE/'books/registry.json');m=load(SITE/'site-manifest.json')
head=load(RUN/'clean-candidate-site-binding-v1.json')['actual_head']
assert current['lean_verified'] and m['lean_verified'] and not m['source_dirty']
assert current['source_commit']==m['source_commit']==head
assert current['identity']==old['identity']
ob={n['id']:n for n in old['nodes']};nb={n['id']:n for n in current['nodes']}
assert len(ob)==len(old['nodes'])==b['complete_old_nodes']==11055
assert len(nb)==len(current['nodes'])==b['expected_total']==11058
for nid,node in ob.items(): assert nb[nid]==node,nid
assert set(nb)-set(ob)==set(b['new_ids'])
modules={}
for nid in b['new_ids']:
    n=nb[nid];assert n['identity_basis']=='source-qualified-name'
    url=n['url'].split('#')[0];p=SITE/url;assert p.is_file();modules[url]=sha(p)
assert not any('OnlineAdaptiveEnergyCanary' in nid for nid in nb)
reading=next(x for x in load(ROOT/'website/content/readings.json')['readings'] if x['slug']=='online-ogd')
assert len(reading['source_theorems'])==b['expected_source_cards']==16
write(RUN/'registry-inspected-v1.json',dict(source_commit=head,source_dirty=False,lean_verified=True,
    retained_complete_old_nodes=11055,new_production_nodes=3,new_theorems=3,new_definitions=0,
    source_families=1,total_nodes=11058,identity=current['identity'],new_ids=b['new_ids'],
    module_HTML_sha256=modules,source_cards=16,registry_sha256=sha(SITE/'books/registry.json'),
    Test_not_canonical_nodes=True,chapter_proof_total=None,deployed=False,chapter_complete=False,whole_Goal='active'))
print('Actual11055complete oldobjects retained +3canonical production nodes=11058;one source family/16cards.',flush=True)
