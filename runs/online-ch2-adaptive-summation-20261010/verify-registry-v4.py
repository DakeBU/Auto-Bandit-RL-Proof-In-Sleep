from candidate_guard_v4 import *
import gzip
candidate_fixed();actual_gates_fixed()
b=load(RUN/'registry-baseline-binding-v1.json');compressed=(RUN/'registry-baseline-v1.json.gz').read_bytes()
assert hashlib.sha256(compressed).hexdigest()==b['compressed_snapshot_sha256']
prior=next(r for r in b['prior'] if r['path'].endswith('/books/registry.json'))
raw=gzip.decompress(compressed);assert hashlib.sha256(raw).hexdigest()==prior['sha256']
old=json.loads(raw.decode('utf8'));current=load(SITE/'books/registry.json');m=load(SITE/'site-manifest.json')
head=load(RUN/'clean-candidate-site-binding-v1.json')['actual_head']
assert current['lean_verified'] and m['lean_verified'] and not m['source_dirty']
assert current['source_commit']==m['source_commit']==head
assert current['identity']==old['identity']
ob={n['id']:n for n in old['nodes']};nb={n['id']:n for n in current['nodes']}
assert len(ob)==len(old['nodes'])==b['total_shared_nodes']==11054 and len(nb)==len(current['nodes'])==b['expected_total']==11055
for nid,node in ob.items(): assert nb[nid]==node,nid
assert set(nb)-set(ob)=={b['expected_new_id']}
n=nb[b['expected_new_id']];assert n['identity_basis']=='source-qualified-name'
url=n['url'].split('#')[0];p=SITE/url;assert p.is_file()
assert not any(n.startswith('declaration:Tests.OnlineAdaptiveSummationCanary.') or 'OnlineAdaptiveSummationCanary' in n for n in nb)
reading=next(r for r in load(ROOT/'website/content/readings.json')['readings'] if r['slug']=='online-ogd')
assert len(reading['source_theorems'])==b['expected_source_cards']==15
write(RUN/'registry-inspected-v1.json',dict(source_commit=head,source_dirty=False,lean_verified=True,retained_complete_old_nodes=11054,new_production_nodes=1,new_theorems=1,new_definitions=0,total_nodes=11055,identity=current['identity'],new_ids=[b['expected_new_id']],module_HTML_sha256={url:sha(p)},source_cards=15,registry_sha256=sha(SITE/'books/registry.json'),Test_not_canonical_nodes=True,chapter_proof_total=None,deployed=False,chapter_complete=False,whole_Goal='active'))
candidate_fixed()
print('All11054 complete prior registry nodes retained; one new shared theorem, total11055.',flush=True)
