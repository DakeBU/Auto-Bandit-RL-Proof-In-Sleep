from integration_guard_v4 import *
import gzip
fixed()
b=load(RUN/'registry-baseline-binding-v1.json');compressed=(RUN/'registry-baseline-v1.json.gz').read_bytes()
assert hashlib.sha256(compressed).hexdigest()==b['compressed_snapshot_sha256']
raw=gzip.decompress(compressed);assert hashlib.sha256(raw).hexdigest()==b['prior_complete_raw_sha256']
old=json.loads(raw.decode('utf8'));current=load(SITE/'books/registry.json');m=load(SITE/'site-manifest.json')
head=load(RUN/'clean-candidate-site-binding-v1.json')['actual_head']
assert current['lean_verified'] and m['lean_verified'] and not m['source_dirty']
assert current['source_commit']==m['source_commit']==head
assert current['identity']==old['identity']
ob={n['id']:n for n in old['nodes']};nb={n['id']:n for n in current['nodes']}
assert len(ob)==len(old['nodes'])==11041 and len(nb)==len(current['nodes'])
for nid,node in ob.items():assert nb[nid]==node,nid
expected=set(b['expected_new_canonical_ids'])
assert set(nb)-set(ob)==expected and len(expected)==13 and len(nb)==11054
module_html={}
for nid in expected:
    n=nb[nid];assert n['identity_basis']=='source-qualified-name'
    url=n['url'].split('#')[0];p=SITE/url;assert p.is_file();module_html[url]=sha(p)
assert not any(n.startswith('declaration:Tests.OnlineFTLSelector.') or 'OnlineFTLSelectorCanary' in n for n in nb)
reading=next(r for r in load(ROOT/'website/content/readings.json')['readings'] if r['slug']=='online-ogd')
assert len(reading['source_theorems'])==14
write(RUN/'registry-inspected-v1.json',dict(source_commit=head,source_dirty=False,lean_verified=True,retained_complete_old_nodes=11041,new_production_nodes=13,new_theorems=9,new_definitions=4,total_nodes=11054,identity=current['identity'],new_ids=sorted(expected),module_HTML_sha256=module_html,source_cards=14,registry_sha256=sha(SITE/'books/registry.json'),Test_and_generated_Test_not_canonical_nodes=True,source_container_closed=False,chapter_proof_total=None,deployed=False,chapter_complete=False,whole_Goal='active'))
fixed()
print('All11041 complete old registry objects preserved;13 new shared production declarations;11054 total.',flush=True)
