from common_nonsmooth_publication_v2 import *
import gzip

fixed()
binding=load(RUN/'registry-baseline-binding-v1.json')
compressed=(RUN/'registry-baseline-v1.json.gz').read_bytes()
assert hashlib.sha256(compressed).hexdigest()==binding['compressed_snapshot_sha256']
raw=gzip.decompress(compressed)
assert hashlib.sha256(raw).hexdigest()==binding['prior_complete_raw_sha256']
old=json.loads(raw.decode('utf8'))
current=load(SITE/'books/registry.json');manifest=load(SITE/'site-manifest.json')
head=subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf8').strip()
assert current['lean_verified'] and manifest['lean_verified']
assert current['source_commit']==manifest['source_commit']==head
assert manifest['source_dirty'] is False
assert current['identity']==old['identity']==binding['identity']
ob={n['id']:n for n in old['nodes']};nb={n['id']:n for n in current['nodes']}
assert len(ob)==binding['total_shared_nodes']==10981
assert len(ob)==len(old['nodes']) and len(nb)==len(current['nodes'])
for node_id,node in ob.items():assert nb[node_id]==node,node_id
targets=load(CONTRACT/'nonsmooth-targets-draft-v1.json')['targets']
expected={'declaration:'+t['declaration'] for t in targets}
assert expected==set(binding['expected_new_canonical_ids'])
assert set(nb)-set(ob)==expected and len(nb)==10984
moduleHTML={}
for node_id in sorted(expected):
    node=nb[node_id];assert node['identity_basis']=='source-qualified-name'
    url=node['url'].split('#')[0];p=SITE/url;assert p.is_file();moduleHTML[url]=sha(p)
for t in targets:assert statement_hash(lean_declaration_header(PUBLIC,t['declaration']))==t['statement_hash']
reading=next(r for r in load(ROOT/'website/content/readings.json')['readings'] if r['slug']=='online-subgradient-differentiability')
assert len(reading['source_theorems'])==2
assert (SITE/'chapters/online-subgradient-differentiability/index.html').is_file()
write(RUN/'nonsmooth-registry-inspected-v1.json',dict(source_commit=head,source_dirty=False,
    lean_verified=True,retained_complete_old_nodes=10981,new_production_nodes=3,new_production_theorems=3,
    new_production_definitions=0,total_nodes=10984,identity=current['identity'],new_ids=sorted(expected),
    frozen_headers_unchanged=True,module_HTML_sha256=moduleHTML,source_cards=2,
    actual_current_registry_sha256=sha(SITE/'books/registry.json'),Test_probes_not_canonical_nodes=True,
    new_source_family_count=2,chapter_proof_total=None,deployed=False,chapter_complete=False,whole_Goal_status='ACTIVE'))
fixed()
print('Actual clean candidate registry: all10981 complete old records unchanged; exactly3 new shared proof IDs, no Test or per-Book duplicates.')
