from publication_guard_v1 import *
import gzip
fixed()
prior=ROOT/'tmp/online-ch2-prescient-site-v2/books/registry.json'
prior_run=ROOT/'runs/online-ch2-prescient-20261009'
inspected=load(prior_run/'registry-inspected-v1.json')
assert sha(prior)==inspected['actual_current_registry_sha256']
raw=prior.read_bytes();old=json.loads(raw.decode('utf8'))
assert len(old['nodes'])==10995 and old['lean_verified']
assert old['source_commit']=='5680bcca81c5f894b801c0599689f2a5870e8306'
compressed=gzip.compress(raw,mtime=0)
write(RUN/'registry-baseline-v1.json.gz',compressed)
write(RUN/'registry-baseline-binding-v1.json',dict(prior_source=prior.as_posix(),prior_complete_raw_sha256=sha(prior),compressed_snapshot_sha256=hashlib.sha256(compressed).hexdigest(),prior_actual_registry_receipt_sha256=sha(prior_run/'registry-inspected-v1.json'),source_commit=old['source_commit'],total_shared_nodes=len(old['nodes']),identity=old['identity'],expected_new_canonical_ids=['declaration:BanditRL.OnlineProximal.convex_minimizer_comparison'],Test_probes_not_canonical_nodes=True,boundary='Exact earlier accepted local shared registry; not main/live or new package acceptance.',chapter_complete=False,whole_Goal_status='ACTIVE'))
print('Exact10995 complete prior registry records cached; expected one new shared proof node.')
