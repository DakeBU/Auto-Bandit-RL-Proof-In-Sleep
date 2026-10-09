from common import *
import gzip
fixed()
prior=ROOT/'tmp/online-ch2-proximal-site-v1/books/registry.json'
pr=ROOT/'runs/online-ch2-proximal-20261009/registry-inspected-v1.json'
old_receipt=load(pr)
assert sha(prior)==old_receipt['actual_current_registry_sha256']
raw=prior.read_bytes();old=json.loads(raw.decode('utf8'))
assert len(old['nodes'])==10996 and old['lean_verified']
assert old['source_commit']=='3a81dd6ae283fce90b849d928c18094f37b6d3b7'
d=load(CONTRACT/'stabilized-v1.json')
expected=['declaration:'+d['definition']['declaration']]+['declaration:'+t['declaration'] for t in d['targets']]
compressed=gzip.compress(raw,mtime=0)
write(RUN/'registry-baseline-v1.json.gz',compressed)
write(RUN/'registry-baseline-binding-v1.json',dict(prior_source=prior.as_posix(),prior_complete_raw_sha256=sha(prior),compressed_snapshot_sha256=hashlib.sha256(compressed).hexdigest(),prior_actual_registry_receipt_sha256=sha(pr),source_commit=old['source_commit'],total_shared_nodes=len(old['nodes']),identity=old['identity'],expected_new_canonical_ids=expected,expected_new_definitions=1,expected_new_theorems=5,Test_probes_not_canonical_nodes=True,boundary='Earlier accepted local PR208 shared registry; no main/live/current package acceptance.',chapter_complete=False,whole_Goal_status='ACTIVE'))
fixed()
print('10996 complete prior shared records cached; expect exactly six new source-qualified production nodes.')
