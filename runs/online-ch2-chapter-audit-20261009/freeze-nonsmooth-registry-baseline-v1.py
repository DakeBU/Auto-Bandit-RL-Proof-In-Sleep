from common_nonsmooth_roots_v1 import *
import gzip

fixed()
prior=ROOT/'runs/online-c1-chapter-audit-20261009/site-build-v4-exit.json'
receipt=load(prior)
assert receipt['actual_exit']==0 and receipt['actual_clean_at_site_start']
site=Path(receipt['command'][-1])
reg=site/'books/registry.json';raw=reg.read_bytes();d=json.loads(raw.decode('utf8'))
manifest=load(site/'site-manifest.json')
assert d['lean_verified'] and manifest['lean_verified']
assert d['source_commit']==manifest['source_commit']==receipt['source_commit']
assert len(d['nodes'])==10981
write(RUN/'registry-baseline-v1.json.gz',gzip.compress(raw,mtime=0))
write(RUN/'registry-baseline-binding-v1.json',dict(
    prior_source=reg.as_posix(),prior_complete_raw_sha256=sha(reg),
    compressed_snapshot_sha256=sha(RUN/'registry-baseline-v1.json.gz'),
    prior_actual_site_receipt=prior.relative_to(ROOT).as_posix(),prior_actual_site_receipt_sha256=sha(prior),
    source_commit=d['source_commit'],total_shared_nodes=len(d['nodes']),identity=d['identity'],
    expected_new_canonical_ids=['declaration:'+t['declaration'] for t in load(CONTRACT/'nonsmooth-targets-draft-v1.json')['targets']],
    expected_new_production_proof_nodes=3,expected_new_definition_nodes=0,
    Test_probes_not_canonical_registry_nodes=True,all_other_Books_shared_identity_retained=True,
    boundary='Snapshot of actual earlier accepted C1 local site, not main/live. Its exact node records must survive the new site; actual C2 site not built or certified yet.',
    chapter_complete=False,whole_Goal_status='ACTIVE'))
fixed()
print('Actual10981-node shared registry RAW frozen for future exact old-record preservation plus three new source-qualified nodes.')
