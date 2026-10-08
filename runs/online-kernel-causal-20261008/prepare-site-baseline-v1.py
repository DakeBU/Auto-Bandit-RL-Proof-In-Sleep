from common_body_v1 import *
import gzip

fixed_integrated()
oldsite = ROOT/'tmp/online-completed-causal-site-v5'
p = oldsite/'books/registry.json'
old = load(p)
m = load(oldsite/'site-manifest.json')
assert old['lean_verified'] and m['lean_verified'] and not m['source_dirty']
assert old['source_commit'] == m['source_commit']
assert len(old['nodes']) == 10942
snapshot = RUN/'registry-base-snapshot-v1.json.gz'
write(snapshot,gzip.compress(p.read_bytes(),mtime=0))
assert gzip.decompress(snapshot.read_bytes()) == p.read_bytes()
write(RUN/'registry-base-bindings-v1.json',dict(
    source_cached_registry_path=p.as_posix(),source_cached_registry_raw_sha256=sha(p),
    snapshot_sha256=sha(snapshot),cached_site_manifest_sha256=sha(oldsite/'site-manifest.json'),
    cached_clean_source_commit=m['source_commit'],existing_complete_node_records=len(old['nodes']),
    same_shared_registry_identity=old['identity'],
    old_public_proof_sha256=sha(ROOT/'BanditRLProof/OnlineGuessingCompletedCausal.lean'),
    cached_preceding_accepted_local_site_not_fresh_rebuild=True,
    current_new_package_site_not_yet_built=True,chapter_complete=False,goal_complete=False))
gate('help-site-build-v1',sys.executable,'-B','-X','utf8','website/scripts/build_site.py','--help')
gate('help-site-check-v1',sys.executable,'-B','-X','utf8','website/scripts/check_site.py','--help')
fixed_integrated()
print('Previous clean verified cached registry10942 complete node records preserved as a byte-bound baseline; current site gate pending.',flush=True)
