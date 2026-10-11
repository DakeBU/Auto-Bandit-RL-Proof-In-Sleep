import hashlib
import json
import pathlib
import subprocess
from datetime import datetime, timezone

ROOT = pathlib.Path(__file__).resolve().parents[3]
APP = pathlib.Path(__file__).resolve().parent
def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT).decode().strip()
def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()
def check(row):
    p = pathlib.Path(row['path'])
    if not p.is_absolute():
        p = ROOT / p
    assert digest(p) == row['sha256'], str(p)
    if 'bytes' in row:
        assert p.stat().st_size == row['bytes'], str(p)

review_path = ROOT / 'tmp/online-ch2-b4-next-strong-convex-freeze-audit-20261011/preproof-source-readiness-v1.json'
assert digest(review_path) == 'f9fb655d7932598e0a799865c1e56be6b8853f0675ee5d6bec54fdea1b8a0e93'
review = json.loads(review_path.read_bytes())
head = git('rev-parse', 'HEAD')
assert head == review['source_head'] == review['gate_source_head']
assert not git('status', '--porcelain=v1')
assert review['verdict'] == 'PASS_PREPROOF_SOURCE_READINESS'
assert review['maintenance_accepted'] is False
assert review['BODY_authorized'] is False
verified = []
for key in ['premise_bindings', 'static_archive_source_bindings', 'governance_continuity', 'nine_baseline_gate_receipts']:
    for row in review[key]:
        check(row)
        verified.append(row)
for row in review['nine_baseline_gate_receipts']:
    receipt = json.loads((ROOT / row['path']).read_bytes())
    assert receipt['actual_exit'] == 0 and receipt['capture_integrity_ok'] is True
    assert receipt['pre_git']['HEAD'] == receipt['post_git']['HEAD'] == head
    assert not receipt['pre_git']['status_porcelain_v1_z_hex']
    assert not receipt['post_git']['status_porcelain_v1_z_hex']
assert not (ROOT / 'BanditRLProof/OnlineStrongConvexMinimum.lean').exists()
assert not (ROOT / 'Tests/OnlineStrongConvexMinimumCanary.lean').exists()
assert git('rev-parse', 'HEAD') == head and not git('status', '--porcelain=v1')
out = dict(status='PASS_PREPROOF_SOURCE_READINESS', source_head=head, gate_source_head=head,
           utc=datetime.now(timezone.utc).isoformat(), actor='/root', clean=True,
           independent_review=dict(path=review_path.relative_to(ROOT).as_posix(), sha256=digest(review_path)),
           independent_review_sha256=digest(review_path), verified_bindings=verified,
           source_contract_sha256='aae24add096d1a78e6d1be0c75a5f9141703d196eb2a264f70ea51e74dc5e767',
           header_sha256='ded5adebef211f810552abbc4eced856dd9fff59f268989e9c1ff5a4ecd3d590',
           maintenance_accepted=False, reader_pending=True, proof_accepted=False, BODY_authorized=False,
           scope='Parent readiness decision based on independently checked unchanged source; explicit V3 only. Baseline gates do not certify a future BODY.',
           remaining='V3 design review, explicit freeze authorization, create-only application and clean committed independent applied review, then separate BODY authorization. All final publication and chapter gates retained.')
target = APP / 'parent-preproof-readiness-v1.json'
with target.open('x', encoding='utf-8', newline='\n') as f:
    json.dump(out, f, ensure_ascii=False, indent=2)
    f.write('\n')
print(json.dumps(dict(path=target.relative_to(ROOT).as_posix(), sha256=digest(target), checked_bindings=len(verified))))
