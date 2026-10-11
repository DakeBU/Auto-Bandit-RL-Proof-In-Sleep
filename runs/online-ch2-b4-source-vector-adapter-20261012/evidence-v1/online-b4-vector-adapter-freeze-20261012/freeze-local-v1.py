import datetime
import hashlib
import json
from pathlib import Path
import subprocess

root = Path('E:/ABRL/worktrees/research-online-book')
dest = Path(__file__).parent
bindings = {
 'tmp/online-b4-next-after-support-planning-20261012/proposed-header-v1.txt': '6b3937a683760c04d44a0fe595490aa3a12ead49ee490eaca534670c641d3b7f',
 'tmp/online-b4-next-after-support-planning-20261012/proposal-v2.md': 'cb8f0257e2412015aab4737c993ef62211ea60de99d07617569c183b8c91e2a2',
 'tmp/neutral-finite-coordinate-declaration-20261012/blind-reconstruction-v1.md': 'af8d861cba1dfa073460be174af9d1fc4a909cbc5f15271e0e79696b38ab7797',
 'tmp/neutral-finite-coordinate-declaration-20261012/blind-reconstruction-v1.json': 'b366c90dcd3b11c06b08f9a87523c8d292310a8721a97b0295aa4d31f0fef956',
 'tmp/online-b4-vector-adapter-source-review-20261012/pre-freeze-source-review-v2.json': 'ee72677455ab97d65ddb73819080b85fef867f0dcadc8a002ddbc4ab9bb6b5c5',
 'BanditRLProof/OnlineStrongConvexSupport.lean': 'f3a475b58661a4efefdb33b9715852a08008940bd437e1cb3ad64862b772d1e5',
}
for name, sha in bindings.items():
    assert hashlib.sha256((root / name).read_bytes()).hexdigest() == sha, name
head = subprocess.check_output(['git', '-c', 'core.longpaths=true', 'rev-parse', 'HEAD'], cwd=root).decode().strip()
status = subprocess.check_output(['git', '-c', 'core.longpaths=true', 'status', '--porcelain=v1', '-z'], cwd=root).hex()
assert head == 'ceef2d303da1398bd543d144930e3ec7e1b58263' and not status
header = (root / next(iter(bindings))).read_bytes()
assert len(header) == 1097
with (dest / 'neutral-frozen-header-v1.txt').open('xb') as stream:
    stream.write(header)
record = {
 'kind': 'LOCAL TEMPORARY header freeze and experimental BODY authorization',
 'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'actor': '/root',
 'source_head': head,
 'git_status_hex': status,
 'whole_header_sha256': hashlib.sha256(header).hexdigest(),
 'whole_header_bytes': len(header),
 'input_bindings': bindings,
 'formalizer': '/root/b4_next_leaf_formalizer_20261012',
 'blind_decoder': '/root/finite_coordinate_blind_20261012',
 'source_reviewer': '/root/support_reader_source_review_20261012',
 'source_verdict': 'accepted-with-explicit-delta',
 'allowed': ['Author one BODY candidate beneath ignored tmp/online-b4-vector-adapter-body-20261012 with this exact unchanged header/context', 'Derive continuity and finite dimensionality internally; genuinely call existing stronglyConvex_support_growth'],
 'disallowed': ['tracked source or contract changes', 'public imports/reader publication', 'new public hypotheses or norm substitution', 'extra public helper declarations', 'sorry/admit/new axioms', 'canary BODY before its own reviewed frozen contract'],
 'compile_waits_for_parent_resource_release': True,
 'header_elaborated': False,
 'candidate_accepted': False,
 'canonical_contract_written_or_committed': False,
 'parent_global_validation_pending': True,
 'global_goal_complete': False,
 'open_boundaries': ['full Lemma4.2 iff', 'support existence', 'attainment', 'actual cumulative-objective producers', 'stability', 'full Theorem7.47/15.31', 'terminal repairs', 'Chapter2 and Chapters1-16 closure'],
}
with (dest / 'local-freeze-and-body-authorization-v1.json').open('x', encoding='utf-8') as stream:
    json.dump(record, stream, indent=2)
print(json.dumps({'local_header_frozen': True, 'HEAD': head, 'production_changed': False}))
