from common_reader_v4 import *

fixed_integrated()
receipt = load(RUN/'final-reader-receipt-v1.json')
assert sha(RUN/'final-reader-receipt-v1.json') == 'c006c6c836a03bb0259e5fccafeae810d23efc1b224da67b4a38200943627b94'
assert sha(RUN/'final-reader-review-v1.md') == '55d97b86c8ba364b5ac83c2d1adfaac70e8de85fa4eef070651a2161f18d3c39'
assert receipt['verdict'] == 'rejected'
assert len(receipt['required_blocking_repairs']) == 1
assert receipt['required_blocking_repairs'][0]['id'] == 'F1'
assert not receipt['required_mathematical_repairs']
original = load(RUN/'FINAL-review-inputs-v1.json')
assert len(original['rows']) == 444
assert all(sha(r['path']) == r['sha256'] for r in original['rows'])

before = (RUN/'prospective-PR-body-v1.md').read_bytes()
old = b'Given a prediction process with a strict-past measurable version almost everywhere, '
new = b'Given a prediction process that is [0,1]-valued almost everywhere at every natural time and has a strict-past measurable version almost everywhere, '
assert before.count(old) == 1 and before.startswith(old)
write(RUN/'prospective-PR-body-v2.md', new + before[len(old):])
write(RUN/'prospective-PR-title-v2.txt', (RUN/'prospective-PR-title-v1.txt').read_bytes())
write(CONTRACT/'publication-prose-repair-v2.json', dict(
    blocker='F1', old_prefix=old.decode(), new_prefix=new.decode(),
    original_body_sha256=sha(RUN/'prospective-PR-body-v1.md'),
    repaired_body_sha256=sha(RUN/'prospective-PR-body-v2.md'),
    rejected_receipt_sha256=sha(RUN/'final-reader-receipt-v1.json'),
    rejection_preserved=True, mathematical_contract_version=1,
    public_canary_root_readers_pins_and_pixels_unchanged=True,
    sole_publication_change='Explicit original AE unit feasibility at every natural time',
    bounded_obligations_still_pending=3, chapter_complete=False, goal_complete=False))

snapshots = []
for i, rel in enumerate(['runs/trials.jsonl', 'runs/lifecycle_sessions.jsonl']):
    p = ROOT/rel
    q = RUN/'snapshots'/('FINAL-v1-prose-repair-mutable-'+str(i)+'.raw')
    write(q, p.read_bytes())
    snapshots.append(dict(live_path=p.as_posix(), snapshot=q.as_posix(), sha256=sha(q)))

native('FINAL-rejected-reviewer-trial-v2', 'trial-log', '--task', TASK,
    '--role', 'reviewer', '--kind', 'review', '--status', 'rejected',
    '--run-id', RUN.name, '--attempt-id', 'AE-CAUSAL-FINAL-V1',
    '--verifier-evidence', RUN/'final-reader-receipt-v1.json',
    '--harness', 'hierarchical', '--progress-class', 'diagnostic', '--reviewer-validated',
    '--obligations-before', '3', '--obligations-after', '3',
    '--notes', 'FINAL444 rejected F1: prospective PR opening omits original prediction AE unit feasibility. Constant2 counterexample retained. Public statements, bodies, readers and eight original pixels unchanged; repair only versioned PR prose, no obligation accepted.')
native('FINAL-publication-repair-event-v2', 'lifecycle-event', '--session', TASK,
    '--event', 'repair', '--payload-json', json.dumps(dict(
        run_id=RUN.name, mathematical_contract_version=1, presentation_version=2,
        repair=(CONTRACT/'publication-prose-repair-v2.json').as_posix(), blocker='F1',
        frozen_mathematical_target_unchanged=True, bounded_obligations_pending=3,
        chapter_complete=False, goal_complete=False)))
for row in snapshots:
    p = Path(row['live_path']); prior = Path(row['snapshot']).read_bytes()
    assert p.read_bytes().startswith(prior)
    suffix = p.read_bytes()[len(prior):]
    entries = [json.loads(s) for s in suffix.decode('utf8').splitlines() if s.strip()]
    assert entries and all(x.get('task', x.get('session_id')) == TASK for x in entries)
    row.update(current_sha256=sha(p), exact_owned_entries=entries,
        suffix_sha256=hashlib.sha256(suffix).hexdigest())
write(RUN/'FINAL-v1-prose-repair-mutable-bindings-v2.json', snapshots)
mutable = {r['live_path']:r for r in snapshots}
for r in original['rows']:
    if r['path'] in mutable:
        assert mutable[r['path']]['sha256'] == r['sha256']
    else:
        assert sha(r['path']) == r['sha256'], r['path']
fixed_integrated()
print('Actual F1 rejection/repair recorded; only new PR prose v2. Three obligations pending; whole Goal active.', flush=True)
