from common_v1 import *

baseline_fixed(mutable=['MANIFEST.md','runs/lifecycle_sessions.jsonl'])
r = load(RUN / 'source-contract-receipt-v1.json')
assert r['verdict'] in ['accepted','accepted-with-explicit-delta']
assert r['inputs_unchanged'] and not r['required_blocking_repairs']
rows = load(RUN / 'source-contract-review-inputs-v1.json')['rows']
assert r['fixed_input_count'] == len(rows) == 104
assert len(r['raw_input_checks']) == len(rows)
checked = {x['path']:x for x in r['raw_input_checks']}
assert set(checked) == {x['path'] for x in rows}
for row in rows:
    x = checked[row['path']]
    assert x['unchanged'] and x['before_sha256'] == x['after_sha256'] == row['sha256']
    assert sha(row['path']) == row['sha256']
assert r['report_sha256'] == sha(RUN / 'source-contract-review-v1.md')
assert r['permitted_future_proof_scope'] == load(RUN / 'contract-mutable-scope-v1.json')
assert r['required_reader_corrections'] == load(CONTRACT / 'reader-requirements-v1.json')
scope = r['permitted_future_proof_scope']
mutable = set(scope['task_metadata_append_only'] + scope['own_journals_append_only'])
snapshots = []
for row in rows:
    p = Path(row['path'])
    try:
        rel = p.relative_to(ROOT).as_posix()
    except ValueError:
        rel = None
    if rel in mutable:
        snapshot = RUN / 'snapshots' / ('contract-mutable-' + str(len(snapshots)) + '.raw')
        write(snapshot, p.read_bytes())
        snapshots.append(dict(path=p.as_posix(), original_sha256=row['sha256'], snapshot=snapshot.as_posix()))
assert len(snapshots) == 6
targets = load(CONTRACT / 'targets-v2.json')['targets']
write(RUN / 'stabilized-contract-v1.json', dict(contract_version=2, source_sha256=PDF_SHA,
      receipt_sha256=sha(RUN / 'source-contract-receipt-v1.json'),
      report_sha256=sha(RUN / 'source-contract-review-v1.md'),
      targets_sha256=sha(CONTRACT / 'targets-v2.json'), headers_sha256=sha(CONTRACT / 'targets-v1.lean.txt'),
      context_sha256=sha(CONTRACT / 'context-v2.lean.txt'), source_intent_sha256=sha(CONTRACT / 'source-intent-v1.md'),
      targets=targets, approved_scope=scope, mutable_reviewed_snapshots=snapshots,
      contract_only_accepted=True, body_accepted=False, compiled_new_bodies=0,
      scanner_historical_diff_reviewer_independently_reproduced=False,
      required_reader_corrections=r['required_reader_corrections'], chapter_complete=False, goal_complete=False))
native('lifecycle-stabilized-v1','lifecycle-event','--session',TASK,'--event','stabilized','--payload-json',
       json.dumps(dict(run_id=RUN.name, contract_version=2, source_sha256=PDF_SHA,
       source_contract_receipt_sha256=sha(RUN / 'source-contract-receipt-v1.json'),
       target_statement_hashes=[t['statement_hash'] for t in targets], obligations=5,compiled=0,
       historical_scanner_review_supplement_pending=True, chapter_complete=False,goal_complete=False)))
write(RUN / 'proving-K1-v1.json', dict(leaf='K1',terminal=targets[0]['name'],
      statement_hash=targets[0]['statement_hash'], dependency_ready=True,
      route='Pinned single-step Markov sampling for each natural time, countable family choice independent of nu/horizon',
      allowed_file=PUBLIC.relative_to(ROOT).as_posix(), single_lower_route=True,
      no_terminal_or_algorithm_definition_edits=True, actual_new_body_compiled=False))
native('lifecycle-proving-K1-v1','lifecycle-event','--session',TASK,'--event','proving','--payload-json',
       json.dumps(dict(run_id=RUN.name,selected_leaf='K1',statement_hash=targets[0]['statement_hash'],
       actual_dependency_ready=True,allowed_file=PUBLIC.relative_to(ROOT).as_posix(), single_lower_route=True,
       no_terminal_type_edits=True,compiled=0)))
print('Actual contractv2 stabilized; dependency-ready K1 selected; no new body compiled.',flush=True)
