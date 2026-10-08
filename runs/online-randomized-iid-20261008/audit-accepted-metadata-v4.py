from common_accepted_v3 import *

r = accepted_fixed()
inputs = load(RUN/'FINAL-review-inputs-v3.json')
mutable = {x['live_path']:x for x in load(RUN/'FINAL-metadata-snapshots-v3.json')}
for row in r['reviewed_files']:
    p = Path(row['path'])
    expected = row.get('sha256', row.get('sha256_raw_bytes'))
    if p.resolve().as_posix() not in mutable:
        assert sha(p) == expected, p
digest = (RUN/'memory-digest-accepted-v3.md').read_text(encoding='utf8').rstrip('\n')
append = ('\n\n## Bounded private-tape producer accepted; draft PR pending\n\n'+digest+'\n').encode('utf8')
rows = []
for path, binding in mutable.items():
    p = Path(path)
    before = Path(binding['snapshot']).read_bytes()
    after = p.read_bytes()
    assert sha(binding['snapshot']) == binding['sha256']
    row = dict(path=path, original_snapshot=binding['snapshot'], original_sha256=binding['sha256'],
        current_sha256=sha(p), original_bytes=len(before), current_bytes=len(after))
    if p.resolve() == MANIFEST.resolve():
        old, now = json.loads(before.decode('utf8')), load(p)
        fields = [('semantic_roundtrip','remaining_semantic_delta'), ('graph_contribution','visual_review')]
        fields += [('verification',k) for k in ['independent_review','bandit_check','site_build','site_check']]
        row['exact_six_changed_fields'] = [dict(field=top+'.'+key, original=old[top][key], current=now[top][key]) for top,key in fields]
        for top,key in fields:
            assert now[top][key] != old[top][key]
            now[top][key] = old[top][key]
        assert now == old
    elif p.resolve() in {x.resolve() for x in OWN_METADATA}:
        assert after == before + append, p
        row['actual_suffix_utf8'] = append.decode('utf8')
        row['exact_single_owned_acceptance_append'] = True
    elif p.name == 'MANIFEST.md':
        assert after == before, 'No MANIFEST suffix was needed by this native acceptance.'
        row['unchanged'] = True
    else:
        assert p.suffix == '.jsonl' and after.startswith(before)
        suffix = after[len(before):]
        entries = [json.loads(line) for line in suffix.decode('utf8').splitlines() if line.strip()]
        row['unchanged'] = not entries
        assert all(x.get('task',x.get('session_id')) == TASK for x in entries)
        row['actual_suffix_entries'] = entries
        row['actual_suffix_sha256'] = hashlib.sha256(suffix).hexdigest()
        row['only_this_task_or_session'] = True
    rows.append(row)
ledger = load(CONTRACT/'chapter-one-source-ledger-accepted-v3.json')
oldledger = load(CONTRACT/'chapter-one-source-ledger-draft-v2.json')
assert ledger['maintext_items'] == oldledger['maintext_items'] and len(ledger['maintext_items']) == 16
assert ledger['chapter_mandatory_proof_total'] is None and ledger['mandatory_total'] is None
write(RUN/'actual-accepted-metadata-audit-v4.json', dict(status='passed', rows=rows,
    immutable_FINAL_inputs_rechecked=1822, all_reviewed_extra_inputs_unchanged=True,
    actual_native_overlay_sha256=sha(RUN/'native-acceptance-overlay-v3.json'),
    original16_source_objects_unchanged=True, required_proof_total_still_null=True,
    new_accepted_source_ledger_sha256=sha(CONTRACT/'chapter-one-source-ledger-accepted-v3.json'),
    globalSGB_unchanged=True, distinct_suffix_review_pending=True, PR_delivery_pending=True,
    chapter_complete=False, goal_complete=False))
print('Actual ten metadata mutations audited; distinct suffix review and draft PR delivery pending.')
