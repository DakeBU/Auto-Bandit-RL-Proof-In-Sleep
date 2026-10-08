from common_body_v2 import *

MANIFEST = CONTRIBUTION
APPEND_METADATA = [ROOT/d/(TASK+'.md') for d in
                   ['tasks','proof-obligations','proof-blueprints','conversion-windows']]

def accepted_fixed():
    fixed_integrated()
    final = load(RUN/'final-reader-receipt-v1.json')
    assert final['verdict'] in ['accepted','accepted-with-explicit-delta']
    assert final['inputs_unchanged'] and not final['required_blocking_repairs']
    assert final['report_sha256'] == sha(RUN/'final-reader-review-v1.md')
    index = RUN/'FINAL-review-inputs-v1.json'
    rows = load(index)['rows']
    assert final['fixed_input_count'] == len(rows)
    checks = {x['path']:x for x in final['raw_input_checks']}
    reviewed = {x['path']:x['sha256'] for x in final['reviewed_files']}
    assert len(checks) == len(rows) and set(checks) == {x['path'] for x in rows}
    assert reviewed[index.as_posix()] == sha(index)
    assert final['permitted_future_metadata'] == load(RUN/'FINAL-future-metadata-scope-v1.json')
    req = load(CONTRACT/'reader-requirements-v1.json')
    assert set(req) == set(final['reader_requirement_verdicts'])
    for k,v in req.items():
        x = final['reader_requirement_verdicts'][k]
        assert x['requirement'] == v and x['verdict'] == 'satisfied'
    binding = RUN/'accepted-metadata-bindings-v1.json'
    bindings = load(binding) if binding.exists() else None
    mutable = {x['path']:x for x in bindings['rows']} if bindings else {}
    originals = {x['live_path']:x for x in load(RUN/'FINAL-metadata-snapshots-v1.json')}
    for row in rows:
        p = Path(row['path']); h = row['sha256']; x = checks[row['path']]
        assert x['unchanged'] and x['before_sha256'] == x['after_sha256'] == h
        assert reviewed[row['path']] == h
        if sha(p) == h: continue
        assert row['path'] in mutable and row['path'] in originals, p
        b = mutable[row['path']]; o = originals[row['path']]
        assert sha(o['snapshot']) == h == b['original_sha256']
        assert sha(p) == b['current_sha256']
        before = Path(o['snapshot']).read_bytes()
        if p == MANIFEST:
            old = json.loads(before.decode('utf8')); current = load(p)
            assert [x['field'] for x in b['exact_six_fields']] == final['permitted_future_metadata']['manifest_fields']
            for x in b['exact_six_fields']:
                a,k = x['field'].split('.')
                assert old[a][k] == x['old'] and current[a][k] == x['new']
                current[a][k] = old[a][k]
            assert current == old
        else:
            assert p.read_bytes().startswith(before)
            suffix = p.read_bytes()[len(before):]
            assert hashlib.sha256(suffix).hexdigest() == b['suffix_sha256']
            if p in APPEND_METADATA: assert suffix.decode('utf8') == b['exact_owned_suffix']
            elif p.suffix == '.jsonl':
                entries = [json.loads(s) for s in suffix.decode('utf8').splitlines() if s.strip()]
                assert entries == b['exact_owned_entries']
                assert all(x.get('task',x.get('session_id')) == TASK for x in entries)
            else: assert p.name in ['MANIFEST.md','lifecycle_memory.jsonl'] and not suffix
    actual = final['actual_pixel_review']; expected = load(RUN/'formula-render-v1.json')['images']
    assert len(actual) == len(expected) == 12
    assert {x['path']:x['sha256'] for x in actual} == {x['path']:x['sha256'] for x in expected}
    assert all(x['actually_viewed'] and sha(x['path']) == x['sha256'] for x in actual)
    if bindings:
        assert bindings['exact_owned_suffixes'] and bindings['original_source16_unchanged']
        assert bindings['required_proof_total_null'] and bindings['globalSGB_unchanged']
    return final
