from common_reader_v3 import *

APPEND_METADATA = [ROOT / d / (TASK + '.md') for d in
                   ['tasks', 'proof-obligations', 'proof-blueprints', 'conversion-windows']]

def accepted_fixed():
    final = load(RUN / 'final-reader-receipt-v1.json')
    assert final['verdict'] in ['accepted', 'accepted-with-explicit-delta']
    assert final['inputs_unchanged'] and not final['required_blocking_repairs']
    index = RUN / 'FINAL-review-inputs-v1.json'
    rows = load(index)['rows']
    assert final['fixed_input_count'] == len(rows)
    checks = final['raw_input_checks']
    assert len(checks) == len(rows)
    checkmap = {x['path']: x for x in checks}
    assert set(checkmap) == {r['path'] for r in rows}
    for r in rows:
        x = checkmap[r['path']]
        assert x['unchanged'] and x['before_sha256'] == x['after_sha256'] == r['sha256']
    assert final['report_sha256'] == sha(RUN / 'final-reader-review-v1.md')
    req = load(CONTRACT / 'reader-requirements-v1.json')
    assert set(final['reader_requirement_verdicts']) == set(req)
    for k, v in req.items():
        r = final['reader_requirement_verdicts'][k]
        assert r['requirement'] == v and r['verdict'] == 'satisfied', k
    assert final['permitted_future_metadata'] == load(RUN / 'FINAL-future-metadata-scope-v1.json')
    reviewed = {r['path']: r['sha256'] for r in final['reviewed_files']}
    assert reviewed[index.as_posix()] == sha(index)
    bindingfile = RUN / 'accepted-metadata-bindings-v1.json'
    bindings = load(bindingfile) if bindingfile.exists() else None
    mutable = {r['path']: r for r in bindings['rows']} if bindings else {}
    originals = {r['live_path']: r for r in load(RUN / 'FINAL-metadata-snapshots-v1.json')}
    for r in rows:
        assert reviewed[r['path']] == r['sha256'], r['path']
        if sha(r['path']) == r['sha256']: continue
        assert r['path'] in mutable and r['path'] in originals, r['path']
        b = mutable[r['path']]; o = originals[r['path']]
        assert sha(o['snapshot']) == r['sha256'] == b['original_sha256']
        assert sha(r['path']) == b['current_sha256']
        p = Path(r['path']); before = Path(o['snapshot']).read_bytes()
        if p == MANIFEST:
            old = json.loads(before.decode('utf8')); current = load(p)
            assert [x['field'] for x in b['exact_six_fields']] == final['permitted_future_metadata']['manifest_fields']
            for x in b['exact_six_fields']:
                a, k = x['field'].split('.')
                assert old[a][k] == x['old'] and current[a][k] == x['new']
                current[a][k] = old[a][k]
            assert current == old
        else:
            assert p.read_bytes().startswith(before)
            suffix = p.read_bytes()[len(before):]
            assert hashlib.sha256(suffix).hexdigest() == b['suffix_sha256']
            if p in APPEND_METADATA:
                assert suffix.decode('utf8') == b['exact_owned_suffix']
            elif p.suffix == '.jsonl':
                entries = [json.loads(s) for s in suffix.decode('utf8').splitlines() if s.strip()]
                assert entries == b['exact_owned_entries']
                assert all(x.get('task', x.get('session_id')) == TASK for x in entries)
            else: assert p.name == 'MANIFEST.md' and not suffix
    images = final['actual_pixel_review']
    expected = load(RUN / 'formula-render-v3.json')['images']
    assert len(images) == len(expected) == 10
    assert {x['path']: x['sha256'] for x in images} == {x['path']: x['sha256'] for x in expected}
    assert all(x['actually_viewed'] and sha(x['path']) == x['sha256'] for x in images)
    assert sha(PUBLIC) == load(RUN / 'body-bindings-v1.json')['public_sha256']
    assert sha(CANARY) == load(RUN / 'body-bindings-v1.json')['canary_sha256']
    if bindings:
        assert bindings['exact_owned_suffixes'] and bindings['original_source16_unchanged']
        assert bindings['required_proof_total_null'] and bindings['globalSGB_unchanged']
    else: fixed_integrated()
    return final
