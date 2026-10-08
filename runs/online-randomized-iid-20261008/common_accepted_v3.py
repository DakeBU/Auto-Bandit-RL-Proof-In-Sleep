from common_integrated_v2 import *


def accepted_fixed():
    fixed_integrated()
    r = reviewer_receipt('final-reader-receipt-v3.json')
    assert r['inputs_unchanged'] and r['before_after_raw_hashes_match']
    requirements = load(CONTRACT/'reader-requirements-v2.json')
    assert set(r['reader_requirement_verdicts']) == {x['id'] for x in requirements}
    for row in requirements:
        verdict = r['reader_requirement_verdicts'][row['id']]
        assert verdict['verdict'] == 'satisfied' and verdict['requirement'] == row['requirement']
    inputs = load(RUN/'FINAL-review-inputs-v3.json')
    assert r['fixed_input_count'] == inputs['fixed_input_count'] == len(inputs['rows']) == 1822
    reviewed = {Path(x['path']).resolve().as_posix():x.get('sha256', x.get('sha256_raw_bytes'))
        for x in r['reviewed_files']}
    resolutions = {x['live_path']:x for x in load(RUN/'FINAL-metadata-snapshots-v3.json')}
    assert len(resolutions) == 10
    for row in inputs['rows']:
        p = Path(row['path'])
        assert reviewed[p.resolve().as_posix()] == row['sha256'], p
        if sha(p) == row['sha256']:
            continue
        resolution = resolutions[p.resolve().as_posix()]
        original_bytes = Path(resolution['snapshot']).read_bytes()
        assert sha(resolution['snapshot']) == resolution['sha256'] == row['sha256'], p
        if p.resolve() == MANIFEST.resolve():
            original_manifest = json.loads(original_bytes.decode('utf8'))
            current_manifest = load(p)
            allowed = [('semantic_roundtrip', 'remaining_semantic_delta'), ('graph_contribution', 'visual_review')]
            allowed += [('verification', key) for key in ['independent_review', 'bandit_check', 'site_build', 'site_check']]
            for top, key in allowed:
                current_manifest[top][key] = original_manifest[top][key]
            assert current_manifest == original_manifest, 'Only six explicitly reviewed acceptance fields may change.'
        else:
            assert p.read_bytes().startswith(original_bytes), p
            suffix = p.read_bytes()[len(original_bytes):].decode('utf8')
            if p.suffix == '.jsonl':
                for line in suffix.splitlines():
                    if line.strip():
                        entry = json.loads(line)
                        assert entry.get('task', entry.get('session_id')) == TASK, p
    proposal = load(RUN/'proposed-publication-v3.json')
    for key in ['title', 'body']:
        assert sha(proposal[key+'_path']) == proposal[key+'_sha256']
    for row in load(RUN/'formula-render-v3.json')['images']:
        assert sha(row['path']) == row['sha256']
        assert reviewed[Path(row['path']).resolve().as_posix()] == row['sha256']
    assert r.get('permitted_future_metadata'), 'Final reviewer has not authorized the limited metadata updates.'
    return r
