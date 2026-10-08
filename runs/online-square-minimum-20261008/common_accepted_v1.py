from common_integrated_v1 import *

def accepted_fixed():
    fixed_integrated()
    r = reviewer_receipt('final-reader-receipt-v1.json')
    assert not r.get('required_blocking_reader_repairs', [])
    requirements = load(RUN / 'stabilized-contract-v1.json')['original_reader_requirements']
    assert set(r['reader_requirement_verdicts']) == {row['id'] for row in requirements}
    for row in requirements:
        actual = r['reader_requirement_verdicts'][row['id']]
        assert actual['verdict'] == 'satisfied' and actual['requirement'] == row['requirement']
    reviewed = {x['path']:x.get('sha256', x.get('sha256_raw_bytes')) for x in r['reviewed_files']}
    resolutions = {Path(x['live_path']).resolve().as_posix():x for x in load(RUN / 'FINAL-metadata-snapshots-v1.json')}
    inputs = load(RUN / 'final-reader-inputs-v1.json')
    assert inputs['fixed_input_count'] == r['fixed_input_count'] == 489
    for row in inputs['rows']:
        p, expected = row['path'], row['sha256']
        assert reviewed[p] == expected, p
        if sha(p) != expected:
            resolution = resolutions[p]
            assert expected == resolution['sha256'] == sha(resolution['snapshot']), p
            current, original_bytes = Path(p).read_bytes(), Path(resolution['snapshot']).read_bytes()
            if Path(p) != MANIFEST.resolve():
                assert current.startswith(original_bytes), 'Only exact owned append allowed: ' + p
                if p.endswith('.jsonl'):
                    added = current[len(original_bytes):].decode('utf8')
                    for line in added.splitlines():
                        if line.strip():
                            entry = json.loads(line)
                            assert entry.get('task', entry.get('session_id')) == TASK, p
            else:
                original_manifest = json.loads(original_bytes.decode('utf8'))
                current_manifest = load(p)
                allowed = [('semantic_roundtrip', 'remaining_semantic_delta'), ('graph_contribution', 'visual_review')]
                allowed += [('verification', key) for key in ['independent_review', 'bandit_check', 'site_build', 'site_check']]
                for top, key in allowed:
                    current_manifest[top][key] = original_manifest[top][key]
                assert current_manifest == original_manifest, 'Only reviewed acceptance-evidence fields may update.'
    return r
