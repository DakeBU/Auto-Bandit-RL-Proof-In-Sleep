from common_v1 import *

def reviewer_receipt(name):
    receipt = load(RUN / name)
    assert receipt['actor']['task'] == '/root/source_reviewer'
    assert receipt['verdict'] in ['accepted', 'accepted-with-explicit-delta']
    for key in ['required_repairs', 'required_mathematical_repairs', 'required_metadata_repairs']:
        assert not receipt.get(key, []), key
    report = receipt['report']
    path = report['path'] if isinstance(report, dict) else report
    assert sha(path) == receipt['report_sha256']
    return receipt

def reviewed_fixed():
    fixed()
    frozen = load(RUN / 'stabilized-contract-v1.json')
    assert sha(CONTRACT / 'targets-v1.json') == frozen['targets_sha256']
    assert sha(CONTRACT / 'public-context-v1.lean') == frozen['context_sha256']
    assert sha(CONTRACT / 'source-fingerprint-v1.json') == frozen['source_fingerprint_sha256']
    assert sha(RUN / 'source-contract-receipt-v1.json') == frozen['source_review_receipt_sha256']
    receipt = reviewer_receipt('source-contract-receipt-v1.json')
    reviewed = {r['path']: r.get('sha256', r.get('sha256_raw_bytes')) for r in receipt['reviewed_files']}
    resolutions = {r['original']: r for r in load(RUN / 'contract-review-baseline-resolutions-v1.json')}
    for row in load(RUN / 'source-contract-inputs-v1.json')['rows']:
        path, expected = row['path'], row['sha256']
        assert reviewed[path] == expected, path
        if sha(path) != expected:
            resolution = resolutions[path]
            assert expected == resolution['original_sha256'] == resolution['snapshot_sha256'] == sha(resolution['snapshot']), path
    assert receipt['required_reader_corrections'] == frozen['original_reader_requirements']

def headers_fixed(count):
    reviewed_fixed()
    source = PUBLIC.read_text(encoding='utf8')
    for row in load(CONTRACT / 'targets-v1.json')['rows'][:count]:
        assert source.count(row['header'] + ' := by') == 1, row['name']
        assert hashlib.sha256(row['header'].encode('utf8')).hexdigest() == row['header_sha256']
    assert 'sorry' not in source and 'admit' not in source
