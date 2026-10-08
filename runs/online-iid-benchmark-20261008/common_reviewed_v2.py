from common_v1 import *
import re

def reviewer_receipt(name='source-contract-receipt-v2.json'):
    receipt = load(RUN / name)
    assert receipt['actor']['task'] == '/root/source_reviewer'
    assert receipt['verdict'] in ['accepted', 'accepted-with-explicit-delta']
    for key in ['required_repairs', 'required_blocking_repairs', 'required_mathematical_repairs', 'required_metadata_repairs']:
        assert not receipt.get(key, []), (key, receipt.get(key))
    report = receipt['report']
    path = report['path'] if isinstance(report, dict) else report
    expected = receipt.get('report_sha256')
    if expected is None and isinstance(report, dict):
        expected = report.get('sha256', report.get('sha256_raw_bytes'))
    assert expected and sha(path) == expected
    return receipt

def reviewed_fixed():
    fixed()
    receipt = reviewer_receipt()
    inputs = load(RUN / 'source-review-inputs-v2.json')
    assert inputs['contract_version'] == 2 and inputs['fixed_input_count'] == 186
    assert receipt['fixed_input_count'] == 186
    reviewed = {row['path']:row.get('sha256', row.get('sha256_raw_bytes')) for row in receipt['reviewed_files']}
    metadata = {Path(row['live_path']).resolve().as_posix():row for row in load(RUN / 'CONTRACT-metadata-snapshots-v2.json')}
    for row in inputs['rows']:
        p, expected = row['path'], row['sha256']
        assert reviewed[p] == expected, p
        if sha(p) != expected:
            snapshot = metadata[p]
            assert snapshot['sha256'] == expected == sha(snapshot['snapshot']), p
            assert Path(p).read_bytes().startswith(Path(snapshot['snapshot']).read_bytes()), p
    fingerprint = load(CONTRACT / 'source-fingerprint-v2.json')
    assert sha(CONTRACT / 'targets-v2.json') == fingerprint['targets_sha256']
    assert sha(CONTRACT / 'public-context-v1.lean') == fingerprint['public_context_sha256']
    return receipt

def headers_fixed(count=8):
    reviewed_fixed()
    context = (CONTRACT / 'public-context-v1.lean').read_text(encoding='utf8')
    context = context[:context.index('end BanditRL.OnlineLearning')]
    text = PUBLIC.read_text(encoding='utf8')
    assert text.startswith(context), 'Complete frozen definition/import context changed.'
    rows = load(CONTRACT / 'targets-v2.json')['rows']
    assert len(rows) == 8
    for row in rows[:count]:
        assert hashlib.sha256(row['header'].encode('utf8')).hexdigest() == row['header_sha256']
        assert text.count(row['header'] + ' := by\n') == 1, row['name']
    assert not re.search(r'\b(sorry|admit)\b|(?m:^\s*axiom\b)', text), 'Proof placeholder/axiom disallowed.'

