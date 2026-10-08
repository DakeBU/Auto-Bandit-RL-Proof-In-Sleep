from common_v1 import *

old_guard = RUN / 'common_body_v1.py'
old_integration = RUN / 'integrate-reader-v1.py'
original = old_guard.read_bytes()
needle = b"    assert r['required_reader_corrections']==load(CONTRACT/'reader-requirements-v1.json')"
assert original.count(needle) == 1
replacement = b"""    corrections = r['required_reader_corrections']
    requirements = load(CONTRACT/'reader-requirements-v1.json')
    assert len(corrections) == len(requirements) == 7
    assert [x['id'] for x in corrections] == list(requirements)
    assert {x['id']: x['requirement'] for x in corrections} == requirements
    assert all(x['status'] == 'future mandatory; not discharged by BODY' for x in corrections)"""
write(RUN / 'common_body_v2.py', original.replace(needle, replacement))
integration = old_integration.read_bytes()
assert integration.count(b'from common_body_v1 import *') == 1
write(RUN / 'integrate-reader-v2.py', integration.replace(
    b'from common_body_v1 import *', b'from common_body_v2 import *'))
write(RUN / 'body-receipt-reader-repair-v2.json', dict(
    failed_helper_sha256=sha(old_guard), failed_integration_sha256=sha(old_integration),
    failure='Actual AssertionError before integration mutation: receipt R1-R7 list compared to contract R1-R7 dictionary.',
    original_outer_stderr_not_separately_saved=True,
    repaired_guard_sha256=sha(RUN / 'common_body_v2.py'),
    repaired_integration_sha256=sha(RUN / 'integrate-reader-v2.py'),
    exact_original_requirement_ids_order_text_and_future_status_required=True,
    no_review_receipt_contract_or_proof_change=True))
gate('reader-integration-v2', sys.executable, '-B', '-X', 'utf8',
     RUN / 'integrate-reader-v2.py')
