from common_v1 import *

fixed()
original = RUN / 'prepare-source-review-v1.py'
receipt_path = RUN / 'blind-receipt-v1.json'
b = load(receipt_path)
assert b['actor']['task'] == '/root/osd_blind'
assert isinstance(b['report'], dict)
assert sha(b['report']['path']) == b['report']['sha256_raw_bytes'] == b['report_sha256']
assert not b.get('ambiguities', [])
for row in b['reviewed_files']:
    assert sha(row['path']) == row['sha256_raw_bytes'], row['path']
for row in b['input_rehash']:
    assert sha(row['path']) == row['sha256_before'] == row['sha256_after'], row['path']
assert b['inputs_unchanged'] and b['manifest_row_hashes_match']
write(RUN / 'source-preparation-repair-v2.json', dict(
    failed_script=original.as_posix(), failed_script_sha256=sha(original),
    observed_actual_exit_code=1,
    observed_exception="TypeError: expected str, bytes or os.PathLike object, not dict",
    cause='The original helper treated receipt.report as a path; the actual immutable decoder receipt uses a path/hash object.',
    failure_stage='First receipt assertion, before reader requirements or source-review outputs were written.',
    preserved_receipt_sha256=sha(receipt_path),
    repair='Read actual report.path and report.sha256_raw_bytes; rehash every reviewed/input row without changing the decoder outputs.',
    target_or_context_changed=False, source_acceptance=False, theorem_bodies_proved=False))
source = original.read_text(encoding='utf8')
tail_marker = 'required=[\n'
assert source.count(tail_marker) == 1
tail = source[source.index(tail_marker):]
exec(compile(tail, original.as_posix() + ':verified-resume-tail-v2', 'exec'))
