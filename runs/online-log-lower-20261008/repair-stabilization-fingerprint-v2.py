from common_v1 import *
original = RUN/'stabilize-and-first-leaf-v1.py'
assert not PUBLIC.exists() and not (RUN/'stabilized-contract-v1.json').exists()
write(RUN/'stabilization-fingerprint-repair-v2.json',dict(
    failed_helper=original.as_posix(), failed_helper_sha256=sha(original),
    observed_exit=1, observed_error='AssertionError: probability_mem at line 23',
    cause='Original planned fingerprints bind exact header UTF-8 bytes, not normalized whitespace. Stabilization v1 incorrectly compared the normalized hash.',
    correction='v2 checks original exact header bytes; native fence normalization is checked separately later.',
    source_or_header_changed=False, proof_body_written=False,
    failed_helper_preserved=True))
old='hashlib.sha256(normalize_statement(header).encode()).hexdigest()'
new='hashlib.sha256(header.encode("utf-8")).hexdigest()'
text=original.read_text(encoding='utf-8'); assert text.count(old)==1
write(RUN/'stabilize-and-first-leaf-v2.py',text.replace(old,new))
print('Exact-byte fingerprint check repaired; original failed helper and frozen inputs preserved.')
