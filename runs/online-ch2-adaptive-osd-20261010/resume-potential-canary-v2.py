from common import *
sys.path.insert(0, str(ROOT))
from tools.abrl_lifecycle import lean_declaration_header, statement_hash
canary = ROOT/'Tests/OnlineAdaptivePotentialCanary.lean'
original = RUN/'prove-potential-canary-v1.py'
write(RUN/'potential-canary-hash-wrapper-failure-v1.json', dict(
    actual_exit=1, error='AssertionError comparing parser header hash against header including := by',
    stage='after create-only Test/snapshot and stabilization metadata; before build or body-input receipt',
    helper_raw_base64=base64.b64encode(original.read_bytes()).decode('ascii'), helper_sha256=sha(original),
    source_unchanged=True, canary_sha256=sha(canary), repair='normalize frozen header by removing only trailing := by before statement_hash'))
assert canary.read_bytes() == (RUN/'potential-canary-body-attempt-v1.lean.txt').read_bytes()
scope = load(RUN/'potential-BODY-and-canary-CONTRACT-review-v1.json')['allowed_new_Test_scope']
context = Path(scope['frozen_context_and_headers'][0]['path']).read_bytes()
assert canary.read_bytes().startswith(context+b'\n')
hashes = {}
for i, name in [(1, 'leading_zero_and_stall'), (2, 'signed_zero_and_free_terminal')]:
    p = Path(scope['frozen_context_and_headers'][i]['path'])
    assert sha(p) == scope['frozen_context_and_headers'][i]['sha256']
    raw = p.read_bytes()
    assert raw in canary.read_bytes()
    expected = statement_hash(raw.decode('utf8').rstrip()[:-len(':= by')])
    assert statement_hash(lean_declaration_header(canary, name)) == expected
    hashes[name] = expected
write(RUN/'potential-canary-body-input-v2.json', dict(
    canary_sha256=sha(canary), header_hashes=hashes, expected_selected_public_calls=4,
    public_production_sha256=sha(PUBLIC), source_edit_during_recovery=False, combined_gate='pending'))
code, out = capture('potential-canary-focused-build-v1', 'lake', 'build',
    'Tests.OnlineAdaptivePotentialCanary', required=False)
print(out)
sys.exit(code)
