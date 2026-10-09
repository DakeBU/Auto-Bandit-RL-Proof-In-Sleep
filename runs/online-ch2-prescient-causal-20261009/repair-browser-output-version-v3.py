from publication_guard_v2 import *
fixed()
failure = load(RUN / 'reader-file-browser-capture-command-v2.json')
assert failure['actual_exit'] == 1
out = base64.b64decode(failure['stdout_base64']).decode('utf8')
assert 'EEXIST' in out and 'formula-render-v1-dom.html' in out
s = (RUN / 'capture-prescient-reader-v2.cjs').read_text(encoding='utf8')
s = s.replace('-v2.', '-v3.').replace('formula-render-v1-', 'formula-render-v3-')
assert 'formula-render-v1-' not in s and 'public-note-7-v3.png' in s
write(RUN / 'capture-prescient-reader-v3.cjs', s)
s = (RUN / 'run-file-browser-capture-v2.py').read_text(encoding='utf8')
for name in ['browser-generated-inputs-before', 'browser-generated-inputs-after', 'reader-file-browser-capture-command', 'formula-render', 'online-ch2-prescient-causal-browser', 'capture-prescient-reader']:
    s = s.replace(name + '-v2', name + '-v3')
write(RUN / 'run-file-browser-capture-v3.py', s)
s = (RUN / 'prepare-FINAL-v3.py').read_text(encoding='utf8')
for name in ['reader-file-browser-capture-command', 'formula-render', 'browser-generated-inputs-before']:
    s = s.replace(name + '-v2', name + '-v3')
s = s.replace('Original DOM/images/failed inspections retained.', 'Original DOM/images/failed inspections retained. Browser-v2 strengthened premise check passed but create-only DOM output collided with v1 name; actual exit1 retained, no old evidence overwritten; complete browser-v3 uses fresh names/profile.')
write(RUN / 'prepare-FINAL-v4.py', s)
write(RUN / 'browser-output-collision-inspected-v2.json', dict(
    actual_exit=1, receipt_sha256=sha(RUN / 'reader-file-browser-capture-command-v2.json'),
    cause='Version substitution covered -v1. image suffixes but missed -v1-dom/-v1-browser names. Create-only DOM write raised EEXIST after twelve panel images; prior evidence protected.',
    actual_strengthened_MathML_premise_check_passed_before_output_collision=True,
    old_DOM_and_browser_receipts_preserved=True,
    repaired_SITEv2_content_unchanged=True, proof_and_contract_unchanged=True,
    fresh_v3_capture_pending=True, whole_Goal_status='ACTIVE'))
fixed()
print('Recorded browser-v2 output collision; fresh v3 output names/profile preserve all old evidence.')
