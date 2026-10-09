from common import *
import re

def retained_domain(p, data):
    assert p.exists() and load(p) == data, p


fixed()
domain_file = ROOT / 'BanditRLProof/OnlineGradientDescent.lean'
domain_receipt = RUN / 'domain-structure-compiler-v1.json'
domain_result = load(domain_receipt)
assert domain_result['actual_exit'] == 0
domain_stdout = base64.b64decode(domain_result['stdout_base64'])
assert hashlib.sha256(domain_stdout).hexdigest() == domain_result['stdout_sha256']
domain_text = domain_stdout.decode('utf8')
prefix = 'BanditRL.OnlineGradientDescent.Domain'
for marker in ['structure ' + prefix, 'fields:', 'constructor:'] + [prefix + '.' + n for n in ['mk', 'carrier', 'nonempty', 'closed', 'convex']]:
    assert marker in domain_text, marker
lines = domain_file.read_text(encoding='utf8').splitlines()
start = lines.index('structure Domain (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where')
expected = [lines[start], '  carrier : Set E', '  nonempty : carrier.Nonempty', '  closed : IsClosed carrier', '  convex : Convex ℝ carrier']
assert lines[start:start + len(expected)] == expected
assert lines[start + len(expected)] == ''
assert lines[start + len(expected) + 2].startswith('def project ')
block = '\n'.join(expected) + '\n'
normalized = ' '.join(block.split())
inventory = load(ROOT / 'docs/contracts/online-ch2-chapter-audit-v1/complete-source-reconciliation-draft-v3.json')
old = [b for r in inventory['rows'] for b in r.get('exact_current_terminal_bindings', []) if b['declaration'] == prefix]
assert len(old) == 1
assert old[0]['complete_scope_and_BODY_sha256'] == sha(domain_file)
assert 'def project' in old[0]['native_header'] and 'def project' not in block
retained_domain(CONTRACT / 'domain-structure-signature-repair-v1.json', dict(
    declaration=prefix, module=domain_file.relative_to(ROOT).as_posix(), complete_module_sha256=sha(domain_file),
    source_first_line=start + 1, source_last_line=start + len(expected), exact_source_block=block,
    source_block_sha256=hashlib.sha256(block.encode('utf8')).hexdigest(),
    normalized_source_signature=normalized, normalized_source_signature_sha256=hashlib.sha256(normalized.encode('utf8')).hexdigest(),
    old_v3_native_header=old[0]['native_header'], old_v3_native_statement_hash=old[0]['native_statement_hash'],
    parser_defect='Historical native header extraction continued past structure where and included the next project definition header. The current complete Lean module is byte-identical.',
    authority='Narrow OWN source-block adapter v1, exact five-line assertion plus actual compiler structure/constructor/field inspection. This is not a canonical lifecycle native-header result or a newly enforced native statement fence.',
    actual_compiler_receipt=dict(path=domain_receipt.as_posix(), sha256=sha(domain_receipt), stdout_sha256=domain_result['stdout_sha256'], actual_exit=0),
    compiler_structure_and_field_output=domain_text,
    semantic_delta='Fingerprint/extraction boundary repair only. No Lean source, field, parameter, algorithm or theorem changed.',
    old_contract_mutated=False, canonical_parser_mutated=False, source_signature_review='pending', chapter_complete=False))

ancillary_file = ROOT / 'Tests/OnlineGradientDescentSourceCanary.lean'
index = load(RUN / 'current-online-declarations-v1.json')
failed = index['extraction_failures']
assert len(failed) == 6
namespace = 'Tests.OnlineGradientDescentSource'
expected_names = ['e00', 'e01', 'e10', 'e11', 'norm_e0', 'norm_e1']
assert set(r['declaration'] for r in failed) == {namespace + '.' + n for n in expected_names}
test_lines = ancillary_file.read_text(encoding='utf8').splitlines()
repaired = []
for short in expected_names:
    hits = [(i, s) for i, s in enumerate(test_lines, 1) if s.startswith('@[simp] theorem ' + short + ' :')]
    assert len(hits) == 1
    line, exact_line = hits[0]
    assert ' := by' in exact_line and exact_line.count(':=') == 1
    header = exact_line[len('@[simp] '):].split(':=')[0].strip()
    assert re.fullmatch(r'theorem ' + short + r' : .+', header)
    repaired.append(dict(declaration=namespace + '.' + short, module=ancillary_file.relative_to(ROOT).as_posix(),
        source_line=line, exact_attributed_source_line=exact_line,
        narrow_OWN_header=header, narrow_OWN_header_sha256=hashlib.sha256(' '.join(header.split()).encode('utf8')).hexdigest(),
        complete_module_sha256=sha(ancillary_file), native_header_still_unavailable=True,
        ancillary_Test_helper=True, new_production_declaration=False, source_obligation=False))
probe = RUN / 'AncillarySignatureProbeV1.lean'
write(probe, 'import Tests.OnlineGradientDescentSourceCanary\n\n' + '\n'.join('#check ' + r['declaration'] for r in repaired))
capture('ancillary-signature-compiler-v1', 'lake', 'env', 'lean', probe)
receipt = RUN / 'ancillary-signature-compiler-v1.json'
compiled = load(receipt)
compiled_stdout = base64.b64decode(compiled['stdout_base64'])
assert hashlib.sha256(compiled_stdout).hexdigest() == compiled['stdout_sha256']
compiled_text = compiled_stdout.decode('utf8')
for r in repaired:
    assert r['declaration'] + ' :' in compiled_text, r['declaration']
write(CONTRACT / 'ancillary-signature-adapter-v1.json', dict(rows=repaired,
    authority='Narrow OWN adapter limited to six exact single-line @[simp] Test headers; actual compiler checks all six names. Not a canonical native header or native fence.',
    actual_compiler_receipt=dict(path=receipt.as_posix(), sha256=sha(receipt), stdout_sha256=compiled['stdout_sha256'], actual_exit=0),
    actual_compiler_output=compiled_text,
    preserved_native_errors=failed, native_parser_mutated=False, old_source_mutated=False,
    new_mathematical_proofs=0, source_review='pending', chapter_complete=False))
event('native-signature-boundary-repair-v1', 'repair', dict(
    scope='OWN versioned source signature reconciliation',
    reason='One historical structure overcapture and six retained ancillary attributed-header extraction failures',
    evidence=['domain-structure-signature-repair-v1.json', 'ancillary-signature-adapter-v1.json'],
    old_contract_or_source_modified=False, canonical_parser_modified=False,
    mathematically_new_proofs=0, source_review='pending', chapter_complete=False))
fixed()
print('Exact structure source block and six ancillary public compiler types inspected; no Lean source changes.', flush=True)
