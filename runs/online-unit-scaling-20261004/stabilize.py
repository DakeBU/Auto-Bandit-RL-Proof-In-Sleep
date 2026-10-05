from pathlib import Path
import hashlib, json, sys, subprocess

root = Path.cwd()
run = Path(__file__).resolve().parent
sys.path.insert(0, str(root / 'tools'))
import abrl_lifecycle as lifecycle

def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def write_json(name, value):
    with (run / name).open('w', encoding='utf-8', newline='\n') as f:
        json.dump(value, f, ensure_ascii=False, indent=2)
        f.write('\n')

receipt = json.loads((run / 'source-contract-receipt-v1.json').read_text(encoding='utf-8'))
assert receipt['actor'] == '/root/source_reviewer'
assert receipt['verdict'] == 'accepted-with-explicit-delta'
assert not receipt['required_repairs'] and not receipt['raw_drift']
assert digest(receipt['report']) == receipt['report_sha256']
for row in receipt['reviewed_files']:
    assert digest(row['path']) == row['sha256'], row['path']
freeze = json.loads((run / 'draft-freeze.json').read_text(encoding='utf-8'))
headers = json.loads((run / 'draft-headers-v1.json').read_text(encoding='utf-8'))
assert len(headers) == 22
for name, header in headers.items():
    assert lifecycle.statement_hash(header) == freeze['headers'][name]
    fence = json.loads((root / 'docs/contracts/online-unit-scaling-v1' / (name + '.json')).read_text(encoding='utf-8'))
    assert fence['statement_hash'] == freeze['headers'][name]
assert digest(run / 'leaves/context-v1.lean.txt') == freeze['context_sha256']
assert digest(root / 'docs/contracts/online-unit-scaling-v1/context.lean.txt') == freeze['context_sha256']
for label in ('draft-types-01', 'neutral-types-01', 'api-check-01'):
    assert json.loads((run / (label + '-exit.json')).read_text(encoding='utf-8'))['exit_code'] == 0
assert not (root / 'BanditRLProof/OnlineUnitScaling.lean').exists()
write_json('stabilization-binding-audit.json', {
    'status': 'passed', 'reviewed_raw_rows': len(receipt['reviewed_files']),
    'fixed_source_input_rows': receipt['fixed_input_rows'], 'frozen_headers': 22,
    'context_unchanged': True, 'source_report_sha256': receipt['report_sha256'],
    'proof_bodies_started': False, 'chapter_complete': False, 'book_complete': False})
write_json('active-contract-v1.json', {
    'stage': 'stabilized-to-proving', 'target_count': 22,
    'first_ready_leaf': 'unit_exponents',
    'allowed_edits': 'body-only new leaves/public module using identical22headers/fourdefinitioncontext; new Tests/evidence/Book metadata after actual proof compilation',
    'source_verdict': receipt['verdict'], 'remaining_required_targets': list(headers),
    'chapter_complete': False, 'book_complete': False})
(run / 'stabilization-decision.md').write_text(
    'Draft to stabilized: distinct fresh restricted-input decoder reconstructed22 targets in seven slots; distinct source reviewer accepted-with-explicit-delta without required repair. All173 raw review bindings rehashed unchanged; all22 native statement hashes and the exact four-definition context match the freeze. No proof/body/canary acceptance. Single lower route now starts dependency-ready unit_exponents, followed by inverse/support and actual history induction. Allowed edits are bodies only in new leaf/public module, with unchanged headers/context; later new public canaries/root/Test imports/Book evidence. Units exponent abstraction, full-space fixed positive coordinate conversion, explicit same-policy transport, real gradient vs EReal global-support refinement, structural arbitrary eta/improper loss algebra vs positive finite performance, source1=Lean0 and sharp negative residual remain explicit. No chapter/book/main/live completion.\n', encoding='utf-8')
runner = [sys.executable, str(run / 'run-command.py')]
for label, event, payload in [
    ('draft-lifecycle', 'draft', {'run_id': run.name, 'target_count': 22, 'context_defs': 4, 'typed_only': True, 'proof_started': False, 'frozen_contract': 'online-unit-scaling-v1'}),
    ('stabilized-lifecycle', 'stabilized', {'run_id': run.name, 'contract_version': 1, 'target_count': 22, 'source_contract_verdict': receipt['verdict'], 'edit_scope': 'body-only frozenheaders/context', 'first_leaf': 'unit_exponents'}),
    ('proving-lifecycle', 'proving', {'run_id': run.name, 'route': 'single-lower', 'first_leaf': 'unit_exponents', 'dependency_route': 'units group algebra; inverse/support transport; actual finite-history induction'})]:
    subprocess.run(runner + [label, sys.executable, 'tools/bandit.py', 'lifecycle-event', '--session', 'ONLINE-UNIT-SCALING-20261004', '--event', event, '--payload-json', json.dumps(payload)], check=True)
print('Stabilized22 unchanged targets; bodies may now start, no package acceptance.')
