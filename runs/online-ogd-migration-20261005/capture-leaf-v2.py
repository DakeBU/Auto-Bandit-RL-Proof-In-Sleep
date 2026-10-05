"""Bind a successful actual Lean attempt to the frozen headers and native trial."""
from pathlib import Path
import hashlib, json, subprocess, sys
sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header
run = Path(__file__).parent
module = Path('BanditRLProof/OnlineGradientDescentSource.lean')
label, *names = sys.argv[1:]
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def load(p): return json.loads(Path(p).read_text(encoding='utf-8'))
def write(p, obj):
    with Path(p).open('w', encoding='utf-8', newline='\n') as f:
        json.dump(obj, f, indent=2); f.write('\n')
gate = load(run/(label+'-exit.json')); assert gate['exit_code'] == 0
assert gate['command'] == ['lake', 'env', 'lean', str(module).replace('\\','/')]
snapshot = run/'leaves'/(label+'.lean')
assert not snapshot.exists()
snapshot.write_bytes(module.read_bytes())
freeze = load(run/'freeze-review-v2.json')
headers = {}
for name in names:
    h = lean_declaration_header(module, name)
    hh = hashlib.sha256(h.encode()).hexdigest()
    assert hh == freeze['headers'][name], name
    headers[name] = hh
evidence = dict(status='compiled-local-leaves', command=gate['command'],
    exit_code=0, seconds=gate['elapsed_seconds'], module=str(module),
    module_sha256=sha(module), snapshot=str(snapshot), snapshot_sha256=sha(snapshot),
    headers=headers, semantic_body_review='pending', package_gates='pending')
write(run/(label+'-bindings.json'), evidence)
current_path = run/'proof-obligations-current-v2.json'
current = load(current_path if current_path.exists() else run/'proof-obligations-proving-v2.json')
before = sum(r['state']=='unproved' for r in current['required'])
for row in current['required']:
    if row['name'] in names:
        row.update(state='compiled-leaf', evidence=[str(run/(label+'-bindings.json'))])
after = sum(r['state']=='unproved' for r in current['required'])
current.update(stage='proving', body_review='pending', package_accepted=False)
write(current_path, current)
subprocess.run([sys.executable, '-X', 'utf8', str(run/'run-command.py'), label+'-trial',
    sys.executable, '-X', 'utf8', 'tools/bandit.py', 'trial-log',
    '--task', 'ONLINE-OGD-MIGRATION-20261005', '--run-id', run.name,
    '--role', 'lower', '--kind', 'build', '--status', 'compiled',
    '--attempt-id', label, '--progress-class', 'compiled-leaf',
    '--changed-file', str(module), '--lean', str(module),
    '--verifier-evidence', str(run/(label+'-bindings.json')),
    '--obligations-before', str(before), '--obligations-after', str(after),
    '--notes', 'Frozen v2 actual bodies typechecked locally: '+', '.join(names)+
    '. Distinct body/combined/package gates pending; chapter/book incomplete.'], check=True)
print(label, 'actual compiled leaves', len(names), 'remaining unproved', after)
