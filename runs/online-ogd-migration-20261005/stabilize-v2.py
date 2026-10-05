"""Check raw contract evidence before recording the bounded proof transaction."""
from pathlib import Path
import hashlib, json, subprocess, sys
sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header
run = Path(__file__).parent
contract = Path('docs/contracts/online-ogd-migration-v2')
task = 'ONLINE-OGD-MIGRATION-20261005'
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def load(p): return json.loads(Path(p).read_text(encoding='utf-8'))
def write(p, value):
    with Path(p).open('w', encoding='utf-8', newline='\n') as f:
        if isinstance(value, str): f.write(value + '\n')
        else: json.dump(value, f, indent=2); f.write('\n')
fixed = load(run/'contract-source-inputs-v2.json')['rows']
review = load(run/'source-contract-receipt-v2.json')
assert review['verdict'] == 'accepted-with-explicit-delta'
assert review['required_repairs'] == [] and not review['body_acceptance']
assert len(fixed) == 215 and len(review['reviewed_files']) == 216
for row in fixed + review['reviewed_files']:
    assert sha(row['path']) == row['sha256'], row['path']
assert sha(review['report']) == review['report_sha256']
freeze = load(run/'freeze-review-v2.json')
assert sha(contract/'context.lean.txt') == freeze['context_sha256']
for name, expected in freeze['headers'].items():
    header = lean_declaration_header(run/'leaves/targets-v2.lean.txt', name)
    assert hashlib.sha256(header.encode()).hexdigest() == expected, name
    assert load(contract/(name+'.json'))['statement_hash'] == expected
for label in ['native-types-v2-01', 'neutral-types-v2-01', 'api-v2-01']:
    assert load(run/(label+'-exit.json'))['exit_code'] == 0
assert not Path('BanditRLProof/OnlineGradientDescentSource.lean').exists()
audit = dict(stage='stabilized', raw_fixed_rows=215, raw_review_rows=216,
    report_sha256=review['report_sha256'], context_sha256=freeze['context_sha256'],
    headers=freeze['headers'], first_ready_leaf='source_to_feasible',
    proof_bodies_started=False, chapter_complete=False, book_complete=False)
write(run/'stabilization-v2.json', audit)
obligations = load(run/'proof-obligations-v2.json')
obligations['stage'] = 'proving'
obligations['contract_review'] = str(run/'source-contract-receipt-v2.json')
obligations['edit_scope'] = ['BanditRLProof/OnlineGradientDescentSource.lean',
    'Tests/OnlineGradientDescentSourceCanary.lean', 'public root imports',
    'source-qualified reader/registry and evidence files',
    'later explicitly snapshotted old comment qualification; no old header/body changes']
write(run/'proof-obligations-proving-v2.json', obligations)
rows = '\n'.join('| '+r['name']+' | '+', '.join(obligations['dependency_graph'].get(r['name'], []))+
    ' | unproved |' for r in obligations['required'])
write(Path('conversion-windows')/(task+'.md'),
    '# OGD source regularity repair conversion window\n\n'
    'Frozen source: Orabona v10, printed12–15/PDF24–27, loss game printed8/PDF20. '
    'Source and twelve signatures: docs/contracts/online-ogd-migration-v2; distinct '
    'contract review: source-contract-receipt-v2.json. V1 is rejected as broad source '
    'coverage; its true stronger-assumption proof bodies stay unchanged.\n\n'
    'Lean0 is source round1; iterateT is source x_(T+1). SourceRegularLoss uses an '
    'arbitrary open differentiability neighborhood and convexity on V; source_to_feasible '
    'must produce convexity on V plus ambient derivatives at every feasible point. '
    'The supplied ambient extension fixes gradients; no extension independence.\n\n'
    'Same old project/step/iterate/iterateVariable/regret definitions. Fixed terminal '
    'has no diameter premise and retains negative distance. Variable terminal uses '
    'T>=1, positive adjacent nonincreasing schedule and eta(T-1); exact diameter '
    'requires boundedness. Tuned terminal has positive D,G,T and actual-run gradient '
    'bounds. See immutable source-intent and actual header fingerprints.\n\n'
    '| Target | Actual dependencies | State |\n|---|---|---|\n'+rows+'\n\n'
    'Proof scope fixed in proof-obligations-proving-v2.json. First leaf source_to_feasible. '
    'No theorem consumers, new algorithm or weakened terminal. Body/public canary/axioms/'
    'root/Tests/full harness/actual graph/shared registry/reader/PR gates pending. '
    'Global SGB frontier and whole-book active Goal unchanged.')
write(Path('proof-obligations')/(task+'.md'),
    '# OGD source repair obligations\n\n'+rows+'\n\n'
    'Version2 unproved obligations are frozen; prior version1 rejection and all failures '
    'retained. Future current-state overlays preserve immutable reviewed files. '
    'Allowed failure classes follow the harness; semantic/assumption changes require '
    'a new reviewed version. Source contract acceptance is not body/package acceptance. '
    'Current native command evidence and leaf attempts live in runs/'+run.name+'. '
    'Chapter2/book remain incomplete; complete migration and enumeration mandatory.')
def event(label, name, payload):
    subprocess.run([sys.executable, '-X', 'utf8', str(run/'run-command.py'), label,
        sys.executable, '-X', 'utf8', 'tools/bandit.py', 'lifecycle-event',
        '--session', task, '--event', name, '--payload-json', json.dumps(payload)], check=True)
event('stabilized-v2', 'stabilized', dict(run_id=run.name, scope='v2 twelve source repair contracts only',
    receipt=str(run/'source-contract-receipt-v2.json'), raw_rows=216,
    first_ready_leaf='source_to_feasible', body_accepted=False))
event('proving-v2', 'proving', dict(run_id=run.name, first_ready_leaf='source_to_feasible',
    route='source/compatibility adapters, real affine specialization, actual recurrence telescope',
    edit_scope=obligations['edit_scope'], frozen_headers=freeze['headers'], chapter_complete=False))
print('Version2 contract stabilized; bounded proof work may now begin.')
