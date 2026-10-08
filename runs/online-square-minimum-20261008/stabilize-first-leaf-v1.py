from common_reviewed_v1 import *

fixed()
r = reviewer_receipt('source-contract-receipt-v1.json')
manifest = load(RUN / 'source-contract-inputs-v1.json')
reviewed = {x['path']: x.get('sha256', x.get('sha256_raw_bytes')) for x in r['reviewed_files']}
for row in manifest['rows']:
    assert sha(row['path']) == row['sha256'] == reviewed[row['path']], row['path']
assert r['required_reader_corrections'] == load(CONTRACT / 'reader-requirements-v1.json')
targets = load(CONTRACT / 'targets-v1.json')['rows']
write(RUN / 'stabilized-contract-v1.json', dict(
    state='stabilized', version=1, source_sha256=PDF_SHA,
    targets_sha256=sha(CONTRACT / 'targets-v1.json'),
    context_sha256=sha(CONTRACT / 'public-context-v1.lean'),
    source_fingerprint_sha256=sha(CONTRACT / 'source-fingerprint-v1.json'),
    source_review_receipt_sha256=sha(RUN / 'source-contract-receipt-v1.json'),
    original_reader_requirements=r['required_reader_corrections'],
    terminal_headers=targets, first_ready_leaf='M001',
    theorem_bodies_compiled=False, package_accepted=False, chapter_complete=False, goal_complete=False))
resolutions = []
for folder in ['tasks', 'conversion-windows', 'proof-obligations', 'proof-blueprints', 'research-wiki/retrieval-index']:
    p = Path(folder) / (TASK + '.md')
    snapshot = RUN / 'snapshots' / ('CONTRACT-review-' + p.as_posix().replace('/', '--') + '.raw')
    write(snapshot, p.read_bytes())
    resolutions.append(dict(original=p.resolve().as_posix(), original_sha256=sha(p),
        snapshot=snapshot.as_posix(), snapshot_sha256=sha(snapshot),
        reason='Only this task-owned mutable stage metadata changes; exact reviewed originals retained. No source/type/definition/other-task waiver.'))
    p.write_bytes(p.read_bytes() + b'\n\n## Stabilized version1; first finite proving leaf\n\nDistinct source/type CONTRACT review accepted with explicit scope. Six terminal headers and one definition frozen unchanged. R1-R8 remain future reader requirements. First leaf M001 produces empirical-mean feasibility and minimization using actual imported APIs; no target body, package, chapter or Goal acceptance at stabilization.\n')
write(RUN / 'contract-review-baseline-resolutions-v1.json', resolutions)
reviewed_fixed()
native('stabilized-event-v1', 'lifecycle-event', '--session', TASK, '--event', 'stabilized', '--payload-json',
    json.dumps(dict(contract_version=1, frozen_contract=(RUN / 'stabilized-contract-v1.json').as_posix(),
        source_review_receipt_sha256=sha(RUN / 'source-contract-receipt-v1.json'))))
native('proving-event-v1', 'lifecycle-event', '--session', TASK, '--event', 'proving', '--payload-json',
    json.dumps(dict(leaf=targets[0]['name'], reason='Actual empiricalMean_mem/minimizes types compiled; empty-prefix case explicit',
        edit_scope=PUBLIC.as_posix(), frozen_terminal_sha256=targets[0]['header_sha256'])))
native('first-worker-running-v1', 'trial-log', '--task', TASK, '--role', 'lower', '--kind', 'attempt', '--status', 'running',
    '--run-id', RUN.name, '--lean', PUBLIC, '--attempt-id', 'SQUARE-MINIMUM-M001-V1', '--harness', 'hierarchical',
    '--target-fingerprint', sha(CONTRACT / 'targets-v1.json'), '--notes',
    'First actual source-reviewed leaf: nonempty interval and actual feasible empirical mean minimize the same prefix square losses. T0 explicit empty extension without uniqueness; imported actual mean proofs for positive T.')
context = (CONTRACT / 'public-context-v1.lean').read_text(encoding='utf8')
context = context[:context.index('end BanditRL.OnlineLearning')]
body = ''' := by
  by_cases hT : T = 0
  · subst T
    simp [empiricalMean]
  · have hp : 0 < T := Nat.pos_of_ne_zero hT
    exact ⟨empiricalMean_mem y T hp hy,
      fun u _ => empiricalMean_minimizes y T hp u⟩

'''
write(PUBLIC, context + '/-- Produced feasible minimum; T0 is the empty-prefix convention, not uniqueness. -/\n' +
    targets[0]['header'] + body + 'end BanditRL.OnlineLearning\n')
headers_fixed(1)
gate('first-leaf-focused-build-v1', 'lake', 'build', 'BanditRLProof.OnlineSquareMinimum')
native('first-leaf-fence-v1', 'statement-fence', '--declaration', targets[0]['name'], '--file', PUBLIC,
    '--output', RUN / 'first-leaf-fence-v1.json')
native('first-leaf-safe-verify-v1', 'safe-verify', '--fence', RUN / 'first-leaf-fence-v1.json', '--lean-file', PUBLIC)
native('first-worker-compiled-v1', 'trial-log', '--task', TASK, '--role', 'lower', '--kind', 'build', '--status', 'compiled',
    '--run-id', RUN.name, '--lean', PUBLIC, '--attempt-id', 'SQUARE-MINIMUM-M001-V1', '--harness', 'hierarchical',
    '--target-fingerprint', sha(CONTRACT / 'targets-v1.json'), '--new-declaration', targets[0]['name'],
    '--verifier-evidence', RUN / 'first-leaf-focused-build-v1-exit.json', '--progress-class', 'compiled-leaf',
    '--obligations-before', '6', '--obligations-after', '5', '--notes',
    'Actual M001 body focused-builds; native safe-verify is a header scan, not Lean compilation. Five fixed targets and package/canary/kernel/root/Tests/harness/source BODY/reader/site/native/PR gates remain.')
write(RUN / '30_worker-M001-v1.md', 'Actual first frozen leaf compiled. Positive T uses shared mean feasibility/global minimum; T0 simplifies exact empty sum/default mean. Six-target frontier 6->5, no source/package/chapter/Goal acceptance. Actual build/fence/trial evidence is separately retained.')
write(RUN / 'leaf-progress-v1.json', dict(contract_targets=6, closed=[targets[0]['name']], remaining=[x['name'] for x in targets[1:]],
    public_sha256=sha(PUBLIC), package_accepted=False, chapter_complete=False, goal_complete=False))
headers_fixed(1)
print('Actual M001 body compiled; five exact targets remain, not package accepted.')
