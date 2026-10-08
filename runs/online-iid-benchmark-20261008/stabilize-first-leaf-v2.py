from common_reviewed_v2 import *

receipt = reviewed_fixed()
requirements = load(CONTRACT / 'reader-requirements-v2.json')
assert receipt['required_reader_corrections'] == requirements
assert receipt['revision_verdict']['verdict'] == 'satisfied'
assert receipt['revision_verdict']['changed_ids'] == ['I005', 'I008']
targets = load(CONTRACT / 'targets-v2.json')['rows']
write(RUN / 'stabilized-contract-v2.json', dict(state='stabilized', version=2, source_sha256=PDF_SHA,
    targets_sha256=sha(CONTRACT / 'targets-v2.json'), context_sha256=sha(CONTRACT / 'public-context-v1.lean'),
    source_fingerprint_sha256=sha(CONTRACT / 'source-fingerprint-v2.json'),
    source_review_receipt_sha256=sha(RUN / 'source-contract-receipt-v2.json'),
    original_reader_requirements=requirements, terminal_headers=targets, first_ready_leaf='I001',
    theorem_bodies_compiled=False, package_accepted=False, chapter_complete=False, goal_complete=False))
for folder in ['tasks', 'conversion-windows', 'proof-obligations', 'proof-blueprints', 'research-wiki/retrieval-index']:
    p = Path(folder) / (TASK + '.md')
    p.write_bytes(p.read_bytes() + ('\n\n## Stabilized version2; first finite proving leaf I001\n\n' +
        'Actual distinct CONTRACT v2 accepted-with-explicit-delta; exact eight headers/two definitions frozen. '
        'R1–R9 remain future actual proof/reader/gate obligations. First I001 derives observation L2 and finite square integrability from a.s. support, '
        'then reuses actual square decomposition/same-law equality and finite sums. No public body/package/chapter/Goal accepted at stabilization.\n').encode('utf8'))
reviewed_fixed()
native('stabilized-event-v2', 'lifecycle-event', '--session', TASK, '--event', 'stabilized', '--payload-json', json.dumps(dict(
    contract_version=2, frozen_contract=(RUN / 'stabilized-contract-v2.json').as_posix(),
    source_review_receipt_sha256=sha(RUN / 'source-contract-receipt-v2.json'), original_v1_preserved=True)))
native('proving-event-v2', 'lifecycle-event', '--session', TASK, '--event', 'proving', '--payload-json', json.dumps(dict(
    leaf=targets[0]['name'], reason='Actual L2 square decomposition, integral finite-sum and same-law API types compile',
    edit_scope=PUBLIC.as_posix(), frozen_terminal_sha256=targets[0]['header_sha256'], contract_version=2)))
native('first-worker-running-v2', 'trial-log', '--task', TASK, '--role', 'lower', '--kind', 'attempt', '--status', 'running',
    '--run-id', RUN.name, '--lean', PUBLIC, '--attempt-id', 'IID-I001-V2', '--harness', 'hierarchical',
    '--target-fingerprint', sha(CONTRACT / 'targets-v2.json'), '--notes',
    'First source-reviewed fixed expected-loss prefix leaf; derive L2 from a.s. unit support, integrable square finite sum, same-law mean/variance, actual square decomposition. No target edit or supplied minimizer/regret certificate.')
context = (CONTRACT / 'public-context-v1.lean').read_text(encoding='utf8')
context = context[:context.index('end BanditRL.OnlineLearning')]
body = ''' := by
  have hL (t : ℕ) : MemLp (Y t) 2 μ :=
    memLp_of_bounded (hb t) (hY t).aestronglyMeasurable 2
  rw [integral_finset_sum (Finset.range T)
    (fun t _ => ((memLp_const u).sub (hL t)).integrable_sq)]
  have heq (t : ℕ) :
      (∫ ω, (u - Y t ω)^2 ∂μ) =
        variance (Y 0) μ + (u - ∫ ω, Y 0 ω ∂μ)^2 := by
    simpa only [(hlaw t).integral_eq, (hlaw t).variance_eq] using
      expected_square_decomposition μ (Y t) (hL t) u
  simp_rw [heq]
  simp [Finset.sum_add_distrib]

'''
write(PUBLIC, context + '/-- Same-law expected fixed loss; a.s. support produces L2 before finite integration. -/\n' +
    targets[0]['header'] + body + 'end BanditRL.OnlineLearning\n')
headers_fixed(1)
gate('first-leaf-focused-build-v2', 'lake', 'build', 'BanditRLProof.OnlineGuessingIIDBenchmark')
native('first-leaf-fence-v2', 'statement-fence', '--declaration', targets[0]['name'], '--file', PUBLIC,
    '--output', RUN / 'first-leaf-fence-v2.json')
native('first-leaf-safe-verify-v2', 'safe-verify', '--fence', RUN / 'first-leaf-fence-v2.json', '--lean-file', PUBLIC)
native('first-worker-compiled-v2', 'trial-log', '--task', TASK, '--role', 'lower', '--kind', 'build', '--status', 'compiled',
    '--run-id', RUN.name, '--lean', PUBLIC, '--attempt-id', 'IID-I001-V2', '--harness', 'hierarchical',
    '--target-fingerprint', sha(CONTRACT / 'targets-v2.json'), '--new-declaration', targets[0]['name'],
    '--verifier-evidence', RUN / 'first-leaf-focused-build-v2-exit.json', '--progress-class', 'compiled-leaf',
    '--obligations-before', '8', '--obligations-after', '7', '--notes',
    'Actual I001 body focused-builds; current-target independence not needed for fixed losses. Native safe-verify is only header scan. Seven exact targets and actual min/causal/canary/kernel/root/Tests/harness/source BODY/reader/site/FINAL/native/PR gates remain.')
write(RUN / '30_worker-I001-v2.md',
    'Actual first frozen I001 body compiles. Derives L2 from a.s. interval support, each square Integrable, then integrates finite sum and actual same-law scalar square decomposition. '
    'Eight-terminal frontier8→7 only; no assumed minimizer/current-target independence/regret bound, no source-package/chapter/Goal acceptance. Build/fence/trial evidence separate.')
write(RUN / 'leaf-progress-I001-v2.json', dict(contract_version=2, contract_targets=8, closed=[targets[0]['name']],
    remaining=[row['name'] for row in targets[1:]], public_sha256=sha(PUBLIC), package_accepted=False, chapter_complete=False, goal_complete=False))
headers_fixed(1)
print('Actual I001 body compiled; seven fixed targets remain, package not accepted.')
