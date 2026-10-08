from common_reviewed_v1 import *

headers_fixed(1)
assert load(RUN / 'first-leaf-focused-build-v1-exit.json')['exit_code'] == 0
targets = load(CONTRACT / 'targets-v1.json')['rows']
bodies = [
''' := by
  have hm := guessing_prefix_minimum y T hy
  have hleast : IsLeast
      ((fun u : ℝ => ∑ t ∈ Finset.range T, (u - y t)^2) '' Set.Icc (0 : ℝ) 1)
      (∑ t ∈ Finset.range T, (empiricalMean y T - y t)^2) := by
    constructor
    · exact ⟨empiricalMean y T, hm.1, rfl⟩
    · rintro a ⟨u, hu, rfl⟩
      exact hm.2 u hu
  exact hleast.csInf_eq

''',
''' := by
  unfold squaredBestRegret comparatorRegret
  rw [squaredLoss_minimum_eq y T hy]

''',
''' := by
  rw [squaredBestRegret_eq_comparatorRegret y prediction T hy]
  unfold comparatorRegret
  exact sub_le_sub_left ((guessing_prefix_minimum y T hy).2 u hu) _

''',
''' := by
  rw [squaredBestRegret_eq_comparatorRegret y (meanPredict y) T hy]
  simpa only [comparatorRegret] using theorem_1_3 y T hT hy

''',
''' := by
  rw [squaredBestRegret_eq_comparatorRegret y (meanPredict y) T hy]
  simpa only [comparatorRegret] using meanPredict_regret_refined y T hT hy

''']
comments = [
    'The actual least element is in the interval-loss image; no minimizer is assumed.',
    'Signed pathwise minimum regret equals regret at the produced empirical mean.',
    'Any feasible fixed comparator gives regret at most the same-horizon minimum regret.',
    'Orabona v10 Theorem 1.3, now expressed against the actual interval minimum.',
    'Printed p5 intermediate bound: initial half and source rounds 2..T preserved.']
before = PUBLIC.read_bytes()
write(RUN / 'snapshots' / 'first-leaf-public-v1.raw', before)
native('remaining-worker-running-v1', 'trial-log', '--task', TASK, '--role', 'lower', '--kind', 'attempt', '--status', 'running',
    '--run-id', RUN.name, '--lean', PUBLIC, '--attempt-id', 'SQUARE-MINIMUM-M002-M006-V1', '--harness', 'hierarchical',
    '--target-fingerprint', sha(CONTRACT / 'targets-v1.json'), '--notes',
    'Single dependency-ready route: actual IsLeast from M001, imported csInf_eq, same-trace identity/order, then existing actual FTL guarantees. No assumed minimizer/regret certificates or type edits.')
text = PUBLIC.read_text(encoding='utf8')
assert text.endswith('end BanditRL.OnlineLearning\n')
text = text[:-len('end BanditRL.OnlineLearning\n')]
for row, body, comment in zip(targets[1:], bodies, comments):
    text += '/-- ' + comment + ' -/\n' + row['header'] + body
text += 'end BanditRL.OnlineLearning\n'
PUBLIC.write_bytes(text.encode('utf8'))
headers_fixed(6)
gate('all-six-focused-build-v1', 'lake', 'build', 'BanditRLProof.OnlineSquareMinimum')
for row in targets[1:]:
    stem = row['id'] + '-v1'
    native(stem + '-fence', 'statement-fence', '--declaration', row['name'], '--file', PUBLIC, '--output', RUN / (stem + '-fence.json'))
    native(stem + '-safe-verify', 'safe-verify', '--fence', RUN / (stem + '-fence.json'), '--lean-file', PUBLIC)
native('remaining-worker-compiled-v1', 'trial-log', '--task', TASK, '--role', 'lower', '--kind', 'build', '--status', 'compiled',
    '--run-id', RUN.name, '--lean', PUBLIC, '--attempt-id', 'SQUARE-MINIMUM-M002-M006-V1', '--harness', 'hierarchical',
    '--target-fingerprint', sha(CONTRACT / 'targets-v1.json'), '--new-declaration', targets[-1]['name'],
    '--verifier-evidence', RUN / 'all-six-focused-build-v1-exit.json', '--progress-class', 'closed-frontier',
    '--obligations-before', '5', '--obligations-after', '0', '--notes',
    'Only the six frozen square-minimum math terminals close in focused build. Source BODY/canary/kernel/root/Tests/full harness/reader/site/native/PR acceptance still required; original C1 total unknown and total Goal active.')
write(RUN / '30_worker-M002-M006-v1.md', 'Actual M002 produces IsLeast including membership and lower-bound proofs, then imports generic csInf_eq. M003/M004 preserve signed same-prefix quantities and arbitrary supplied traces. M005/M006 instantiate the existing actual first-half strict-past strategy and exact rate/sharp-tail bodies. All six fixed headers unchanged and actual focused build passed. Package acceptance is pending.')
write(RUN / 'leaf-progress-v2.json', dict(contract_targets=6, closed=[x['name'] for x in targets], remaining=[],
    public_sha256=sha(PUBLIC), focused_build='all-six-focused-build-v1-exit.json',
    package_accepted=False, chapter_complete=False, goal_complete=False))
headers_fixed(6)
print('All six fixed public bodies actually compile; package and chapter gates remain.')
