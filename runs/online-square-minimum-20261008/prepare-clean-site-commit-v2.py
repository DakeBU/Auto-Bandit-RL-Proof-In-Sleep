from common_integrated_v1 import *

fixed_integrated()
for label in ['combined-root-v1', 'combined-Tests-v1', 'full-harness-v1']:
    assert load(RUN / (label + '-exit.json'))['exit_code'] == 0
assert load(RUN / 'pre-source-full-diff-v1-exit.json')['actual_exit_code'] != 0
write(RUN / 'delivery-check-repair-v2.json', dict(
    preserved_failed_script_sha256=sha(RUN / 'prepare-clean-site-commit-v1.py'),
    preserved_failed_diff_log_sha256=sha(RUN / 'pre-source-full-diff-v1.log'),
    preserved_failed_diff_receipt_sha256=sha(RUN / 'pre-source-full-diff-v1-exit.json'),
    original_contributor_receipt_sha256=sha(RUN / 'contributor-exact-base-v1-exit.json'),
    original_contributor_log_sha256=sha(RUN / 'contributor-exact-base-v1.log'),
    original_contributor_is_vacuous=True, original_affected_production_paths=0, original_changed_contracts=0,
    repair='Preserve immutable decoder output and exact compiler/failed-check stdout; five individually hashed raw-evidence whitespace exceptions only. After scoped source commit run the actual committed-diff contributor gate and require five production paths/one contract.',
    math_types_readers_sources_not_edited=True, combined_root_Tests_harness_pass_remains_actual=True,
    committed_contributor_pending=True, chapter_complete=False, goal_complete=False))
exceptions = []
for name, reason in [
    ('blind-reconstruction-v1.md', 'Independent decoder raw report has blank EOF; CONTRACT/BODY receipt hashes must remain exact.'),
    ('combined-root-v1.log', 'Actual Lean diagnostic stdout contains source whitespace; preserve exact verifier evidence.'),
    ('combined-Tests-v1.log', 'Actual Lean diagnostic stdout contains source whitespace; preserve exact verifier evidence.'),
    ('full-harness-v1.log', 'Actual full harness stdout includes original Lean diagnostics; preserve exact verifier evidence.'),
    ('pre-source-full-diff-v1.log', 'Actual failed whitespace-check stdout quotes the original diagnostic whitespace.')]:
    p = RUN / name
    exceptions.append(dict(path=p.relative_to(ROOT).as_posix(), sha256=sha(p), reason=reason))
write(RUN / 'diff-raw-evidence-exceptions-v2.json', dict(exceptions=exceptions, scope='Only five exact preserved evidence files; all production/readers/contracts/helpers remain checked.'))
gate('scope-before-source-commit-v2', sys.executable, '-B', '-X', 'utf8', RUN / 'audit-scope-v2.py', 'before-source-commit-v2')
paths = load(RUN / 'owned-paths-before-source-commit-v2.json')['paths']
globals = ['MANIFEST.md', 'runs/trials.jsonl', 'runs/lifecycle_sessions.jsonl', 'runs/lifecycle_memory.jsonl']
exact_owned = [p for p in paths if p not in globals]
for offset in range(0, len(exact_owned), 48):
    child = subprocess.run(['git', '-c', 'core.autocrlf=false', 'add', '--', *exact_owned[offset:offset+48]], stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    assert child.returncode == 0, child.stdout.decode('utf8', errors='replace')
changed_globals = [p for p in paths if p in globals]
child = subprocess.run(['git', 'add', '--', *changed_globals], stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
assert child.returncode == 0
for p in exact_owned: assert subprocess.check_output(['git', 'show', ':' + p]) == Path(p).read_bytes(), p
for p in changed_globals:
    assert subprocess.check_output(['git', 'show', ':' + p]).startswith(subprocess.check_output(['git', 'show', BASE + ':' + p])), p
command = ['git', '-c', 'core.whitespace=blank-at-eol,blank-at-eof,space-before-tab,cr-at-eol', 'diff', '--check', BASE, '--', '.',
    *[':(exclude)' + r['path'] for r in exceptions]]
for row in exceptions: assert sha(row['path']) == row['sha256']
child = subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
write(RUN / 'pre-source-full-diff-v2.log', child.stdout)
write(RUN / 'pre-source-full-diff-v2-exit.json', dict(command=command, actual_exit_code=child.returncode,
    log_sha256=sha(RUN / 'pre-source-full-diff-v2.log'), exact_raw_evidence_exceptions=exceptions,
    all_production_readers_contracts_helpers_checked=True))
assert child.returncode == 0, child.stdout.decode('utf8', errors='replace')
child = subprocess.run(['git', '-c', 'core.autocrlf=false', 'add', '--', str(RUN / 'pre-source-full-diff-v2.log'),
    str(RUN / 'pre-source-full-diff-v2-exit.json')], stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
assert child.returncode == 0
child = subprocess.run(['git', 'commit', '-m', 'Produce the attained square-loss minimum and actual FTL best regret'], stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
sys.stdout.write('\n'.join(child.stdout.decode('utf8', errors='replace').splitlines()[-8:]) + '\n')
assert child.returncode == 0
assert not subprocess.check_output(['git', 'status', '--porcelain', '--untracked-files=all'], text=True).strip()
print('Clean source commit', subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip())
