from common_integrated_v2 import *
from commit_owned_v2 import current_owned_paths

fixed_integrated()
old = load(RUN / 'diff-raw-bound-exceptions-v4.json')['exceptions']
assert len(old) == 7
for row in old:
    assert sha(row['path']) == row['sha256']

def stage_owned():
    paths = current_owned_paths()
    globals_ = {'MANIFEST.md', 'runs/trials.jsonl', 'runs/lifecycle_sessions.jsonl', 'runs/lifecycle_memory.jsonl'}
    assert not (set(paths) & globals_), 'No native metadata mutation is needed for this repair.'
    for start in range(0, len(paths), 48):
        child = subprocess.run(['git', '-c', 'core.autocrlf=false', 'add', '--'] + paths[start:start+48], stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        assert child.returncode == 0, child.stdout.decode('utf8', errors='replace')
    for p in paths:
        assert subprocess.check_output(['git', 'show', ':'+p]) == Path(p).read_bytes(), p

command = ['git', '-c', 'core.whitespace=blank-at-eol,blank-at-eof,space-before-tab,cr-at-eol', 'diff', '--check', BASE, '--', '.']
stage_owned()
first = subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
assert first.returncode == 2, first.returncode
write(RUN / 'pre-FINAL-full-diff-v7.log', first.stdout)
write(RUN / 'pre-FINAL-full-diff-v7-exit.json', dict(command=command, exit_code=first.returncode,
    log_sha256=sha(RUN / 'pre-FINAL-full-diff-v7.log'), full_unexcluded_check_passed=False))
stage_owned()
second = subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
assert second.returncode == 2
stdout = second.stdout.decode('utf8', errors='strict')
findings = sorted({line.split(':', 1)[0] for line in stdout.splitlines() if line.startswith(RUN.relative_to(ROOT).as_posix()+'/') and ': ' in line})
prefix = RUN.relative_to(ROOT).as_posix()+'/'
old_paths = {r['path'] for r in old}
allowed_new = {prefix+f for f in ['current-reader-capture-v2.log', 'overflow-diagnostic-helper-v3.log',
    'current-reader-capture-v4.log', 'overflow-diagnostic-helper-v5.log', 'current-reader-capture-v6.log',
    'pre-FINAL-full-diff-v7.log']}
assert old_paths <= set(findings), (old_paths-set(findings))
assert set(findings) <= old_paths | allowed_new, (set(findings)-old_paths-allowed_new, stdout)
new = [dict(path=p, sha256=sha(p), reason='Exact actual browser/failure-check stdout; only recorded whitespace, original bytes retained.')
    for p in findings if p not in old_paths]
write(RUN / 'diff-raw-bound-exceptions-v7.json', dict(exceptions=old+new, actual_full_check_findings=stdout,
    exact_individually_bound_files=len(old)+len(new), original_v4_seven_unchanged=True,
    full_unexcluded_check_exit_code=second.returncode, full_unexcluded_check_passed=False,
    two_frozen_helper_EOF_findings_require_distinct_FINAL_judgment=True,
    no_production_test_reader_contract_or_other_helper_exception=True, chapter_complete=False, goal_complete=False))
write(RUN / 'whitespace-evidence-repair-v7.json', dict(status='Exact raw-evidence exception extension; scoped gate still separate.',
    source_commit_after_failed_layout_diff='af28b5d586c8d1e6cf4d5a901466050356e6ab6d',
    original_pre_status_diff_exit=2,
    original_findings=['current-reader-capture-v2.log blank EOF', 'overflow-diagnostic-helper-v3.log blank EOF'],
    diagnosis='The local reversible layout/evidence commit occurred after this failed whitespace check. It was not a passing check; no mathematical or semantic gate is inferred.',
    original_failed_stdout_and_commit_retained=True, all_math_body_source_header_bindings_unchanged=True,
    individually_bound_exception_count=len(old)+len(new), full_unexcluded_diff_passed=False,
    scoped_diff_pending=True, FINAL_pending=True, package_accepted=False, chapter_complete=False, goal_complete=False))
stage_owned()
print('Actual unexcluded exit2; exact individually hashed evidence findings:', len(old)+len(new))
