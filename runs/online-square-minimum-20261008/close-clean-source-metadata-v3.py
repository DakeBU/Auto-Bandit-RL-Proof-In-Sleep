from common_integrated_v1 import *

fixed_integrated()
assert load(RUN / 'integrated-gates-v2.json')['affected_production_paths'] == 5
source_commit = subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip()
assert source_commit == '00186126e1c75b5f5222e0355f8c1c34beaaf4c0'
write(RUN / 'clean-source-tail-repair-v3.json', dict(source_commit=source_commit, source_commit_succeeded=True,
    failed_helper_sha256=sha(RUN / 'prepare-clean-site-commit-v2.py'), observed_actual_exit_code=1,
    failed_stage='Post-commit clean-tree assertion',
    cause='The scope helper produced owned-paths and its outer gate produced an exit receipt after the path collection; these two new owned metadata files were not staged.',
    exact_two_original_tail_paths=['owned-paths-before-source-commit-v2.json', 'scope-before-source-commit-v2-exit.json'],
    repair='Commit only remaining task-owned operational evidence and actual nonvacuous contributor receipt; no source/public/canary/reader edits.',
    mathematical_gate_rerun_needed=False, package_accepted=False, chapter_complete=False, goal_complete=False))
paths = [line[3:] for line in subprocess.check_output(['git', 'status', '--porcelain', '--untracked-files=all'], text=True).splitlines()]
assert paths and all(p.startswith(RUN.relative_to(ROOT).as_posix() + '/') for p in paths), paths
assert all(Path(p).suffix in ['.json', '.log', '.py'] for p in paths), paths
for offset in range(0, len(paths), 48):
    child = subprocess.run(['git', '-c', 'core.autocrlf=false', 'add', '--', *paths[offset:offset+48]], stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    assert child.returncode == 0
for p in paths: assert subprocess.check_output(['git', 'show', ':' + p]) == Path(p).read_bytes(), p
child = subprocess.run(['git', 'commit', '-m', 'Record the committed contributor gate and clean source receipt'], stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
sys.stdout.write('\n'.join(child.stdout.decode('utf8', errors='replace').splitlines()[-8:]) + '\n')
assert child.returncode == 0
assert not subprocess.check_output(['git', 'status', '--porcelain', '--untracked-files=all'], text=True).strip()
fixed_integrated()
print('Actual clean source head', subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip())
