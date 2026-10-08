from common_integrated_v1 import *

fixed_integrated()
assert load(RUN / 'integrated-gates-v1.json')['status'].startswith('Actual combined')
native_globals = ['MANIFEST.md', 'runs/trials.jsonl', 'runs/lifecycle_sessions.jsonl', 'runs/lifecycle_memory.jsonl']
gate('scope-before-source-commit-v1', sys.executable, '-B', '-X', 'utf8', RUN / 'audit-scope-v2.py', 'before-source-commit-v1')
paths = load(RUN / 'owned-paths-before-source-commit-v1.json')['paths']
exact_owned = [p for p in paths if p not in native_globals]
# Bind new task evidence to exact raw bytes from the outset; no global config or inherited-file renormalization.
for offset in range(0, len(exact_owned), 48):
    child = subprocess.run(['git', '-c', 'core.autocrlf=false', 'add', '--', *exact_owned[offset:offset+48]], stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    assert child.returncode == 0, child.stdout.decode('utf8', errors='replace')
changed_globals = [p for p in paths if p in native_globals]
child = subprocess.run(['git', 'add', '--', *changed_globals], stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
assert child.returncode == 0, child.stdout.decode('utf8', errors='replace')
for p in exact_owned:
    staged = subprocess.check_output(['git', 'show', ':' + p])
    assert staged == Path(p).read_bytes(), p
for p in changed_globals:
    base_git = subprocess.check_output(['git', 'show', BASE + ':' + p])
    staged = subprocess.check_output(['git', 'show', ':' + p])
    assert staged.startswith(base_git), p
diff_command = ['git', '-c', 'core.whitespace=blank-at-eol,blank-at-eof,space-before-tab,cr-at-eol', 'diff', '--check', BASE]
child = subprocess.run(diff_command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
write(RUN / 'pre-source-full-diff-v1.log', child.stdout)
write(RUN / 'pre-source-full-diff-v1-exit.json', dict(command=diff_command, actual_exit_code=child.returncode,
    log_sha256=sha(RUN / 'pre-source-full-diff-v1.log'), staged_all_owned_paths=True))
assert child.returncode == 0, child.stdout.decode('utf8', errors='replace')
child = subprocess.run(['git', '-c', 'core.autocrlf=false', 'add', '--',
    str(RUN / 'pre-source-full-diff-v1.log'), str(RUN / 'pre-source-full-diff-v1-exit.json')], stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
assert child.returncode == 0
child = subprocess.run(['git', 'commit', '-m', 'Produce the attained square-loss minimum and actual FTL best regret'], stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
sys.stdout.write('\n'.join(child.stdout.decode('utf8', errors='replace').splitlines()[-8:]) + '\n')
assert child.returncode == 0
assert not subprocess.check_output(['git', 'status', '--porcelain', '--untracked-files=all'], text=True).strip()
print('Clean scoped source commit', subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip())
