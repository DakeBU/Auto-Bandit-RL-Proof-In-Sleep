from common_integrated_v2 import *
from commit_owned_v2 import current_owned_paths, commit_owned

fixed_integrated()
assert load(RUN/'reader-semantic-repair-v9.json')['no_mathematical_repair_or_terminal_weakening']
paths = current_owned_paths()
globals_ = {'MANIFEST.md', 'runs/trials.jsonl', 'runs/lifecycle_sessions.jsonl', 'runs/lifecycle_memory.jsonl'}
assert not (set(paths) & globals_)
for start in range(0, len(paths), 48):
    child = subprocess.run(['git', '-c', 'core.autocrlf=false', 'add', '--']+paths[start:start+48], stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    assert child.returncode == 0
for p in paths:
    assert subprocess.check_output(['git', 'show', ':'+p]) == Path(p).read_bytes()
gate('scoped-diff-reader-repair-v9', sys.executable, '-B', '-X', 'utf8', RUN/'check-scoped-diff-v7.py', 'reader-repair-v9')
commit_owned('Repair the IID reader min-expectation wording and positive-time formula')
