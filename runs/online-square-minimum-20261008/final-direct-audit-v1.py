from common_accepted_v1 import *

accepted_fixed()
head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], encoding='utf8').strip()
assert subprocess.check_output(['git', 'branch', '--show-current'], encoding='utf8').strip() == BRANCH
assert not subprocess.check_output(['git', 'status', '--porcelain', '--untracked-files=all'], encoding='utf8').strip()
assert subprocess.check_output(['git', 'ls-remote', 'origin', 'refs/heads/' + BRANCH], encoding='utf8').split()[0] == head
pr = json.loads(subprocess.check_output(['gh', 'api', 'repos/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/pulls/193']))
assert pr['head']['sha'] == head and pr['base']['ref'] == BASE_BRANCH and pr['draft'] and pr['state'] == 'open' and not pr['merged']
assert pr['body'].replace('\r\n', '\n').strip() == (RUN / 'prospective-pr-body-v1.md').read_text(encoding='utf8').strip()
tracked = subprocess.check_output(['git', 'ls-files', '--', RUN.relative_to(ROOT).as_posix(), CONTRACT.as_posix(), PUBLIC.as_posix(), CANARY.as_posix(),
    MANIFEST.as_posix(), *[folder + '/' + TASK + '.md' for folder in ['tasks', 'conversion-windows', 'proof-obligations', 'proof-blueprints', 'research-wiki/retrieval-index']]], encoding='utf8').splitlines()
for p in tracked:
    assert subprocess.check_output(['git', 'show', 'HEAD:' + p]) == Path(p).read_bytes(), p
globals_ = ['MANIFEST.md', 'runs/trials.jsonl', 'runs/lifecycle_sessions.jsonl', 'runs/lifecycle_memory.jsonl']
for p in globals_:
    assert Path(p).read_bytes().startswith((RUN / 'snapshots' / (p.replace('/', '--') + '.raw')).read_bytes()), p
    assert subprocess.check_output(['git', 'show', 'HEAD:' + p]).startswith(subprocess.check_output(['git', 'show', BASE + ':' + p])), p
    if p.endswith('.jsonl'):
        old = (RUN / 'snapshots' / (p.replace('/', '--') + '.raw')).read_bytes()
        for s in Path(p).read_bytes()[len(old):].decode('utf8').splitlines():
            if s.strip():
                row = json.loads(s)
                assert row.get('task', row.get('session_id')) == TASK
canonical = Path('E:/ABRL/research')
assert not subprocess.check_output(['git', '-C', str(canonical), 'status', '--porcelain', '--untracked-files=all'], encoding='utf8').strip()
print(json.dumps(dict(status='passed DIRECT; no file writes', PR=193, head=head, local_dirty=False, remote_and_REST_exact=True,
    exact_raw_tracked_files=len(tracked), four_inherited_globals_separate_raw_and_Git_prefixes_preserved=True,
    canonical_head=subprocess.check_output(['git', '-C', str(canonical), 'rev-parse', 'HEAD'], encoding='utf8').strip(),
    chapter_complete=False, goal_complete=False, merged=False, live=False, worktree_retained=True)), flush=True)
