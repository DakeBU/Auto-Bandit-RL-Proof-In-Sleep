from common_integrated_v1 import *

fixed_integrated()
owned_metadata = [folder + '/' + TASK + '.md' for folder in ['tasks', 'conversion-windows', 'proof-obligations', 'proof-blueprints', 'research-wiki/retrieval-index']]
globals = ['MANIFEST.md', 'runs/trials.jsonl', 'runs/lifecycle_sessions.jsonl', 'runs/lifecycle_memory.jsonl']
integration = ['BanditRLProof.lean', 'Tests.lean', 'website/content/readings.json', 'website/content/highlights.json', 'website/content/chapters.json']
singletons = set(owned_metadata + globals + integration + [PUBLIC.as_posix(), CANARY.as_posix(), MANIFEST.as_posix()])
prefixes = [RUN.relative_to(ROOT).as_posix() + '/', CONTRACT.as_posix() + '/']
status = subprocess.check_output(['git', 'status', '--porcelain', '--untracked-files=all'], text=True)
paths = sorted(set(line[3:] for line in status.splitlines()))
for p in paths:
    assert p in singletons or any(p.startswith(prefix) for prefix in prefixes), 'Unowned dirty file: ' + p
assert subprocess.check_output(['git', 'branch', '--show-current'], text=True).strip() == BRANCH
assert subprocess.check_output(['git', 'merge-base', 'HEAD', BASE], text=True).strip() == BASE
global_bindings = []
for p in globals:
    baseline = (RUN / 'snapshots' / (p.replace('/', '--') + '.raw')).read_bytes()
    current = Path(p).read_bytes()
    assert current.startswith(baseline), p
    addition = current[len(baseline):]
    if p.endswith('.jsonl'):
        rows = [json.loads(line) for line in addition.decode('utf8').splitlines() if line.strip()]
        for row in rows:
            assert row.get('task', row.get('session_id')) == TASK, (p, row)
    else:
        lines = [line for line in addition.decode('utf8').splitlines() if line.strip()]
        assert len(lines) == 8 and all(RUN.name in line and 'native-reference-index' in line for line in lines), p
    git_old = subprocess.check_output(['git', 'show', BASE + ':' + p])
    global_bindings.append(dict(path=p, working_original_sha256=hashlib.sha256(baseline).hexdigest(),
        working_original_bytes=len(baseline), current_working_sha256=sha(p), working_append_sha256=hashlib.sha256(addition).hexdigest(),
        base_git_original_sha256=hashlib.sha256(git_old).hexdigest(), base_git_original_bytes=len(git_old),
        representations_are_separate=True, historical_prefix_preserved=True, owned_append_only=True))
label = sys.argv[1]
write(RUN / ('owned-paths-' + label + '.json'), dict(paths=paths, current_globals=global_bindings,
    private_main_canonical_other_worktrees_untouched=True, current_task_owns_checkout=True, worktree_retained=True,
    chapter_complete=False, goal_complete=False))
print('Scope checked:', len(paths), 'owned paths; four inherited raw prefixes intact; global SGB/source/math/pins fixed.')
