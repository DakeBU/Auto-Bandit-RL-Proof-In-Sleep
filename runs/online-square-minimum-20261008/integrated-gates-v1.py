from common_integrated_v1 import *

fixed_integrated()
# Stage actual new production paths so the diff-aware contributor gate is nonvacuous.
gate('stage-owned-public-tests-manifest-v1', 'git', '-c', 'core.autocrlf=false', 'add', '--', PUBLIC, CANARY, MANIFEST)
baseline = Path('tmp/online-no-regret-site-v1/books/registry.json')
assert len(load(baseline)['nodes']) == 10906
write(RUN / 'registry-base-snapshot-v1.json', baseline.read_bytes())
trials = [json.loads(line) for line in Path('runs/trials.jsonl').read_text(encoding='utf8').splitlines() if line.strip()]
trials = [x for x in trials if x.get('task') == TASK]
assert trials
write(RUN / 'candidate-scoped-trials-v1.jsonl', '\n'.join(json.dumps(x, ensure_ascii=False) for x in trials))
terminal = load(CONTRACT / 'targets-v1.json')['rows'][-1]
native('candidate-frontier-refresh-v1', 'frontier-refresh', '--root-objective',
    'Persistent Orabona Chapters1–16; actual pathwise square-loss minimum and same FTL guarantee',
    '--leaf', TASK, '--kind', 'lean', '--statement', terminal['header'], '--declaration', terminal['name'], '--file', PUBLIC,
    '--source-status', 'source-reviewed', '--leaf-status', 'gate-pending', '--dependency', 'review:source-body:accepted',
    '--dependency', 'lean:' + PRE + 'squaredLoss_minimum_eq:compiled', '--dependency', 'lean:' + PRE + 'meanPredict_regret_refined:compiled',
    '--trials', RUN / 'candidate-scoped-trials-v1.jsonl', '--output', RUN / 'candidate-frontier-v1.json', '--shadow-status', 'pending')
native('candidate-frontier-shadow-v1', 'frontier-shadow', '--trials', RUN / 'candidate-scoped-trials-v1.jsonl',
    '--memory-digest', RUN / 'memory_digest-candidate-v1.md', '--frontier', RUN / 'candidate-frontier-v1.json')
gate('combined-root-v1', 'lake', 'build')
gate('combined-Tests-v1', 'lake', 'build', 'Tests')
native('full-harness-v1', 'check')
gate('contributor-exact-base-v1', sys.executable, '-B', '-X', 'utf8', 'tools/check_contributor_contract.py', '--base', BASE)
write(RUN / 'integrated-gates-v1.json', dict(status='Actual combined root/Tests/full harness/own shadow/nonvacuous exact-base contributor passed',
    root_log_sha256=sha(RUN / 'combined-root-v1.log'), Tests_log_sha256=sha(RUN / 'combined-Tests-v1.log'),
    harness_log_sha256=sha(RUN / 'full-harness-v1.log'), public_sha256=sha(PUBLIC), canary_sha256=sha(CANARY),
    globalSGB_unchanged=True, clean_site_FINAL_native_PR_pending=True, chapter_complete=False, goal_complete=False))
fixed_integrated()
print('Combined shared library gates passed; clean site/FINAL/native/PR remain.')
