from common_integrated_v2 import *
fixed_integrated()
baseline=Path('tmp/online-square-minimum-site-v1/books/registry.json')
assert len(load(baseline)['nodes'])==10913
write(RUN/'registry-base-snapshot-v2.json',baseline.read_bytes())
trials=[json.loads(line) for line in Path('runs/trials.jsonl').read_text(encoding='utf8').splitlines() if line.strip()]
trials=[r for r in trials if r.get('task')==TASK]
assert trials
write(RUN/'candidate-scoped-trials-v2.jsonl','\n'.join(json.dumps(r,ensure_ascii=False) for r in trials))
terminal=load(CONTRACT/'targets-v2.json')['rows'][5]
native('candidate-frontier-refresh-v2','frontier-refresh','--root-objective',
    'Persistent Orabona Chapters1–16; actual expected fixed minimum and deterministic strict-past causal IID core',
    '--leaf',TASK,'--kind','lean','--statement',terminal['header'],'--declaration',terminal['name'],'--file',PUBLIC,
    '--source-status','source-reviewed','--leaf-status','gate-pending','--dependency','review:source-body:accepted',
    '--dependency','lean:'+PRE+'expectedFixedMinimum_eq_variance:compiled',
    '--dependency','lean:'+PRE+'iid_cumulative_prediction_decomposition:compiled',
    '--dependency','lean:'+PRE+'meanPredict_independent:compiled',
    '--trials',RUN/'candidate-scoped-trials-v2.jsonl','--output',RUN/'candidate-frontier-v2.json','--shadow-status','pending')
native('candidate-frontier-shadow-v2','frontier-shadow','--trials',RUN/'candidate-scoped-trials-v2.jsonl',
    '--memory-digest',RUN/'memory_digest-candidate-v2.md','--frontier',RUN/'candidate-frontier-v2.json')
gate('combined-root-v2','lake','build')
gate('combined-Tests-v2','lake','build','Tests')
native('full-harness-v2','check')
write(RUN/'combined-gates-v2.json',dict(status='Actual combined root/Tests/full harness/own scoped shadow passed.',
    root_log_sha256=sha(RUN/'combined-root-v2.log'),Tests_log_sha256=sha(RUN/'combined-Tests-v2.log'),
    harness_log_sha256=sha(RUN/'full-harness-v2.log'),public_sha256=sha(PUBLIC),canary_sha256=sha(CANARY),
    contributor='Committed diff gate REQUIRED after scoped source commit; no zero-path exit accepted.',
    globalSGB_unchanged=True,site_FINAL_native_PR_pending=True,chapter_complete=False,goal_complete=False))
fixed_integrated()
print('Combined gates passed; nonvacuous committed contributor/clean site/FINAL/native/PR remain.')
