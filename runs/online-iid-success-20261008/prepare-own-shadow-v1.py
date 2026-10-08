from common_integrated_v1 import *
fixed_integrated()
native('canary-compiled-trial-v1','trial-log','--task',TASK,'--role','lower','--kind','build','--status','compiled',
    '--run-id',RUN.name,'--lean',CANARY,'--attempt-id','SUCCESS-CANARY-V1','--harness','hierarchical',
    '--verifier-evidence',RUN/'canary-focused-build-v1-exit.json','--progress-class','compiled-leaf',
    '--notes','Actual14nondegeneratecanaryproofs/2fixtures; trueunknown-lawmeanPredict success withpositivefiniteexcess, persistentprivate-bitT/4nonsuccess, correlatednegativeexcess andzero-horizon/genericnonzeroinitial boundary. Header/kernel/VALUE audits passed; FINAL/site/package pending.')
trials=[json.loads(s) for s in Path('runs/trials.jsonl').read_text(encoding='utf8').splitlines() if s.strip()]
trials=[t for t in trials if t.get('task')==TASK]
assert trials
write(RUN/'candidate-scoped-trials-v1.jsonl','\n'.join(json.dumps(r,ensure_ascii=False) for r in trials))
for cmd in ['frontier-refresh','frontier-shadow']:
    native(cmd+'-help-v1',cmd,'--help')
terminal=load(CONTRACT/'targets-v1.json')['targets'][3]
native('candidate-frontier-refresh-v1','frontier-refresh','--root-objective',
    'Persistent Orabona Chapters1–16; bounded C1 expectedfixed stochastic success andactualmeanPredict',
    '--leaf',TASK,'--kind','lean','--statement',terminal['header'],'--declaration',terminal['name'],'--file',PUBLIC,
    '--source-status','source-reviewed','--leaf-status','gate-pending',
    '--dependency','review:source-body:accepted','--dependency','lean:'+PRE+'meanPredict_expectedFixed_upper:compiled',
    '--dependency','lean:'+PRE+'centered_total_sublinear_iff_average:compiled',
    '--trials',RUN/'candidate-scoped-trials-v1.jsonl','--output',RUN/'candidate-frontier-v1.json','--shadow-status','pending')
native('candidate-frontier-shadow-v1','frontier-shadow','--trials',RUN/'candidate-scoped-trials-v1.jsonl',
    '--memory-digest',RUN/'memory-digest-candidate-v1.md','--frontier',RUN/'candidate-frontier-v1.json')
fixed_integrated()
prior=Path('tmp/online-randomized-iid-site-v3/books/registry.json')
old=load(prior)
assert len(old['nodes'])==10931
write(RUN/'registry-base-snapshot-v1.json',prior.read_bytes())
write(RUN/'registry-base-provenance-v1.json',dict(path=prior.as_posix(),sha256=sha(prior),
    prior_source_commit=old['source_commit'],prior_nodes=len(old['nodes']),
    use='oldsharednodeID/URL/statementhash preservation only; notnewpackageproof or liveevidence'))
print('Own boundedcandidate shadow passed; globalSGB unchanged; old10931 registry preserved baseline only.')
