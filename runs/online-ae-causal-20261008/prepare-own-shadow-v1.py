from common_body_v1 import *
fixed_integrated()
trials=[json.loads(line) for line in (ROOT/'runs/trials.jsonl').read_text(encoding='utf8').splitlines() if line.strip()]
own=[t for t in trials if t.get('task')==TASK]
assert own and all(t.get('task')==TASK for t in own)
write(RUN/'candidate-scoped-trials-v1.jsonl','\n'.join(json.dumps(t,ensure_ascii=False) for t in own))
write(RUN/'memory-digest-candidate-v2.md','Task: `'+TASK+'`\n\n'+
    (RUN/'memory-digest-candidate-v1.md').read_text(encoding='utf8')+
    '\nDistinct actual BODY236 accepted-with-explicit-delta, immutable public/canary bytes and exact R1-R6. Root/site integration is precise and prospectively approved; full combined/site/FINAL/native gates still required.\n')
native('candidate-frontier-refresh-v1','frontier-refresh','--root-objective',
    'Persistent Orabona Chapters1-16; three derived AE causal producers, whole program required',
    '--leaf',TASK,'--kind','theorem','--statement',
    'Three frozen AE causal public proofs compiled, actual original-process expected fixed excess and AE-only positive-variance canary; acceptance still awaits combined/reader/FINAL/native gates.',
    '--file',PUBLIC.relative_to(ROOT).as_posix(),'--source-status','source-reviewed','--leaf-status','gate-pending',
    '--dependency','review:source-body:accepted',
    '--dependency','lean:BanditRL.OnlineLearning.ae_predictable_private_seed_expectedFixed_excess:compiled',
    '--trials',RUN/'candidate-scoped-trials-v1.jsonl','--output',RUN/'candidate-frontier-v1.json','--shadow-status','pending')
native('candidate-frontier-shadow-v1','frontier-shadow','--trials',RUN/'candidate-scoped-trials-v1.jsonl',
    '--memory-digest',RUN/'memory-digest-candidate-v2.md','--frontier',RUN/'candidate-frontier-v1.json')
fixed_integrated()
print('Own AE candidate shadow passed; original global SGB frontier unchanged.',flush=True)
