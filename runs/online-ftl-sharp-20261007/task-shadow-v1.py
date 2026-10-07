from common_v1 import *
fixed(proving=True,integrated=True)
trials=[json.loads(s) for s in Path('runs/trials.jsonl').read_text(encoding='utf-8').splitlines() if s.strip()]
own=[t for t in trials if t.get('task')==TASK];assert own and {'compiled','failed'}<={t['status'] for t in own}
write(RUN/'candidate-scoped-trials-v1.jsonl','\n'.join(json.dumps(t) for t in own))
write(RUN/'memory-digest-candidate-v1.md','Persistent Chapters1-16 ACTIVE. Current FTL two frozen source bounds compiled; old5proof1def intact, six named tests/one testdef. CONTRACT repair/BODY accepted; actual15kernel/13rfl/13guards/9VALUE2401refs. Metadata/ledger/path/snapshot/CLI failures preserved, no source target weakening. Chapter1 required16 sourceitems but proof totalnull/generalinit/streaming/WV/loglower open; eight other main-relative gaps inclFoundations unwaived pendingactualcheck;Chapter2null,3–16unenumerated/requiredappendices. Site/pixels/FINAL/native/PRpending, no merge/live.')
statement=load(RUN/'native-public-fences/meanPredict_regret_refined-v1.json')['statement']
native('candidate-frontier-refresh-v1','frontier-refresh','--root-objective','Persistent Orabona Chapters1–16; current FTL first-round and exact-tail proof package','--leaf',TASK,'--kind','lean','--statement',statement,'--declaration',PRE+'meanPredict_regret_refined','--file',PUBLIC,'--source-status','source-reviewed','--leaf-status','gate-pending','--dependency','lean:'+PRE+'meanPredict_initial_stability:compiled','--dependency','lean:'+PRE+'meanPredict_stability:compiled','--dependency','review:source-body:accepted','--trials',RUN/'candidate-scoped-trials-v1.jsonl','--output',RUN/'candidate-frontier-v1.json','--shadow-status','pending')
native('candidate-frontier-shadow-v1','frontier-shadow','--trials',RUN/'candidate-scoped-trials-v1.jsonl','--memory-digest',RUN/'memory-digest-candidate-v1.md','--frontier',RUN/'candidate-frontier-v1.json')
shadow=json.loads((RUN/'candidate-frontier-shadow-v1.log').read_text(encoding='utf-8'));assert not shadow['mismatches'] and not shadow['would_mutate']
fixed(proving=True,integrated=True)
