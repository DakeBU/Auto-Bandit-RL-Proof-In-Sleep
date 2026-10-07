"""Task-scoped shadow; global SGB and all source targets remain frozen."""
from common_v1 import *
fixed(True);passed('project-gates-v1-01')
rows=[json.loads(s) for s in Path('runs/trials.jsonl').read_text(encoding='utf-8').splitlines() if s.strip()]
write(RUN/'candidate-scoped-trials-v1.jsonl','\n'.join(json.dumps(t) for t in rows if t.get('task')==TASK))
write(RUN/'memory-digest-candidate-v1.md','Actual existing21 public proofs/whole74canary proofs,122 named kernel checks/21 frozen guards/32 actual VALUE pairs. Current distinct CONTRACT/BODY and combined root/Tests/full harness pass. Zero new math proofs/defs/maintext closures/registry nodes. GlobalSGB/old targets/otherBooks/pins unchanged. Required Example2.32/linearization/unitanalysis/remainingmaintext/appendices remain. FINAL/site/native/PR pending; wholeGoal ACTIVE unbudgeted.')
sys.path.insert(0,str(ROOT));from tools.abrl_lifecycle import lean_declaration_header
native('candidate-frontier-refresh-v1','frontier-refresh','--root-objective','Persistent Orabona Chapters1-16; existing finite-history OSD current public reuse audit only','--leaf',TASK,'--kind','lean','--statement',lean_declaration_header(PUBLIC,'regret_tuned'),'--declaration',PRE+'regret_tuned','--file',PUBLIC,'--source-status','source-reviewed','--leaf-status','gate-pending','--dependency','lean:'+PRE+'regret_tuned_distance:compiled','--dependency','lean:'+PRE+'regret_fixed:compiled','--trials',RUN/'candidate-scoped-trials-v1.jsonl','--output',RUN/'candidate-frontier-v1.json','--shadow-status','pending')
native('candidate-frontier-shadow-v1','frontier-shadow','--trials',RUN/'candidate-scoped-trials-v1.jsonl','--memory-digest',RUN/'memory-digest-candidate-v1.md','--frontier',RUN/'candidate-frontier-v1.json')
fixed(True);print('Actual own candidate shadow passes; global SGB unchanged.')
