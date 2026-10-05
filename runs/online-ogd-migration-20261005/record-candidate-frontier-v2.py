"""Task-local native frontier, leaving the historical global SGB pointer unchanged."""
from pathlib import Path
import hashlib,json,subprocess,sys
run=Path(__file__).parent;task='ONLINE-OGD-MIGRATION-20261005'
def gate(label,*args):subprocess.run([sys.executable,'-X','utf8',str(run/'run-command.py'),label,*args],check=True)
trials=[json.loads(s) for s in Path('runs/trials.jsonl').read_text(encoding='utf-8').splitlines() if s.strip()]
with (run/'candidate-scoped-trials-v2.jsonl').open('w',encoding='utf-8',newline='\n') as f:
    for t in trials:
        if t.get('task')==task:f.write(json.dumps(t)+'\n')
d=json.loads((run/'public-actual-bindings-v2.json').read_text(encoding='utf-8'))
gate('candidate-frontier-refresh-v2',sys.executable,'-X','utf8','tools/bandit.py','frontier-refresh',
    '--root-objective','Persistent Orabona Chapters1-16 Goal; OGD source repair candidate only, Chapter2/book incomplete',
    '--leaf',task,'--kind','lean','--statement',d['public_headers']['theorem_2_13_fixed'],
    '--declaration','BanditRL.OnlineGradientDescentSource.theorem_2_13_fixed',
    '--file','BanditRLProof/OnlineGradientDescentSource.lean','--source-status','source-body-reviewed',
    '--leaf-status','gate-pending','--dependency','lean:BanditRL.OnlineGradientDescentSource.lemma_2_12:compiled',
    '--dependency','lean:BanditRL.OnlineGradientDescentSource.source_to_feasible:compiled',
    '--dependency','review:source-body:accepted','--trials',str(run/'candidate-scoped-trials-v2.jsonl'),
    '--output',str(run/'candidate-frontier-v2.json'),'--shadow-status','pending')
gate('candidate-frontier-shadow-v2',sys.executable,'-X','utf8','tools/bandit.py','frontier-shadow',
    '--trials',str(run/'candidate-scoped-trials-v2.jsonl'),'--memory-digest',str(run/'memory-digest-candidate-v2.md'),
    '--frontier',str(run/'candidate-frontier-v2.json'))
assert hashlib.sha256(Path('runs/active_frontier.json').read_bytes()).hexdigest()=='567e5873aa2549a83f2820d758069213808da822a93087129877385a1addf7c3'
print('Task-local native frontier and shadow recorded; global SGB unchanged.')
