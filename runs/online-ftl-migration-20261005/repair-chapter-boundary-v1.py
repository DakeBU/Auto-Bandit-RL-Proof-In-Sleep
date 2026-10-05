"""Retain the existing reader boundary phrase after a real full-harness failure."""
from pathlib import Path
import json,subprocess,sys
run=Path(__file__).parent;p=Path('website/content/chapters.json')
assert json.loads((run/'full-harness-v1-01-exit.json').read_text(encoding='utf-8'))['exit_code']!=0
snapshot=run/'leaves/pre-boundary-repair-chapters-v1.json.txt'
assert not snapshot.exists();snapshot.write_bytes(p.read_bytes())
x=json.loads(p.read_text(encoding='utf-8'));c=next(r for r in x['chapters'] if r['slug']=='online-ftl-failure')
c['completion_definition']='One source Example2.10: retained actual prefix recursion, fixed-initial-input causality, feasibility plus historical minimization, exact comparator0 regret for T>=1; not completion of Chapter2. Seven existing proofs are reused; no new theorem bodies or main/live update.'
with p.open('w',encoding='utf-8',newline='\n') as f:json.dump(x,f,ensure_ascii=False,indent=2);f.write('\n')
subprocess.run([sys.executable,'-X','utf8',str(run/'run-command.py'),'reader-repair-lifecycle-v1',
    sys.executable,'-X','utf8','tools/bandit.py','lifecycle-event','--session','ONLINE-FTL-MIGRATION-20261005','--event','repair',
    '--payload-json',json.dumps(dict(run_id=run.name,reason='Full harness requires existing not completion of Chapter2 reader phrase',
        failed_gate='full-harness-v1-01',repair='Preserve exact Chapter2 boundary phrase alongside precise same-source scope',
        mathematical_statement_changed=False,Lean_code_changed=False))],check=True)
print('Exact chapter boundary restored; failed full harness preserved; no Lean change.')
