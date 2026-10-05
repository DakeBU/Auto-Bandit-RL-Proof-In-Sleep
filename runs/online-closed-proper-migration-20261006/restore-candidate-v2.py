"""Return the exact unchanged terminal to candidate only after successful retry."""
from pathlib import Path
import hashlib,json,subprocess,sys
run=Path(__file__).parent;task='ONLINE-CLOSED-PROPER-MIGRATION-20261006'
load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'))
assert load(run/'full-harness-v2-01-exit.json')['exit_code']==0
raw=(run/'full-harness-v2-01.log').read_text(encoding='utf-8');assert 'Ran 466 tests' in raw and 'OK (skipped=7)' in raw and 'check passed' in raw
repair=load(run/'public-comment-qualification-v2.json');assert hashlib.sha256(Path(repair['path']).read_bytes()).hexdigest()==repair['qualified_sha256']
ob=load(run/'proof-obligations-repair-v1.json');ob['stage']='candidate';ob['repair_resolved']='Leading ordinary comment lexical fix only, fullharnessv2 actual success, statements/proofs/complete definitions/canary/rootTests unchanged.'
p=run/'proof-obligations-candidate-v2.json';assert not p.exists();p.write_bytes((json.dumps(ob,ensure_ascii=False,indent=2)+'\n').encode())
subprocess.run([sys.executable,'-X','utf8',str(run/'run-command.py'),'candidate-lifecycle-v2',sys.executable,'-X','utf8','tools/bandit.py','lifecycle-event','--session',task,'--event','candidate','--payload-json',json.dumps(dict(run_id=run.name,repair_resolved=True,actual_retry='full-harness-v2-01',frozen_headers=ob['required'],no_mathematical_change=True,remaining_gates=['contributor/history/site/registry/finalreader/PR'],source_package_accepted=False,chapter_complete=False,goal_complete=False))],check=True)
print('Unchanged exact terminal candidate restored after full retry; final package gates pending.')
