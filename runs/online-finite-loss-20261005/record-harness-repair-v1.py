"""Preserve the failed full gate and make the new source tracked before rerunning."""
from pathlib import Path
import json,subprocess,sys,hashlib
run=Path(__file__).parent;task='ONLINE-FINITE-LOSS-20261005'
failed=json.loads((run/'full-harness-v1-01-exit.json').read_text(encoding='utf-8'));assert failed['exit_code']==1
raw=(run/'full-harness-v1-01.log').read_text(encoding='utf-8')
assert 'untracked Lean source under allowlisted tree: BanditRLProof/OnlineConstraintFiniteLoss.lean' in raw
assert 'Ran 440 tests' in raw and 'FAILED (errors=1, skipped=7)' in raw
p=run/'full-harness-repair-v1.json';assert not p.exists()
with p.open('w',encoding='utf-8',newline='\n') as f:json.dump(dict(failed_gate='full-harness-v1-01',failure='Anonymous supplement test refuses untracked production Lean source.',
    repair='Track and commit the new candidate production/canary module with exact source/evidence; rerun the full gate without changing proof code or tests.',
    proof_statement_change=False,test_disabled=False,anonymous_frozen_snapshot_edited=False,actual_failed_tests=440,actual_skips=7),f,indent=2);f.write('\n')
subprocess.run([sys.executable,'-X','utf8',str(run/'run-command.py'),'harness-repair-lifecycle-v1',sys.executable,'-X','utf8','tools/bandit.py','lifecycle-event','--session',task,'--event','repair','--payload-json',json.dumps(dict(run_id=run.name,reason='untracked new production source rejected by existing supplement test',target_change=False,chapter_complete=False,goal_complete=False))],check=True)
print('Failed440/7 gate preserved; tracking/commit required before actual rerun, no proof weakening/test bypass.')
