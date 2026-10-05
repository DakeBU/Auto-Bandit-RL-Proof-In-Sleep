"""Repair Git visibility for the packaging gate, without changing proof inputs."""
from pathlib import Path
import hashlib,json,subprocess,sys
run=Path(__file__).parent;task='ONLINE-GUESSING-MIGRATION-20261006'
load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'))
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def gate(label,*args):subprocess.run([sys.executable,'-X','utf8',str(run/'run-command.py'),label,*args],check=True)
assert load(run/'full-harness-v1-01-exit.json')['exit_code']==1
assert 'untracked Lean source under allowlisted tree: BanditRLProof/OnlineGuessingComparison.lean' in (run/'full-harness-v1-01.log').read_text(encoding='utf-8')
paths=['BanditRLProof/OnlineGuessingComparison.lean','Tests/OnlineGuessingComparisonCanary.lean']
before={p:sha(p) for p in paths}
gate('harness-repair-lifecycle-v2',sys.executable,'-X','utf8','tools/bandit.py','lifecycle-event','--session',task,'--event','repair','--payload-json',json.dumps(dict(run_id=run.name,failed_command='full-harness-v1-01',reason='Anonymous packaging test requires new allowlisted Lean sources in Git index; stage only two owned new Lean sources.',mathematical_target_changed=False,proof_inputs_changed=False)))
subprocess.run(['git','add','--',*paths],check=True)
assert before=={p:sha(p) for p in paths}
out=run/'harness-index-repair-v2.json';assert not out.exists()
with out.open('w',encoding='utf-8',newline='\n') as f:json.dump(dict(status='Git-index-only-repair',staged_owned_paths=before,failed_test_count=440,failed_existing_skips=7,raw_failure_preserved=True,proof_inputs_changed=False,mathematical_repairs=[]),f,indent=2);f.write('\n')
gate('harness-proving-lifecycle-v2',sys.executable,'-X','utf8','tools/bandit.py','lifecycle-event','--session',task,'--event','proving','--payload-json',json.dumps(dict(run_id=run.name,terminal='guessing_vs_mean_unbounded unchanged',repair='Git-index-only',root_Tests_current_passed=True,full_harness_rerun_pending=True,chapter_complete=False,goal_complete=False)))
gate('harness-candidate-lifecycle-v2',sys.executable,'-X','utf8','tools/bandit.py','lifecycle-event','--session',task,'--event','candidate','--payload-json',json.dumps(dict(run_id=run.name,terminal='guessing_vs_mean_unbounded unchanged',proof_inputs_unchanged=True,package_gates_pending=True,chapter_complete=False,goal_complete=False)))
print('Only two task-owned new Lean sources staged; proof bytes unchanged, failed raw harness evidence retained.')
