"""Separate the checker's production surfaces from owned test evidence."""
from pathlib import Path
import hashlib,json,subprocess,sys
run=Path(__file__).parent;task='ONLINE-GUESSING-MIGRATION-20261006'
load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'))
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def gate(label,*args):subprocess.run([sys.executable,'-X','utf8',str(run/'run-command.py'),label,*args],check=True)
assert load(run/'contributor-exact-v1-01-exit.json')['exit_code']==1
assert 'Tests.lean, Tests/OnlineGuessingComparisonCanary.lean' in (run/'contributor-exact-v1-01.log').read_text(encoding='utf-8')
public=load(run/'public-actual-bindings-v1.json')
for p,h in public['public_modules'].items():assert sha(p)==h
for p,h in public['new_canary'].items():assert sha(p)==h
gate('contributor-repair-lifecycle-v2',sys.executable,'-X','utf8','tools/bandit.py','lifecycle-event','--session',task,'--event','repair','--payload-json',json.dumps(dict(run_id=run.name,reason='Manifest affected_files denotes protected production surfaces; move two owned Tests paths to explicit verification evidence.',mathematical_target_changed=False,proof_inputs_changed=False)))
p=Path('research-wiki/contribution-contracts/online-guessing-migration-20261006.json');snap=run/'leaves/manifest-before-contributor-list-v2.json.txt';assert not snap.exists();snap.write_bytes(p.read_bytes())
data=load(p);tests=['Tests.lean','Tests/OnlineGuessingComparisonCanary.lean'];assert all(t in data['affected_files'] for t in tests)
data['affected_files']=[f for f in data['affected_files'] if f not in tests]
data['verification']['owned_test_files']=tests
with p.open('w',encoding='utf-8',newline='\n') as f:json.dump(data,f,ensure_ascii=False,indent=2);f.write('\n')
out=run/'contributor-list-repair-v2.json';assert not out.exists()
with out.open('w',encoding='utf-8',newline='\n') as f:json.dump(dict(status='manifest-field-classification-only',original_path=p.as_posix(),original_snapshot=snap.as_posix(),raw_sha256=sha(snap),current_sha256=sha(p),production_files=data['affected_files'],owned_test_files=tests,proof_and_test_bytes_unchanged=True,mathematical_repairs=[]),f,indent=2);f.write('\n')
for event in ['proving','candidate']:
 gate('contributor-'+event+'-lifecycle-v2',sys.executable,'-X','utf8','tools/bandit.py','lifecycle-event','--session',task,'--event',event,'--payload-json',json.dumps(dict(run_id=run.name,terminal='guessing_vs_mean_unbounded unchanged',repair='manifest-field-classification-only',package_gates_pending=True,chapter_complete=False,goal_complete=False)))
print('Seven production surfaces and two explicitly retained owned test files; all Lean/canary bytes unchanged.')
