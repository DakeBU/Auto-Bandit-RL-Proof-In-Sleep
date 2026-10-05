"""Add the actual contributor schema prefix, preserving all mathematical/reader data."""
from pathlib import Path
import hashlib,json,subprocess,sys
run=Path(__file__).parent;task='ONLINE-CLOSED-PROPER-MIGRATION-20261006'
load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'))
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert load(run/'contributor-exact-v1-01-exit.json')['exit_code']==1
assert 'progress_updates.teaching_route must start with updated: or no-change-with-reason:' in (run/'contributor-exact-v1-01.log').read_text(encoding='utf-8')
p=Path('research-wiki/contribution-contracts/online-closed-proper-migration-20261006.json');before=p.read_bytes();old=load(p);new=json.loads(json.dumps(old))
assert not old['progress_updates']['teaching_route'].startswith('updated:')
new['progress_updates']['teaching_route']='updated: '+old['progress_updates']['teaching_route']
snap=run/'leaves/pre-integration-contribution-contract-repair-v2.txt';assert not snap.exists();snap.write_bytes(before)
p.write_bytes((json.dumps(new,ensure_ascii=False,indent=2)+'\n').encode('utf-8'))
test=load(p);test['progress_updates']['teaching_route']=old['progress_updates']['teaching_route'];assert test==old
out=run/'contribution-metadata-repair-v2.json';assert not out.exists();out.write_bytes((json.dumps(dict(path=p.as_posix(),before_sha256=hashlib.sha256(before).hexdigest(),after_sha256=sha(p),before_snapshot=snap.as_posix(),delta='Only required updated: prefix to already-updated teaching_route metadata; all other manifest fields identical, no mathematical/reader/test change.',failed_gate='contributor-exact-v1-01',retry_pending=True),indent=2)+'\n').encode())
subprocess.run([sys.executable,'-X','utf8',str(run/'run-command.py'),'metadata-repair-lifecycle-v2',sys.executable,'-X','utf8','tools/bandit.py','lifecycle-event','--session',task,'--event','repair','--payload-json',json.dumps(dict(run_id=run.name,failed_gate='contributor-exact-v1-01',metadata_prefix_only=True,no_math_reader_test_change=True,chapter_complete=False,goal_complete=False))],check=True)
print('Only contributor metadata schema prefix repaired; exact contributor retry pending.')
