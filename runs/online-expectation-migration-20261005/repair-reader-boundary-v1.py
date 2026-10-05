"""Retain the tested explicit source completion boundary without proof changes."""
from pathlib import Path
import hashlib,json,subprocess,sys
run=Path(__file__).parent;path=Path('website/content/chapters.json')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'))
failure=load(run/'full-harness-v1-01-exit.json');assert failure['exit_code']==1
raw=(run/'full-harness-v1-01.log').read_text(encoding='utf-8')
assert 'FAILED (failures=1, skipped=7)' in raw and 'test_expectation_foundations_do_not_claim_full_jensen' in raw
snapshot=run/'leaves/reader-before-boundary-repair-v1--chapters.json.txt';assert not snapshot.exists();snapshot.write_bytes(path.read_bytes())
before=load(path);after=load(path);row=next(x for x in after['chapters'] if x['slug']=='online-expectation')
row['completion_definition']='Seven retained library proofs and three unchanged definitions, zero new proof code/nodes. This is not completion of Orabona Theorem2.9, its negative-part producer, Chapter2 or the whole book; the parent requires separate distinct revalidation.'
assert [x for x in before['chapters'] if x['slug']!='online-expectation']==[x for x in after['chapters'] if x['slug']!='online-expectation']
with path.open('w',encoding='utf-8',newline='\n') as handle:json.dump(after,handle,ensure_ascii=False,indent=2);handle.write('\n')
out=run/'reader-boundary-repair-v1.json';assert not out.exists()
with out.open('w',encoding='utf-8',newline='\n') as handle:
 json.dump(dict(status='reader-wording-repair-test-replay-pending',failed_gate='full-harness-v1-01',failed_test='test_expectation_foundations_do_not_claim_full_jensen',before_snapshot=snapshot.as_posix(),before_sha256=sha(snapshot),after_path=path.as_posix(),after_sha256=sha(path),delta='Restored explicit tested phrase not completion of Orabona Theorem2.9; same boundary, only expectation completion text.',proofs_tests_frozen_headers_unchanged=True,tests_not_modified=True,all_other_Book_subtrees_unchanged=True),handle,indent=2);handle.write('\n')
subprocess.run([sys.executable,'-X','utf8',str(run/'run-command.py'),'repair-lifecycle-v1',sys.executable,'-X','utf8','tools/bandit.py','lifecycle-event','--session','ONLINE-EXPECTATION-MIGRATION-20261005','--event','repair','--payload-json',json.dumps(dict(reason='Reader completion wording omitted tested explicit parent non-completion phrase',failed_gate='full-harness-v1-01',mathematical_target_change=False,tests_unchanged=True,chapter_complete=False,goal_complete=False))],check=True)
ob=load(run/'proof-obligations-proving-v1.json');ob['stage']='repair';ob['repair']='Reader non-completion phrase only; full harness replay and final semantic review required.'
with (run/'proof-obligations-repair-v1.json').open('w',encoding='utf-8',newline='\n') as handle:json.dump(ob,handle,ensure_ascii=False,indent=2);handle.write('\n')
print('Reader boundary phrase repaired; no test/Lean statement/body/context changes.')
