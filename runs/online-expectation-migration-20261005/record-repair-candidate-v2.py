from pathlib import Path
import hashlib,json,subprocess,sys
run=Path(__file__).parent
load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'))
for label in ['reader-registry-tests-v2-01','full-harness-v2-01','history-bindings-v3-01','scoped-diff-v3-01']:
 assert load(run/(label+'-exit.json'))['exit_code']==0,label
raw=(run/'full-harness-v2-01.log').read_text(encoding='utf-8')
assert 'Ran 466 tests' in raw and 'OK (skipped=7)' in raw and 'check passed' in raw
base=load(run/'stacked-base-REST-v1-01.log')
assert base['state']=='open' and base['draft'] and base['head']=='7c3b241a13b1b43d1efcd08429f33c93b890a981' and base['merged_at'] is None
ob=load(run/'proof-obligations-repair-v1.json');ob['stage']='candidate';ob['repair']='Reader wording repaired; isolated reader tests/fullv2/history/scoped replay passed, final source/reader review pending.'
out=run/'proof-obligations-candidate-v2.json';assert not out.exists()
with out.open('w',encoding='utf-8',newline='\n') as handle:json.dump(ob,handle,ensure_ascii=False,indent=2);handle.write('\n')
subprocess.run([sys.executable,'-X','utf8',str(run/'run-command.py'),'repair-candidate-lifecycle-v2',sys.executable,'-X','utf8','tools/bandit.py','lifecycle-event','--session','ONLINE-EXPECTATION-MIGRATION-20261005','--event','candidate','--payload-json',json.dumps(dict(reader_repair_resolved=True,failed_v1_retained=True,full_v2='466tests7skips passed',mathematical_target_change=False,tests_unchanged=True,retained_proofs=7,retained_definitions=3,new_proofs=0,parent_accepted=False,chapter_complete=False,goal_complete=False))],check=True)
print('Reader repair replay passed, bounded candidate restored; final review pending.')
