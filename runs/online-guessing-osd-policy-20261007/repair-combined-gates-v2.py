"""Repair tracked-source packaging precondition, preserving original failed harness evidence."""
from common_v1 import *
headers();b=load(RUN/'body-bindings-v1.json')
assert sha(PUBLIC)==b['public_sha256'] and sha(CANARY)==b['canary_sha256']
failed=load(RUN/'full-harness-v1-01-exit.json');assert failed['exit_code']==1
raw=(RUN/'full-harness-v1-01.log').read_text(encoding='utf-8')
assert 'untracked Lean source under allowlisted tree: '+PUBLIC.as_posix() in raw
for label in ['combined-root-v1-01','combined-Tests-v1-01']:assert load(RUN/(label+'-exit.json'))['exit_code']==0
native('combined-repair-event-v2-01','lifecycle-event','--session',TASK,'--event','repair','--payload-json',json.dumps(dict(run_id=RUN.name,contract_version=1,failed_gate='full-harness-v1-01',actual_cause='Anonymous supplement test requires all allowlisted Lean source tracked by git ls-files; new actual proof module was not staged.',repair='Stage only owned new production/canary source; no type/body/source change.',chapter_complete=False,goal_complete=False)))
gate('stage-owned-Lean-v2-01','git','add','--',PUBLIC,CANARY)
native('combined-repair-resume-v2-01','lifecycle-event','--session',TASK,'--event','proving','--payload-json',json.dumps(dict(run_id=RUN.name,contract_version=1,frozen_types_and_bodies_unchanged=True,combined_harness_rerun=True,chapter_complete=False,goal_complete=False)))
gate('full-harness-v2-01',sys.executable,'-B','-X','utf8','tools/bandit.py','check')
jobs={}
for label in ['combined-root-v1-01','combined-Tests-v1-01']:
 m=re.search(r'Build completed successfully \((\d+) jobs\)',(RUN/(label+'.log')).read_text(encoding='utf-8'));assert m;jobs[label]=int(m.group(1))
raw=(RUN/'full-harness-v2-01.log').read_text(encoding='utf-8');tests=re.search(r'Ran (\d+) tests',raw);skips=re.search(r'OK \(skipped=(\d+)\)',raw)
assert tests and skips and 'FAILED (' not in raw and 'build failed' not in raw
write(RUN/'combined-gates-v1.json',dict(status='actual-root-Tests-full-harness-passed',jobs_including_cached=jobs,full_tests=int(tests.group(1)),existing_skips=int(skips.group(1)),raw_log_rows=[dict(label=x,sha256=sha(RUN/(x+'.log')),receipt_sha256=sha(RUN/(x+'-exit.json'))) for x in ['combined-root-v1-01','combined-Tests-v1-01','full-harness-v2-01']],retained_failed_harness='full-harness-v1-01',repair='Track only owned new Lean sources; frozen target/body unchanged.',public_sha256=sha(PUBLIC),canary_sha256=sha(CANARY),source_BODY_review='accepted-with-explicit-delta',reader_FINAL_site='pending',source_package_accepted=False,chapter_complete=False,goal_complete=False))
native('combined-repaired-candidate-v2-01','lifecycle-event','--session',TASK,'--event','candidate','--payload-json',json.dumps(dict(run_id=RUN.name,contract_version=1,combined_gates=RUN.joinpath('combined-gates-v1.json').as_posix(),reader_FINAL_pending=True,chapter_complete=False,goal_complete=False)))
headers();print('Actual combined gates passed after staged-source packaging repair; no mathematical change.')
