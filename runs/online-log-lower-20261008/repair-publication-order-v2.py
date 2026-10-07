from common_accepted_v1 import *
accepted_fixed()
assert load(RUN/'committed-raw-audit-v1-exit.json')['exit_code']==1
log=(RUN/'committed-raw-audit-v1.log').read_text(encoding='utf8')
assert 'File not in audited' in log or 'AssertionError:' in log
write(RUN/'publication-order-repair-v2.json',dict(failed_gate='committed-raw-audit-v1',exit_code=1,log_sha256=sha(RUN/'committed-raw-audit-v1.log'),reason='New final contribution/scope/diff logs, plus the live wrapper audit log, were not committed at the audited head. Fail-closed result preserved; no source or receipt corruption.',repair='Run final harness, close and commit every owned gate/helper/log, then invoke raw Git batch audit DIRECT with no RUN stdout wrapper. Record actual audited head; later final delivery DIRECT audit verifies its own committed record without self-referential hash.',PUBLIC_CANARY_roots_readers_exact_FINAL=True,all_original_reviews_still_valid=True,chapter_complete=False,goal_complete=False))
native('publication-repair-event-v2','lifecycle-event','--session',TASK,'--event','repair','--payload-json',json.dumps(dict(reason='Publication raw evidence order failure',repair_evidence=(RUN/'publication-order-repair-v2.json').as_posix(),source_terminal_and_reviews_unchanged=True,PR_delivery_pending=True)))
native('publication-recandidate-event-v2','lifecycle-event','--session',TASK,'--event','candidate','--payload-json',json.dumps(dict(reason='Direct raw audit planned after closed evidence commit',source_terminal_and_FINAL_reviews_unchanged=True,PR_delivery_pending=True)))
s=(RUN/'audit-committed-raw-v1.py').read_text(encoding='utf8').replace("RUN/'committed-raw-audit-v1.json'","RUN/'committed-raw-audit-v2.json'")
write(RUN/'audit-committed-raw-v2.py',s)
native('full-harness-final-v1','check')
accepted_fixed()
owned=load(RUN/'owned-commit-paths-v1.json')
for cmd in [['git','add','--',*owned],['git','commit','-m','Preserve publication audit failure and close validation evidence']]:
 child=subprocess.run(cmd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 print('\n'.join(child.stdout.decode('utf8',errors='replace').splitlines()[-5:]),flush=True);assert child.returncode==0,cmd
assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],text=True).strip()
print('Closed evidence commit',subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),'; invoke audit-committed-raw-v2 DIRECT after exit')
