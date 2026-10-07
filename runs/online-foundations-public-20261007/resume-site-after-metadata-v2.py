from common_v1 import *
fixed(True);assert load(RUN/'contributor-exact-v1-exit.json')['exit_code']==1
subprocess.run([sys.executable,'-B','-X','utf8',str(RUN/'commit-owned-v1.py'),'Repair contributor metadata scope and retain all main-relative gaps'],check=True)
gate('contributor-exact-v2',sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base',BASE)
gate('scoped-diff-v2',sys.executable,'-B','-X','utf8',RUN/'check-scoped-diff-v1.py','v2')
gate('source-scope-v2',sys.executable,'-B','-X','utf8',RUN/'audit-scope-v1.py','v2')
cmd=[sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base','origin/main'];log=RUN/'main-relative-diagnostic-v1.log';assert not log.exists();start=time.time()
with log.open('wb') as stream:child=subprocess.run(cmd,stdout=stream,stderr=subprocess.STDOUT)
write(RUN/'main-relative-diagnostic-v1-exit.json',dict(command=cmd,cwd=ROOT.as_posix(),exit_code=child.returncode,seconds=round(time.time()-start,3),log_sha256=sha(log)))
assert child.returncode==1;raw=log.read_text(encoding='utf-8')
for n in ['Asymptotic','FTL','Foundations','History','IID','Information','Mean','Regret','Stochastic']:assert 'OnlineLearning'+n+'.lean' in raw,n
write(RUN/'main-relative-diagnostic-v1.json',dict(status='failed-unwaived',actual_exit_code=child.returncode,exact_PR186_base_separately_passed=True,nine_Chapter1_required_including_retained_Foundations=True,eight_OTHER_current_semantic_migrations_required=True,unchanged_public_source_not_current_production_delta=True,no_gate_waiver=True,chapter_complete=False,goal_complete=False))
gate('full-harness-metadata-repair-v3',sys.executable,'-B','-X','utf8','tools/bandit.py','check')
raw=(RUN/'full-harness-metadata-repair-v3.log').read_text(encoding='utf-8');assert 'Ran 466 tests' in raw and 'OK (skipped=7)' in raw and 'check passed' in raw
combined=load(RUN/'combined-gates-v1.json');combined.update(effective_full_harness='full-harness-metadata-repair-v3',current_reader_metadata_and_contributor_scope_included=True,all_five_failure_histories_retained=True)
write(RUN/'combined-gates-after-metadata-v2.json',combined)
subprocess.run([sys.executable,'-B','-X','utf8',str(RUN/'commit-owned-v1.py'),'Bind actual metadata repair and unwaived whole-Chapter1 contributor gaps'],check=True)
old=(RUN/'source-site-gates-v1.py').read_text(encoding='utf-8');tail=old[old.index("assert not subprocess.check_output(['git','status'"):]
write(RUN/'continue-site-v2.py','from common_v1 import *\nfixed(True)\n'+tail)
# Record the already reviewed infrastructure before the clean-source site build.
subprocess.run([sys.executable,'-B','-X','utf8',str(RUN/'commit-owned-v1.py'),'Bind clean-source Be-the-Leader site execution script'],check=True)
subprocess.run([sys.executable,'-B','-X','utf8',str(RUN/'continue-site-v2.py')],check=True)
fixed(True);print('Metadata repair/current full harness/site branch completed; no source target change.')
