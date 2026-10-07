from common_v1 import *
fixed(proving=True,integrated=True)
gate('full-harness-reader-v3',sys.executable,'-B','-X','utf8','tools/bandit.py','check')
raw=(RUN/'full-harness-reader-v3.log').read_text(encoding='utf-8');assert 'Ran 466 tests' in raw and 'OK (skipped=7)' in raw and 'check passed' in raw
write(RUN/'combined-gates-reader-v3.json',{**load(RUN/'combined-gates-metadata-v2.json'),'effective_full_harness':'full-harness-reader-v3','current_initial_scope_prose_repair_included':True,'mathematical_bodies_unchanged':True})
subprocess.run([sys.executable,'-B','-X','utf8',str(RUN/'commit-owned-v1.py'),'Restrict initial FTL reader notes to first-target-only assumptions'],check=True)
gate('contributor-reader-v3',sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base',BASE)
gate('scoped-diff-reader-v3',sys.executable,'-B','-X','utf8',RUN/'check-scoped-diff-v1.py','reader-v3')
gate('source-scope-reader-v3',sys.executable,'-B','-X','utf8',RUN/'audit-scope-v1.py','reader-v3')
subprocess.run([sys.executable,'-B','-X','utf8',str(RUN/'commit-owned-v1.py'),'Bind current FTL reader repair and clean-site tools'],check=True)
assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],text=True).strip()
site=Path('tmp/online-ftl-sharp-site-v2');cmd=[sys.executable,'-B','-X','utf8','website/scripts/build_site.py','--lean-verified','--output',str(site)];temporary=Path('tmp/online-ftl-sharp-site-build-v2.log');start=time.time()
with temporary.open('wb') as stream:child=subprocess.run(cmd,stdout=stream,stderr=subprocess.STDOUT)
write(RUN/'site-build-v2.log',temporary.read_bytes());write(RUN/'site-build-v2-exit.json',dict(command=cmd,cwd=ROOT.as_posix(),exit_code=child.returncode,seconds=round(time.time()-start,3),log_sha256=sha(RUN/'site-build-v2.log'),actual_clean_tree_at_start=True,stdout_ignored_until_completion=True));assert child.returncode==0
gate('site-check-v2',sys.executable,'-B','-X','utf8','website/scripts/check_site.py','--output',site)
gate('registry-v2',sys.executable,'-B','-X','utf8',RUN/'verify-registry-v2.py')
native('candidate-reader-repaired-event-v3','lifecycle-event','--session',TASK,'--event','candidate','--payload-json',json.dumps(dict(run_id=RUN.name,contract_version=1,reader_initial_scope_repaired=True,all_frozen_statements_and_bodies_unchanged=True,current_combined_harness_site_registry_passed=True,pixels_FINAL_native_PR_pending=True,chapter_complete=False,goal_complete=False)))
gate('formula-render-v2',sys.executable,'-B','-X','utf8',RUN/'capture-reader-v2.py')
fixed(proving=True,integrated=True)
