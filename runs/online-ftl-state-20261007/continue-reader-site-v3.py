from common_v1 import *
fixed(proving=True,integrated=True)
subprocess.run([sys.executable,'-B','-X','utf8',RUN/'commit-owned-v1.py','Repair FTL-state explicit teaching metadata after actual site failure'],check=True)
gate('contributor-reader-v3',sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base',BASE)
gate('scoped-diff-reader-v3',sys.executable,'-B','-X','utf8',RUN/'check-scoped-diff-v1.py','reader-v3')
gate('source-scope-reader-v3',sys.executable,'-B','-X','utf8',RUN/'audit-scope-v2.py','reader-v3')
native('full-harness-reader-v3','check')
raw=(RUN/'full-harness-reader-v3.log').read_text(encoding='utf-8');assert 'Ran 466 tests' in raw and 'OK (skipped=7)' in raw and 'check passed' in raw
write(RUN/'combined-gates-reader-v3.json',{**load(RUN/'combined-gates-reader-v2.json'),'current_feature_metadata_repair_checked':True,'current_harness_log_sha256':sha(RUN/'full-harness-reader-v3.log')})
subprocess.run([sys.executable,'-B','-X','utf8',RUN/'commit-owned-v1.py','Bind current FTL-state source and repaired reader gates'],check=True)
assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],text=True).strip()
site=Path('tmp/online-ftl-state-site-v2');cmd=[sys.executable,'-B','-X','utf8','website/scripts/build_site.py','--lean-verified','--output',str(site)];temporary=Path('tmp/online-ftl-state-site-build-v2.log');start=time.time()
with temporary.open('wb') as stream:child=subprocess.run(cmd,stdout=stream,stderr=subprocess.STDOUT)
write(RUN/'site-build-v2.log',temporary.read_bytes());write(RUN/'site-build-v2-exit.json',dict(command=cmd,cwd=ROOT.as_posix(),exit_code=child.returncode,seconds=round(time.time()-start,3),log_sha256=sha(RUN/'site-build-v2.log'),actual_clean_tree_at_start=True,stdout_ignored_until_completion=True));assert child.returncode==0
gate('site-check-v2',sys.executable,'-B','-X','utf8','website/scripts/check_site.py','--output',site)
gate('registry-v2',sys.executable,'-B','-X','utf8',RUN/'verify-registry-v2.py')
fixed(proving=True,integrated=True)
