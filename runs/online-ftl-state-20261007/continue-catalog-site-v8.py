from common_v1 import *
fixed(proving=True,integrated=True)
subprocess.run([sys.executable,'-B','-X','utf8',RUN/'commit-owned-v2.py','Repair only source-pinned recursive FTL state catalogue boundary'],check=True)
gate('contributor-reader-v5',sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base',BASE)
gate('scoped-diff-reader-v5',sys.executable,'-B','-X','utf8',RUN/'check-scoped-diff-v2.py','reader-v5')
gate('source-scope-reader-v5',sys.executable,'-B','-X','utf8',RUN/'audit-scope-v3.py','reader-v5')
native('full-harness-reader-v5','check')
raw=(RUN/'full-harness-reader-v5.log').read_text(encoding='utf-8');counts=re.search(r'Ran (\d+) tests',raw);skips=re.search(r'OK \(skipped=(\d+)\)',raw)
assert counts and skips and 'check passed' in raw
write(RUN/'combined-gates-reader-v5.json',{**load(RUN/'combined-gates-reader-v4.json'),'full_tests':int(counts[1]),'existing_skips':int(skips[1]),'current_source_catalog_repair_checked':True,'new_python_boundary_tests':6,'current_harness_log_sha256':sha(RUN/'full-harness-reader-v5.log')})
subprocess.run([sys.executable,'-B','-X','utf8',RUN/'commit-owned-v2.py','Bind current FTL state catalogue and complete harness gates'],check=True)
assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],text=True).strip()
site=Path('tmp/online-ftl-state-site-v4');cmd=[sys.executable,'-B','-X','utf8','website/scripts/build_site.py','--lean-verified','--output',str(site)];temporary=Path('tmp/online-ftl-state-site-build-v4.log');start=time.time()
with temporary.open('wb') as stream:child=subprocess.run(cmd,stdout=stream,stderr=subprocess.STDOUT)
write(RUN/'site-build-v4.log',temporary.read_bytes());write(RUN/'site-build-v4-exit.json',dict(command=cmd,cwd=ROOT.as_posix(),exit_code=child.returncode,seconds=round(time.time()-start,3),log_sha256=sha(RUN/'site-build-v4.log'),actual_clean_tree_at_start=True,stdout_ignored_until_completion=True));assert child.returncode==0
gate('site-check-v4',sys.executable,'-B','-X','utf8','website/scripts/check_site.py','--output',site)
gate('registry-v4',sys.executable,'-B','-X','utf8',RUN/'verify-registry-v4.py')
fixed(proving=True,integrated=True)
