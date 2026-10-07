from common_integrated_v1 import *
fixed_integrated()
assert load(RUN/'integrated-gates-v2.json')['committed_production_paths']==5
assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],text=True).strip()
site=Path('tmp/online-log-lower-site-v1');assert not site.exists()
temporary=Path('tmp/online-log-lower-site-build-v1.log');assert not temporary.exists()
cmd=[sys.executable,'-B','-X','utf8','website/scripts/build_site.py','--lean-verified','--output',site.as_posix()];start=time.time()
with temporary.open('wb') as stream:child=subprocess.run(cmd,stdout=stream,stderr=subprocess.STDOUT)
write(RUN/'site-build-v1.log',temporary.read_bytes())
write(RUN/'site-build-v1-exit.json',dict(command=cmd,cwd=ROOT.as_posix(),exit_code=child.returncode,seconds=round(time.time()-start,3),log_sha256=sha(RUN/'site-build-v1.log'),actual_clean_tree_at_start=True,stdout_ignored_until_completion=True,applicable_nonvacuous_contributor='contributor-exact-base-v1'))
assert child.returncode==0
gate('site-check-v1',sys.executable,'-B','-X','utf8','website/scripts/check_site.py','--output',site)
gate('registry-check-v1',sys.executable,'-B','-X','utf8',RUN/'verify-registry-v1.py')
gate('current-reader-capture-v1',sys.executable,'-B','-X','utf8',RUN/'capture-reader-v1.py')
fixed_integrated()
