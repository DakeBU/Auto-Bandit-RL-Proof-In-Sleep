from common_integrated_v2 import *
fixed_integrated()
assert load(RUN/'integrated-gates-v3.json')['status'].startswith('Actual combined')
assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],text=True).strip()
site=Path('tmp/online-no-regret-site-v1');assert not site.exists()
temporary=Path('tmp/online-no-regret-site-build-v2.log');assert not temporary.exists()
cmd=[sys.executable,'-B','-X','utf8','website/scripts/build_site.py','--lean-verified','--output',site.as_posix()];start=time.time()
with temporary.open('wb') as stream:child=subprocess.run(cmd,stdout=stream,stderr=subprocess.STDOUT)
write(RUN/'site-build-v2.log',temporary.read_bytes());write(RUN/'site-build-v2-exit.json',dict(command=cmd,cwd=ROOT.as_posix(),exit_code=child.returncode,seconds=round(time.time()-start,3),log_sha256=sha(RUN/'site-build-v2.log'),actual_clean_tree_at_start=True,stdout_ignored_until_completion=True,applicable_Lean='combined-root-v2/combined-Tests-v2/full-harness-v2; public/canary hashes unchanged',applicable_contributor='contributor-committed-exact-base-v3'))
assert child.returncode==0
gate('site-check-v2',sys.executable,'-B','-X','utf8','website/scripts/check_site.py','--output',site)
gate('registry-check-v2',sys.executable,'-B','-X','utf8',RUN/'verify-registry-v2.py')
gate('current-reader-capture-v2',sys.executable,'-B','-X','utf8',RUN/'capture-reader-v2.py')
fixed_integrated()
