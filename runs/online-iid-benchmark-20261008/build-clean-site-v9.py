from common_integrated_v2 import *
fixed_integrated()
assert load(RUN/'integrated-gates-v2.json')['affected_production_paths']==5
assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],text=True).strip()
site=Path('tmp/online-iid-benchmark-site-v9');assert not site.exists()
temporary=Path('tmp/online-iid-benchmark-site-build-v9.log');assert not temporary.exists()
command=[sys.executable,'-B','-X','utf8','website/scripts/build_site.py','--lean-verified','--output',site.as_posix()]
start=time.monotonic()
with temporary.open('wb') as stream: child=subprocess.run(command,stdout=stream,stderr=subprocess.STDOUT)
write(RUN/'site-build-v9.log',temporary.read_bytes())
write(RUN/'site-build-v9-exit.json',dict(command=command,cwd=ROOT.as_posix(),exit_code=child.returncode,seconds=time.monotonic()-start,
    log_sha256=sha(RUN/'site-build-v9.log'),actual_clean_tree_at_start=True,stdout_ignored_until_completion=True,
    applicable_Lean='Actual combined-root-v2/combined-Tests-v2/full-harness-v2; public/canary/imports/Lean source hashes unchanged; reader-only corrections after rejected FINAL: comparator/expectation wording and meanPredict t>0, with all Lean/source hashes unchanged; page/status label repairs retained.',
    applicable_contributor='Actual committed exact-base gate:5production paths/1contract.',deployed=False))
assert child.returncode==0
gate('site-check-v9',sys.executable,'-B','-X','utf8','website/scripts/check_site.py','--output',site)
gate('registry-check-v9',sys.executable,'-B','-X','utf8',RUN/'verify-registry-v9.py')
gate('current-reader-capture-v9',sys.executable,'-B','-X','utf8',RUN/'capture-reader-v9.py')
fixed_integrated()
