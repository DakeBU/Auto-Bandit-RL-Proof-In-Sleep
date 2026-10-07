from common_v1 import *
fixed(integrated=True)
assert load(RUN/'integrated-gates-v2.json')['status'].startswith('Actual root/Tests/fullharness-v2')
assert not subprocess.check_output(['git','status','--porcelain'],text=True).strip()
site=Path('tmp/online-regret-domains-site-v1');assert not site.exists()
# Preserve a genuinely clean snapshot: capture stdout in ignored tmp until
# the builder has finished its own actual Git source-state snapshot.
temporary=Path('tmp/online-regret-domains-site-build-v1.log');assert not temporary.exists()
cmd=[sys.executable,'-B','-X','utf8','website/scripts/build_site.py','--lean-verified','--output',str(site)];start=time.time()
with temporary.open('wb') as stream:child=subprocess.run(cmd,stdout=stream,stderr=subprocess.STDOUT)
write(RUN/'site-build-v1.log',temporary.read_bytes())
write(RUN/'site-build-v1-exit.json',dict(command=cmd,cwd=ROOT.as_posix(),exit_code=child.returncode,seconds=round(time.time()-start,3),log_sha256=sha(RUN/'site-build-v1.log'),actual_clean_tree_at_start=True,stdout_ignored_until_completion=True))
assert child.returncode==0
gate('site-check-v1',sys.executable,'-B','-X','utf8','website/scripts/check_site.py','--output',site)
gate('registry-check-v1',sys.executable,'-B','-X','utf8',RUN/'verify-registry-v1.py')
gate('scoped-diff-pre-final-v1',sys.executable,'-B','-X','utf8',RUN/'check-scoped-diff-v1.py','pre-final-v1')
gate('current-reader-capture-v1',sys.executable,'-B','-X','utf8',RUN/'capture-reader-v1.py')
fixed(integrated=True)
