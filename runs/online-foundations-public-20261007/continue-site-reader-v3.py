from common_v1 import *
fixed(True)
assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],text=True).strip()
site=Path('tmp/online-foundations-public-site-v2');cmd=[sys.executable,'-B','-X','utf8','website/scripts/build_site.py','--lean-verified','--output',str(site)];temporary=Path('tmp/online-foundations-public-site-build-v2.log');start=time.time()
with temporary.open('wb') as stream:child=subprocess.run(cmd,stdout=stream,stderr=subprocess.STDOUT)
write(RUN/'site-build-v2.log',temporary.read_bytes());write(RUN/'site-build-v2-exit.json',dict(command=cmd,cwd=ROOT.as_posix(),exit_code=child.returncode,seconds=round(time.time()-start,3),log_sha256=sha(RUN/'site-build-v2.log'),actual_clean_tree_at_start=True,stdout_ignored_until_completion=True));assert child.returncode==0
gate('site-check-v2',sys.executable,'-B','-X','utf8','website/scripts/check_site.py','--output',site)
gate('registry-v2',sys.executable,'-B','-X','utf8',RUN/'verify-registry-v2.py')
gate('formula-render-v2',sys.executable,'-B','-X','utf8',RUN/'capture-reader-v2.py')
fixed(True);print('Actual clean local Leanverified site/same registry and browser captures; root pixels/FINAL/native/PR remain pending.')
