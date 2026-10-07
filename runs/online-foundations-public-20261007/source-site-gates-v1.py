from common_v1 import *
fixed(True);assert load(RUN/'combined-gates-v1.json')['status']=='actual-root-Tests-full-harness-passed'
assert load(RUN/'candidate-frontier-v1.json')['current_leaf']['id']==TASK
subprocess.run([sys.executable,'-B','-X','utf8',str(RUN/'commit-owned-v1.py'),'Revalidate Be-the-Leader source with named strict and premise canaries'],check=True)
gate('contributor-exact-v1',sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base',BASE)
gate('scoped-diff-v1',sys.executable,'-B','-X','utf8',RUN/'check-scoped-diff-v1.py','v1')
gate('source-scope-v1',sys.executable,'-B','-X','utf8',RUN/'audit-scope-v1.py','v1')
cmd=[sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base','origin/main'];log=RUN/'main-relative-diagnostic-v1.log';assert not log.exists();start=time.time()
with log.open('wb') as stream:child=subprocess.run(cmd,stdout=stream,stderr=subprocess.STDOUT)
write(RUN/'main-relative-diagnostic-v1-exit.json',dict(command=cmd,cwd=ROOT.as_posix(),exit_code=child.returncode,seconds=round(time.time()-start,3),log_sha256=sha(log)))
assert child.returncode in [0,1];raw=log.read_text(encoding='utf-8')
if child.returncode:
 for name in ['Asymptotic','FTL','History','IID','Information','Mean','Regret','Stochastic']:assert 'OnlineLearning'+name+'.lean' in raw,name
 assert 'production file has no valid contribution contract: BanditRLProof/OnlineLearningFoundations.lean' not in raw
write(RUN/'main-relative-diagnostic-v1.json',dict(status='passed' if child.returncode==0 else 'failed-unwaived',actual_exit_code=child.returncode,exact_PR186_base_separately_passed=True,eight_OTHERChapter1_required=child.returncode!=0,no_waiver=True,chapter_complete=False,goal_complete=False))
subprocess.run([sys.executable,'-B','-X','utf8',str(RUN/'commit-owned-v1.py'),'Bind Be-the-Leader exact-base preservation and unwaived chapter gaps'],check=True)
assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],text=True).strip()
site=Path('tmp/online-foundations-public-site-v1');cmd=[sys.executable,'-B','-X','utf8','website/scripts/build_site.py','--lean-verified','--output',str(site)];temporary=Path('tmp/online-foundations-public-site-build-v1.log');start=time.time()
with temporary.open('wb') as stream:child=subprocess.run(cmd,stdout=stream,stderr=subprocess.STDOUT)
write(RUN/'site-build-v1.log',temporary.read_bytes());write(RUN/'site-build-v1-exit.json',dict(command=cmd,cwd=ROOT.as_posix(),exit_code=child.returncode,seconds=round(time.time()-start,3),log_sha256=sha(RUN/'site-build-v1.log'),actual_clean_tree_at_start=True,stdout_ignored_until_completion=True));assert child.returncode==0
gate('site-check-v1',sys.executable,'-B','-X','utf8','website/scripts/check_site.py','--output',site)
gate('registry-v1',sys.executable,'-B','-X','utf8',RUN/'verify-registry-v1.py')
gate('formula-render-v1',sys.executable,'-B','-X','utf8',RUN/'capture-reader-v1.py')
fixed(True);print('Actual clean local Leanverified site/same registry and browser captures; root pixels/FINAL/native/PR remain pending.')
