"""Clean scoped source commit, contributor diagnostics and real Lean-verified local site."""
from common_v1 import *
headers();assert load(RUN/'combined-gates-v1.json')['status']=='actual-root-Tests-full-harness-passed'
assert load(RUN/'candidate-frontier-v1.json')['current_leaf']['id']==TASK
subprocess.run([sys.executable,'-B','-X','utf8',str(RUN/'commit-owned-v1.py'),'Prove absolute-loss regret for played-legal finite-history OSD policies'],check=True)
gate('contributor-exact-v1-01',sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base',BASE)
gate('scoped-diff-v1-01',sys.executable,'-B','-X','utf8',RUN/'check-scoped-diff-v1.py','v1')
gate('source-scope-v1-01',sys.executable,'-B','-X','utf8',RUN/'audit-scope-v1.py')
cmd=[sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base','origin/main'];start=time.time();child=subprocess.run(cmd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
write(RUN/'main-relative-diagnostic-v1-01.log',child.stdout)
write(RUN/'main-relative-diagnostic-v1-01-exit.json',dict(command=cmd,cwd=ROOT.as_posix(),exit_code=child.returncode,seconds=round(time.time()-start,3),log_sha256=sha(RUN/'main-relative-diagnostic-v1-01.log')))
assert child.returncode==1
line=next(s for s in child.stdout.decode('utf-8').splitlines() if 'production paths missing from all changed contribution manifests:' in s)
missing=set(line.split(': ',1)[1].split(', '));expected={'BanditRLProof/OnlineLearning'+n+'.lean' for n in ['Asymptotic','FTL','Foundations','History','IID','Information','Mean','Regret','Stochastic']};assert missing==expected,missing
write(RUN/'main-relative-diagnostic-v1.json',dict(status='failed-unwaived',actual_exit_code=child.returncode,raw_log_sha256=sha(RUN/'main-relative-diagnostic-v1-01.log'),missing_required_paths=sorted(missing),exact_PR181_base_gate_separately_passed=True,not_a_gate_waiver=True,chapter_complete=False,goal_complete=False))
subprocess.run([sys.executable,'-B','-X','utf8',str(RUN/'commit-owned-v1.py'),'Bind guessing-policy exact-base preservation and contributor evidence'],check=True)
assert not subprocess.check_output(['git','status','--porcelain'],text=True).strip()
site=Path('tmp/online-guessing-osd-policy-site-v1')
# Keep the tree actually clean during generation: temporary stdout is ignored,
# and create the permanent raw log/receipt only after the real build finishes.
cmd=[sys.executable,'-B','-X','utf8','website/scripts/build_site.py','--lean-verified','--output',site]
temporary=Path('tmp/online-guessing-osd-policy-site-build-v1.log');start=time.time()
with temporary.open('wb') as stream: child=subprocess.run(cmd,stdout=stream,stderr=subprocess.STDOUT)
write(RUN/'site-build-v1-01.log',temporary.read_bytes())
write(RUN/'site-build-v1-01-exit.json',dict(command=list(map(str,cmd)),cwd=ROOT.as_posix(),exit_code=child.returncode,seconds=round(time.time()-start,3),log_sha256=sha(RUN/'site-build-v1-01.log'),actual_clean_tree_at_start=True))
assert child.returncode==0
gate('site-check-v1-01',sys.executable,'-B','-X','utf8','website/scripts/check_site.py','--output',site)
gate('registry-v1-01',sys.executable,'-B','-X','utf8',RUN/'verify-registry-v1.py')
gate('browser-v1-01',sys.executable,'-B','-X','utf8',RUN/'browser-v1.py')
gate('formula-render-v1-01',sys.executable,'-B','-X','utf8',RUN/'render-source-card-v1.py')
headers();print('Real local site and shared registry/browser/six cards pass; actual pixel/FINAL/native/PR separate.')
