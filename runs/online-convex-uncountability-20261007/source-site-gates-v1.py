"""Actual exact-base/scope/clean local site gates after current combined Lean gate."""
from common_v2 import *
fixed(True,True);passed('project-gates-v1-01');passed('prepare-site-adapters-v1-01')
subprocess.run([sys.executable,'-B','-X','utf8',str(RUN/'commit-owned-v1.py'),'Prove same convex source function has uncountably many nonsmooth points'],check=True)
gate('contributor-exact-v1-01',sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base',BASE)
gate('scoped-diff-v1-01',sys.executable,'-B','-X','utf8',RUN/'check-scoped-diff-v1.py','v1')
gate('source-scope-v1-01',sys.executable,'-B','-X','utf8',RUN/'audit-scope-v1.py')
q=subprocess.run([sys.executable,'-B','-X','utf8',str(RUN/'run-command.py'),'main-relative-diagnostic-v1-01',sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base','origin/main'])
assert q.returncode in [0,1]
write(RUN/'main-relative-diagnostic-v1.json',dict(status='passed' if q.returncode==0 else 'failed-unwaived',actual_exit_code=q.returncode,raw_log_sha256=sha(RUN/'main-relative-diagnostic-v1-01.log'),exact_current_PR_base_gate_separately_passed=True,prior_Chapter1_gaps_remain_required=True,not_a_gate_waiver=True,chapter_complete=False,goal_complete=False))
subprocess.run([sys.executable,'-B','-X','utf8',str(RUN/'commit-owned-v1.py'),'Bind sourcequalified proof scope and contributor gates'],check=True)
assert not subprocess.check_output(['git','status','--porcelain'],text=True).strip()
site=Path('tmp/online-convex-uncountability-site-v1')
gate('site-build-v1-01',sys.executable,'-B','-X','utf8','website/scripts/build_site.py','--lean-verified','--output',site)
gate('site-check-v1-01',sys.executable,'-B','-X','utf8','website/scripts/check_site.py','--output',site)
gate('registry-v1-01',sys.executable,'-B','-X','utf8',RUN/'verify-registry-v1.py')
gate('browser-v1-01',sys.executable,'-B','-X','utf8',RUN/'browser-v1.py')
gate('formula-render-v1-01',sys.executable,'-B','-X','utf8',RUN/'render-source-card-v1.py')
fixed(True,True);print('Actual clean Leanverified sharedsite/registry/four rendered cards passed; actual pixels/FINAL/native/PR pending.')
