"""Actual scoped preservation and clean local site after current combined Lean gates."""
from common_v2 import *
fixed(True);passed('project-gates-v1-01');passed('prepare-site-adapters-v1-01');passed('full-harness-v3-01')
subprocess.run([sys.executable,'-B','-X','utf8',str(RUN/'commit-owned-v1.py'),'Audit existing canonical projected OSD source chain and reader contract'],check=True)
gate('contributor-exact-v3-01',sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base',BASE)
gate('scoped-diff-v3-01',sys.executable,'-B','-X','utf8',RUN/'check-scoped-diff-v1.py','v3')
gate('source-scope-v3-01',sys.executable,'-B','-X','utf8',RUN/'audit-scope-v1.py')
q=subprocess.run([sys.executable,'-B','-X','utf8',str(RUN/'run-command.py'),'main-relative-diagnostic-v2-01',sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base','origin/main']);assert q.returncode in [0,1]
write(RUN/'main-relative-diagnostic-v2.json',dict(status='passed' if q.returncode==0 else 'failed-unwaived',actual_exit_code=q.returncode,raw_log_sha256=sha(RUN/'main-relative-diagnostic-v2-01.log'),exact_current_PR178_base_gate_separately_passed=True,prior_other_Chapter1_gaps_remain_required=True,not_a_gate_waiver=True,chapter_complete=False,goal_complete=False))
subprocess.run([sys.executable,'-B','-X','utf8',str(RUN/'commit-owned-v1.py'),'Bind exact-base OSD scope and current contributor evidence'],check=True)
assert not subprocess.check_output(['git','status','--porcelain'],text=True).strip()
site=Path('tmp/online-osd-public-site-v2')
gate('site-build-v2-01',sys.executable,'-B','-X','utf8','website/scripts/build_site.py','--lean-verified','--output',site)
gate('site-check-v2-01',sys.executable,'-B','-X','utf8','website/scripts/check_site.py','--output',site)
gate('registry-v2-01',sys.executable,'-B','-X','utf8',RUN/'verify-registry-v2.py')
gate('browser-v2-01',sys.executable,'-B','-X','utf8',RUN/'browser-v2.py')
gate('formula-render-v2-01',sys.executable,'-B','-X','utf8',RUN/'render-source-card-v2.py')
fixed(True);print('Actual clean Leanverified sharedsite/unchanged registry/six rendered cards passed; pixel/FINAL/native/PR pending.')
