"""Actual historical/source gates, clean applicable site, and task-owned browser evidence."""
from common_v2 import *
fixed(True);passed('project-gates-v1-01')
gate('history-bindings-v1-01',sys.executable,'-B','-X','utf8',RUN/'verify-history-bindings-v1.py')
subprocess.run([sys.executable,'-B','-X','utf8',str(RUN/'commit-owned-v1.py'),'Qualify exact affine producer, source reader and current integrated Lean evidence'],check=True)
gate('contributor-exact-v1-01',sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base',BASE)
try:gate('contributor-main-diagnostic-v1-01',sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base','origin/main')
except subprocess.CalledProcessError:
 assert load(RUN/'contributor-main-diagnostic-v1-01-exit.json')['exit_code']==1
 raw=(RUN/'contributor-main-diagnostic-v1-01.log').read_text(encoding='utf-8')
 write(RUN/'main-relative-required-gaps-v1.json',dict(status='failed-separate-main-relative-diagnostic-unwaived',exact_base_gate_passed=True,main_relative_failure_log='contributor-main-diagnostic-v1-01.log',details=raw,remaining_other_Chapter1_contract_gaps_required=True,not_a_Lean_or_statement_failure=True,chapter_complete=False,goal_complete=False))
else:raise AssertionError('Historical main-relative boundary changed; audit current result rather than invent expected gaps.')
subprocess.run([sys.executable,'-B','-X','utf8',str(RUN/'commit-owned-v1.py'),'Bind exact affine contribution checks and unwaived Chapter1 main-relative gaps'],check=True)
gate('scoped-diff-v1-01',sys.executable,'-B','-X','utf8',RUN/'check-scoped-diff-v1.py','v1')
subprocess.run([sys.executable,'-B','-X','utf8',str(RUN/'commit-owned-v1.py'),'Bind scoped affine whitespace before clean applicable lean-verified site'],check=True)
assert not subprocess.check_output(['git','status','--porcelain'],encoding='utf-8').strip()
site=Path('tmp/online-affine-subgradient-migration-site-v1')
gate('site-build-v1-01',sys.executable,'-B','-X','utf8','website/scripts/build_site.py','--lean-verified','--output',site)
gate('site-check-v1-01',sys.executable,'-B','-X','utf8','website/scripts/check_site.py','--site',site)
gate('registry-v1-01',sys.executable,'-B','-X','utf8',RUN/'verify-registry-v1.py')
gate('browser-v1-01',sys.executable,'-B','-X','utf8',RUN/'browser-v1.py')
fixed(True);print('Exact historical/contribution/scoped/site/sharedregistry/task-owned browser passed; separate main-relative diagnostic retained unwaived.')
