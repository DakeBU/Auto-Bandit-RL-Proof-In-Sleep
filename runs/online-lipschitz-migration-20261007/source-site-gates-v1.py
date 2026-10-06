"""Actual exact-base/history gates and clean applicable site AFTER current combined gates."""
from common_v2 import *
fixed(True);passed('project-gates-v1-01')
for label in ['contributor-help-v1-01','site-build-help-v1-01','site-check-help-v1-01']:passed(label)
gate('history-bindings-v1-01',sys.executable,'-B','-X','utf8',RUN/'verify-history-bindings-v1.py')
subprocess.run([sys.executable,'-B','-X','utf8',str(RUN/'commit-owned-v1.py'),'Qualify retained Lipschitz definition and full interior theorem with current integrated Lean evidence'],check=True)
gate('contributor-exact-v1-01',sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base',BASE)
try:gate('contributor-main-diagnostic-v1-01',sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base','origin/main')
except subprocess.CalledProcessError:
 assert load(RUN/'contributor-main-diagnostic-v1-01-exit.json')['exit_code']==1
 raw=(RUN/'contributor-main-diagnostic-v1-01.log').read_text(encoding='utf-8')
 write(RUN/'main-relative-required-gaps-v1.json',dict(status='failed-separate-main-relative-diagnostic-unwaived',exact_base_gate_passed=True,main_relative_failure_log='contributor-main-diagnostic-v1-01.log',details=raw,missing_required_changed_paths=sorted(set(re.findall(r'BanditRLProof/Online\w+\.lean',raw))),required_gaps_not_waived=True,remaining_other_Chapter1_contract_gaps_required=True,not_a_Lean_or_statement_failure=True,chapter_complete=False,goal_complete=False))
else:raise AssertionError('Main-relative boundary changed; audit actual result instead of assuming historical gaps.')
assert len(load(RUN/'main-relative-required-gaps-v1.json')['missing_required_changed_paths'])==9
subprocess.run([sys.executable,'-B','-X','utf8',str(RUN/'commit-owned-v1.py'),'Bind exact Lipschitz contribution gate and unwaived Chapter1 main-relative gaps'],check=True)
gate('scoped-diff-v1-01',sys.executable,'-B','-X','utf8',RUN/'check-scoped-diff-v1.py','v1')
subprocess.run([sys.executable,'-B','-X','utf8',str(RUN/'commit-owned-v1.py'),'Bind scoped Lipschitz whitespace before clean applicable lean-verified site'],check=True)
assert not subprocess.check_output(['git','status','--porcelain'],encoding='utf-8').strip()
site=Path('tmp/online-lipschitz-migration-site-v1')
gate('site-build-v1-01',sys.executable,'-B','-X','utf8','website/scripts/build_site.py','--lean-verified','--output',site)
gate('site-check-v1-01',sys.executable,'-B','-X','utf8','website/scripts/check_site.py','--output',site)
gate('registry-v1-01',sys.executable,'-B','-X','utf8',RUN/'verify-registry-v1.py')
gate('browser-v1-01',sys.executable,'-B','-X','utf8',RUN/'browser-v1.py')
fixed(True);print('Exactbase/history/scoped/site/sharedregistry/taskbrowser pass; main-relative requiredgaps retained, no FINAL/package acceptance.')
