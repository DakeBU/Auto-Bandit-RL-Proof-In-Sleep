"""Gate scoped history/diff/contributor and build a clean local site after real Lean gates."""
from common_v2 import *
fixed(True);passed('project-gates-v1-01');passed('full-harness-v1-01')
gate('history-bindings-v1-01',sys.executable,'-B','-X','utf8',RUN/'verify-history-bindings-v1.py')
subprocess.run([sys.executable,'-B','-X','utf8',str(RUN/'commit-owned-v1.py'),'Qualify exact hinge producer, source reader and current integrated Lean evidence'],check=True)
gate('contributor-exact-v1-01',sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base',BASE)
try:
 gate('contributor-main-diagnostic-v1-01',sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base','origin/main')
except subprocess.CalledProcessError:
 main=load(RUN/'contributor-main-diagnostic-v1-01-exit.json');assert main['exit_code']!=0
else:
 raise AssertionError('Main-relative required-gap boundary changed: review before proceeding.')
raw=(RUN/'contributor-main-diagnostic-v1-01.log').read_text(encoding='utf-8');missing=sorted(set(re.findall(r'BanditRLProof/Online\w+\.lean',raw)));assert len(missing)==9
write(RUN/'main-relative-required-gaps-v1.json',dict(status='failed-separate-main-diagnostic',exit_code=main['exit_code'],missing_required_changed_paths=missing,required_gaps_not_waived=True,exact_stack_base_contributor_passed=True,not_Lean_failure=True,chapter_complete=False,goal_complete=False))
subprocess.run([sys.executable,'-B','-X','utf8',str(RUN/'commit-owned-v1.py'),'Bind exact hinge contribution checks and unwaived Chapter1 main-relative gaps'],check=True)
gate('scoped-diff-v1-01',sys.executable,'-B','-X','utf8',RUN/'check-scoped-diff-v1.py','v1')
subprocess.run([sys.executable,'-B','-X','utf8',str(RUN/'commit-owned-v1.py'),'Bind scoped hinge whitespace before clean lean-verified site build'],check=True)
assert not subprocess.check_output(['git','status','--porcelain'],encoding='utf-8').strip();fixed(True)
gate('site-build-v1-01',sys.executable,'-B','-X','utf8','website/scripts/build_site.py','--lean-verified','--output','tmp/online-hinge-migration-site-v1')
gate('site-check-v1-01',sys.executable,'-B','-X','utf8','website/scripts/check_site.py','--output','tmp/online-hinge-migration-site-v1')
gate('registry-v1-01',sys.executable,'-B','-X','utf8',RUN/'verify-registry-v1.py')
gate('browser-v1-01',sys.executable,'-B','-X','utf8',RUN/'browser-v1.py')
print('Applicable clean local site/check/registry and actual firstviewport captured; sourceformula pixels/FINAL/PR still separate.')
