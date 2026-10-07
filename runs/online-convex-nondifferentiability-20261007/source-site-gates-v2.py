"""History/exact-base/clean current lean-verified local site, after combined project gates."""
from common_v4 import *
fixed(True,True);passed('project-gates-v2-01');passed('full-harness-v2-01')
for label in ['contributor-help-v1-01','site-build-help-v1-01','site-check-help-v1-01']:passed(label)
gate('history-bindings-v2-01',sys.executable,'-B','-X','utf8',RUN/'verify-history-bindings-v2.py')
subprocess.run([sys.executable,'-B','-X','utf8',str(RUN/'commit-owned-v1.py'),'Prove source convex nondifferentiability on entire Euclidean segment'],check=True)
gate('contributor-exact-v1-01',sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base',BASE)
try:gate('contributor-main-diagnostic-v1-01',sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base','origin/main')
except subprocess.CalledProcessError:
 assert load(RUN/'contributor-main-diagnostic-v1-01-exit.json')['exit_code']==1
 raw=(RUN/'contributor-main-diagnostic-v1-01.log').read_text(encoding='utf-8');paths=sorted(set(re.findall(r'BanditRLProof/Online\w+\.lean',raw)))
 write(RUN/'main-relative-required-gaps-v1.json',dict(status='failed-separate-main-relative-diagnostic-unwaived',details=raw,missing_required_changed_paths=paths,exact_base_gate_passed=True,required_gaps_not_waived=True,chapter_complete=False,goal_complete=False))
else:raise AssertionError('Main-relative boundary changed; inspectactualresult.')
assert len(load(RUN/'main-relative-required-gaps-v1.json')['missing_required_changed_paths'])==9
subprocess.run([sys.executable,'-B','-X','utf8',str(RUN/'commit-owned-v1.py'),'Bind new example exact contributor and required Chapter1 gaps'],check=True)
gate('scoped-diff-v1-01',sys.executable,'-B','-X','utf8',RUN/'check-scoped-diff-v1.py','v1')
subprocess.run([sys.executable,'-B','-X','utf8',str(RUN/'commit-owned-v1.py'),'Bind source example whitespace before current clean site gate'],check=True)
assert not subprocess.check_output(['git','status','--porcelain'],text=True).strip()
site=Path('tmp/online-convex-nondifferentiability-site-v1')
gate('site-build-v1-01',sys.executable,'-B','-X','utf8','website/scripts/build_site.py','--lean-verified','--output',site)
gate('site-check-v1-01',sys.executable,'-B','-X','utf8','website/scripts/check_site.py','--output',site)
gate('registry-v1-01',sys.executable,'-B','-X','utf8',RUN/'verify-registry-v1.py')
gate('browser-v1-01',sys.executable,'-B','-X','utf8',RUN/'browser-v1.py')
gate('formula-render-v1-01',sys.executable,'-B','-X','utf8',RUN/'render-source-card-v1.py')
fixed(True,True);print('Actualhistory/exactbase/scoped/currentcleanlocalsite/sharedregistry/browserTHREEcards pass; actualpixel/FINAL/native/PRpending.')
