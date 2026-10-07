"""Final current-reader rerun after preserved bridge/primer schema failures."""
from common_v4 import *
fixed(True,True)
for label in ['project-gates-v2-01','history-bindings-v2-01','repair-notation-primer-v2-01']:passed(label)
for p,d in load(RUN/'combined-project-gates-v2.json')['source_hashes'].items():assert sha(p)==d,p
subprocess.run([sys.executable,'-B','-X','utf8',str(RUN/'commit-owned-v1.py'),'Conserve ambient primer explanations within existing site schema'],check=True)
gate('full-harness-v3-01',sys.executable,'-B','-X','utf8','tools/bandit.py','check')
gate('contributor-exact-v4-01',sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base',BASE)
gate('scoped-diff-v3-01',sys.executable,'-B','-X','utf8',RUN/'check-scoped-diff-v1.py','v3')
subprocess.run([sys.executable,'-B','-X','utf8',str(RUN/'commit-owned-v1.py'),'Bind final reader full harness contributor and scoped checks'],check=True)
assert not subprocess.check_output(['git','status','--porcelain'],text=True).strip()
site=Path('tmp/online-convex-nondifferentiability-site-v1')
gate('site-build-v3-01',sys.executable,'-B','-X','utf8','website/scripts/build_site.py','--lean-verified','--output',site)
gate('site-check-v2-01',sys.executable,'-B','-X','utf8','website/scripts/check_site.py','--output',site)
gate('registry-v2-01',sys.executable,'-B','-X','utf8',RUN/'verify-registry-v2.py')
gate('browser-v1-01',sys.executable,'-B','-X','utf8',RUN/'browser-v1.py')
gate('formula-render-v1-01',sys.executable,'-B','-X','utf8',RUN/'render-source-card-v1.py')
fixed(True,True);print('Actual current reader full harness/clean site/shared registry/three-card rendering pass; pixels/FINAL/native/PR remain separate.')
