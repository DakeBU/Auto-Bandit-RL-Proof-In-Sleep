"""Continue actual pending site gates after preserved v1 bridge-schema rejection."""
from common_v4 import *
fixed(True,True)
for label in ['project-gates-v2-01','full-harness-v2-01','history-bindings-v2-01','contributor-exact-v2-01','scoped-diff-v1-01','repair-proof-bridge-v2-01']:passed(label)
assert len(load(RUN/'main-relative-required-gaps-v1.json')['missing_required_changed_paths'])==9
subprocess.run([sys.executable,'-B','-X','utf8',str(RUN/'commit-owned-v1.py'),'Conserve source proof explanations within existing reader schema'],check=True)
gate('contributor-exact-v3-01',sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base',BASE)
gate('scoped-diff-v2-01',sys.executable,'-B','-X','utf8',RUN/'check-scoped-diff-v1.py','v2')
subprocess.run([sys.executable,'-B','-X','utf8',str(RUN/'commit-owned-v1.py'),'Bind reader repair contributor and scoped diff checks'],check=True)
assert not subprocess.check_output(['git','status','--porcelain'],text=True).strip()
site=Path('tmp/online-convex-nondifferentiability-site-v1')
gate('site-build-v2-01',sys.executable,'-B','-X','utf8','website/scripts/build_site.py','--lean-verified','--output',site)
gate('site-check-v1-01',sys.executable,'-B','-X','utf8','website/scripts/check_site.py','--output',site)
gate('registry-v1-01',sys.executable,'-B','-X','utf8',RUN/'verify-registry-v1.py')
gate('browser-v1-01',sys.executable,'-B','-X','utf8',RUN/'browser-v1.py')
gate('formula-render-v1-01',sys.executable,'-B','-X','utf8',RUN/'render-source-card-v1.py')
fixed(True,True);print('Actual clean current site/shared registry and all three source-card renders pass; actual pixels/FINAL/native/PR pending.')
