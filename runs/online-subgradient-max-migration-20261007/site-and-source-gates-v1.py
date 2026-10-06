from common_v2 import *
fixed(True);passed('project-gates-v1-01');passed('full-harness-v1-01')
gate('history-bindings-v1-01',sys.executable,'-B','-X','utf8',RUN/'verify-history-bindings-v1.py')
# Commit explicit scoped owned paths before diff-aware contributor checking and clean site provenance.
subprocess.run([sys.executable,'-B','-X','utf8',str(RUN/'commit-owned-v1.py'),'Preserve exact finite-maximum contract, proof checks and source reader scope'],check=True)
gate('contributor-exact-v1-01',sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base',BASE)
# This independently reports inherited main-relative required gaps; a nonzero diagnostic must remain visible.
gate('contributor-main-diagnostic-v1-01',sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base','origin/main')
