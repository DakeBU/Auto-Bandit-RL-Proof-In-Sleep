"""Prepare reusable evidence/gate adapters without changing source/math or old receipts."""
from common_v2 import *
old=Path('runs/online-affine-subgradient-migration-20261007')
for name in ['commit-owned-v1.py','check-scoped-diff-v1.py','browser-v1.py','render-source-card-v1.py','prepare-site-CLI-v1.py']:
 t=(old/name).read_text(encoding='utf-8').replace('OnlineAffineSubgradient','OnlineLipschitzSubgradient').replace('online-affine-subgradient','online-lipschitz').replace('ONLINE-AFFINE-SUBGRADIENT','ONLINE-LIPSCHITZ').replace('42da35d05a3cbc26f5ec6b5082ef9135b7d7caf7',BASE).replace('manifest-before-affine-entry','manifest-before-lipschitz-entry')
 if name=='check-scoped-diff-v1.py':t=t.replace("p.endswith('/source-printed18-pdf30.txt')","p.endswith('/source-printed18-pdf30.txt') or p.endswith('/source-printed19-pdf31.txt')")
 compile(t,str(RUN/name),'exec');write(RUN/name,t)
t=(old/'verify-history-bindings-v1.py').read_text(encoding='utf-8')
t=t.replace('arun=Path(__file__).parent;',"lrun=Path(__file__).parent;arun=Path('runs/online-affine-subgradient-migration-20261007');")
needle="str(arun/'historical-raw-supersession-body-v1.json')]:"
addition="str(arun/'historical-raw-supersession-body-v1.json'),str(arun/'historical-raw-supersession-final-v1.json'),str(lrun/'historical-raw-supersession-v1.json'),str(lrun/'historical-raw-supersession-contract-v1.json'),str(lrun/'historical-raw-supersession-body-v1.json')]:"
assert needle in t;t=t.replace(needle,addition)
t=t.replace("receipts=[arun/", "receipts=[lrun/'source-contract-receipt-v1.json',lrun/'public-body-receipt-v1.json',arun/'final-reader-receipt-v1.json',arun/")
t=t.replace("load(arun/'historical-raw-supersession-v1.json')","load(lrun/'historical-raw-supersession-v1.json')").replace('out=arun/','out=lrun/').replace("'online-affine-subgradient'","'online-lipschitz'").replace('only_online_affine_subgradient_subtree_changed','only_online_lipschitz_subtree_changed').replace('selected Theorem2.28 affine subtree only','selected Definition2.29/Theorem2.30 Lipschitz subtree only')
assert "arun=Path('runs/online-affine-subgradient-migration-20261007')" in t and 'out=lrun/' in t
compile(t,str(RUN/'verify-history-bindings-v1.py'),'exec');write(RUN/'verify-history-bindings-v1.py',t)
helpers=[RUN/n for n in ['commit-owned-v1.py','check-scoped-diff-v1.py','browser-v1.py','render-source-card-v1.py','prepare-site-CLI-v1.py','verify-history-bindings-v1.py']]
generated('current-gate-adapters-before-use-v1.json',helpers)
print('Exact scoped adapters and actual original receipt resolver prepared; currentreader/BODY stillpending.')
