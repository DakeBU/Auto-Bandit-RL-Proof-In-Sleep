"""Prepare current immutable raw-audit and PR API adapters before first use."""
from common_v4 import *
old=Path('runs/online-lipschitz-migration-20261007')
t=(old/'audit-committed-raw-v1.py').read_text(encoding='utf-8').replace('from common_v2 import *','from common_v4 import *').replace('codex/research-online-lipschitz-migration','codex/research-online-convex-nondifferentiability').replace('fixed(True)','fixed(True,True)')
write(RUN/'audit-committed-raw-v1.py',t);compile(t,str(RUN/'audit-committed-raw-v1.py'),'exec')
t=(old/'create-pr-v2.py').read_text(encoding='utf-8').replace('from common_v2 import *','from common_v4 import *')
t=t.replace('base-PR175','base-PR176').replace("repo+'/pulls/175'","repo+'/pulls/176'").replace('codex%2Fresearch-online-lipschitz-migration','codex%2Fresearch-online-convex-nondifferentiability')
t=t.replace('codex/research-online-lipschitz-migration','codex/research-online-convex-nondifferentiability').replace('codex/research-online-affine-subgradient-migration','codex/research-online-lipschitz-migration')
assert "repo+'/pulls/176'" in t and 'base-PR176-creation-fresh-v1' in t
write(RUN/'create-pr-v1.py',t);compile(t,str(RUN/'create-pr-v1.py'),'exec')
generated('delivery-adapters-before-use-v1.json',[RUN/'audit-committed-raw-v1.py',RUN/'create-pr-v1.py'])
print('Current exact PR176/remote/duplicate/raw Git tree adapters prepared; no API or push yet.')
