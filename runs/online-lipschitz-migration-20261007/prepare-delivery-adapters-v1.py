"""Prepare exact parent/remote/raw audit adapters before any PR API or push use."""
from common_v2 import *
old=Path('runs/online-affine-subgradient-migration-20261007')
t=(old/'audit-committed-raw-v1.py').read_text(encoding='utf-8').replace('codex/research-online-affine-subgradient-migration','codex/research-online-lipschitz-migration')
write(RUN/'audit-committed-raw-v1.py',t);compile(t,str(RUN/'audit-committed-raw-v1.py'),'exec')
t=(old/'create-pr-v1.py').read_text(encoding='utf-8')
t=t.replace('base-PR174','base-PR175').replace("repo+'/pulls/174'","repo+'/pulls/175'").replace('codex%2Fresearch-online-affine-subgradient-migration','codex%2Fresearch-online-lipschitz-migration')
t=t.replace('codex/research-online-affine-subgradient-migration','codex/research-online-lipschitz-migration').replace('codex/research-online-hinge-migration','codex/research-online-affine-subgradient-migration')
assert "repo+'/pulls/175'" in t and 'base-PR175' in t
write(RUN/'create-pr-v1.py',t);compile(t,str(RUN/'create-pr-v1.py'),'exec')
generated('delivery-adapters-before-use-v1.json',[RUN/'audit-committed-raw-v1.py',RUN/'create-pr-v1.py'])
print('ExactPR175/duplicate/currentremote/rawGit-tree adapters prepared; no push/API yet.')
