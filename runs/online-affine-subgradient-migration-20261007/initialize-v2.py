"""Initialize exact wrappers before bootstrap; retain the failed shell quoting diagnostic."""
from pathlib import Path
import hashlib,json
r=Path(__file__).resolve().parent;old=Path('runs/online-hinge-migration-20261007')
def write(p,x):
 assert not p.exists(),p;p.write_bytes(x if isinstance(x,bytes) else (json.dumps(x,indent=2)+'\n').encode())
p=r/'bootstrap-v1.py';compile(p.read_text(encoding='utf-8'),str(p),'exec')
write(r/'bootstrap-before-use-v1.json',dict(before_first_use=True,path=p.as_posix(),sha256=hashlib.sha256(p.read_bytes()).hexdigest()))
write(r/'run-command.py',(old/'run-command.py').read_bytes())
t=(old/'common_v2.py').read_text(encoding='utf-8').replace('online-hinge-migration-v1','online-affine-subgradient-migration-v1').replace('ONLINE-HINGE-MIGRATION-20261007','ONLINE-AFFINE-SUBGRADIENT-MIGRATION-20261007').replace("ROUTE='online-hinge'","ROUTE='online-affine-subgradient'").replace('OnlineHinge','OnlineAffineSubgradient').replace('8375aa0353a4230ec23c0ccbb8f337a16246c134','42da35d05a3cbc26f5ec6b5082ef9135b7d7caf7')
compile(t,'common_v2.py','exec');write(r/'common_v2.py',t.encode())
write(r/'initialization-quoting-diagnostic-v1.json',dict(chunk='4eccf4',action='inline shell Python preparation',actual_error='SyntaxError unexpected EOF due PowerShell nested quote transport; follow-on wrapper absent; bootstrap never executed',mathematical_or_Lean_failure=False,reviewed_file_mutation=False,repair='separate version2 saved Python initializer before bootstrap first use'))
print('Safe saved initialization complete; bootstrap not yet used.')
