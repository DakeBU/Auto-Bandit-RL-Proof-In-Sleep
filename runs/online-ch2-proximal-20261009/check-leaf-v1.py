from common import *
sys.path.insert(0,str(ROOT))
from tools.abrl_lifecycle import statement_hash,lean_declaration_header
fixed();t=load(CONTRACT/'stabilized-v1.json')['targets'][0]
assert statement_hash(lean_declaration_header(PUBLIC,t['declaration']))==t['statement_hash']
write(RUN/'first-body-v1.raw',PUBLIC.read_bytes())
code,out=capture('focused-build-v1','lake','build','BanditRLProof.OnlineProximalComparison',required=False)
write(RUN/'focused-build-inspected-v1.json',dict(actual_exit=code,compiled=code==0 and 'Build completed successfully' in out,body_sha256=sha(PUBLIC),statement_hash=t['statement_hash'],no_source_container_closure=True,whole_Goal_status='ACTIVE'))
print(out[-9000:]);fixed()
