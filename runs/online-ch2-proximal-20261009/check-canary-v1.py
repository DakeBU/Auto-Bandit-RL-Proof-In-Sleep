from common import *
sys.path.insert(0,str(ROOT))
from tools.abrl_lifecycle import statement_hash,lean_declaration_header
fixed();p=ROOT/'Tests/OnlineProximalComparisonCanary.lean'
assert sha(PUBLIC)=='04dae0024d9a2b61016b4652767f4d678725325a040a02c62680a202ec2593d2'
for t in load(CONTRACT/'canary-stabilized-v1.json')['targets']:assert statement_hash(lean_declaration_header(p,t['declaration']))==t['statement_hash'],t['declaration']
write(RUN/'canary-first-body-v1.raw',p.read_bytes())
code,out=capture('focused-canary-build-v1','lake','build','Tests.OnlineProximalComparisonCanary',required=False)
write(RUN/'focused-canary-inspected-v1.json',dict(actual_exit=code,compiled=code==0 and 'Build completed successfully' in out,production_sha256=sha(PUBLIC),test_sha256=sha(p),frozen3headers=True,actual_VALUE_dependencies_pending=True,source_container_closed=False,chapter_complete=False,whole_Goal_status='ACTIVE'))
print(out[-12000:]);fixed()
