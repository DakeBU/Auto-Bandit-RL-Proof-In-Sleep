from common import *
sys.path.insert(0,str(ROOT))
from tools.abrl_lifecycle import statement_hash,lean_declaration_header
fixed();d=load(CONTRACT/'stabilized-v1.json')
for t in d['targets']:assert statement_hash(lean_declaration_header(PUBLIC,t['declaration']))==t['statement_hash'],t['declaration']
write(RUN/'production-complete-attempt-v1.lean',PUBLIC.read_bytes())
rc,out=capture('focused-complete-build-v1','lake','build','BanditRLProof.OnlineBregmanExtended',required=False)
print(out[-9000:],flush=True);fixed()
