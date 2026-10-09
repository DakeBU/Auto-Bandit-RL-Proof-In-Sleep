from common import *
import re
sys.path.insert(0,str(ROOT))
from tools.abrl_lifecycle import statement_hash,lean_declaration_header
fixed();assert (CONTRACT/'stabilized-v1.json').exists()
d=load(CONTRACT/'stabilized-v1.json')
for t in d['targets'][:2]:assert statement_hash(lean_declaration_header(PUBLIC,t['declaration']))==t['statement_hash']
assert 'theorem proximal_one_step_extended' not in PUBLIC.read_text(encoding='utf8')
write(RUN/'production-first-leaves-attempt-v1.lean',PUBLIC.read_bytes())
rc,out=capture('focused-first-leaves-build-v1','lake','build','BanditRLProof.OnlineBregmanExtended',required=False)
print(out[-9000:],flush=True)
jobs=re.findall(r'Build completed successfully \((\d+) jobs\)',out)
write(RUN/'first-leaves-attempt-result-v1.json',dict(actual_exit=rc,production_sha256=sha(PUBLIC),compiled=rc==0 and bool(jobs),actual_cached_inclusive_build_jobs=jobs,selected_proofs=2,other_frozen_proof_pending=1,source_container_closed=False,whole_Goal_status='ACTIVE'))
fixed()
