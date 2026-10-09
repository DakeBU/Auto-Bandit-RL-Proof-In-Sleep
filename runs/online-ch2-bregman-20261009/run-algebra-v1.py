from common import *
fixed()
write(RUN/'production-algebra-attempt-v1.lean',PUBLIC.read_bytes())
rc,out=capture('focused-algebra-build-v1','lake','build','BanditRLProof.OnlineBregmanProximal',required=False)
write(RUN/'algebra-attempt-result-v1.json',dict(actual_exit=rc,production_sha256=sha(PUBLIC),compiled=rc==0,selected_proofs=2,other_frozen_proofs_pending=3,source_container_closed=False,whole_Goal_status='ACTIVE'))
fixed()
