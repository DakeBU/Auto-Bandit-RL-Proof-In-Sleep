from common import *
fixed()
write(RUN/'implementation-repair-v2.json',dict(failure_receipt='focused-complete-build-v1.json',actual_exit=1,cause='Unrestricted simp normalizes the target derivative of a translated linear map but leaves the composed function on the retrieved term. Implementation elaboration mismatch, not mathematical counterexample.',repair='Use simp only Function.comp_def and ContinuousLinearMap.comp_id on the actual composition derivative.',targets_changed=False,definition_changed=False,source_assumptions_changed=False))
write(RUN/'production-complete-attempt-v2.lean',PUBLIC.read_bytes())
rc,out=capture('focused-complete-build-v2','lake','build','BanditRLProof.OnlineBregmanProximal',required=False)
print(out[-8000:],flush=True)
fixed()
