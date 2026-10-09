from common import *
fixed()
p=ROOT/'Tests/OnlineBregmanProximalCanary.lean'
write(RUN/'canary-implementation-repair-v3.json',dict(failed_receipt='focused-canary-build-v2.json',actual_exit=1,cause='Concrete real inner instance synthesizes RCLike.toInnerProductSpaceReal; simp indexing does not match the generic RCLike.inner_apply prime instance. Adding Basic alone did not resolve matching. All other strictness/minimum/derivative/numeric body goals succeeded.',actual_API_probe='real-inner-API-probe-v1.json actual0 proves exact generic inner lemma elaborates against the concrete real instance',repair='Use an explicitly typed show equality from the retrieved RCLike.inner_apply prime term, then rw that equality. No suppression, simp weakening or target change.',theorem_headers_changed=False,production_changed=False,source_changed=False))
write(RUN/'canary-attempt-v3.lean',p.read_bytes())
rc,out=capture('focused-canary-build-v3','lake','build','Tests.OnlineBregmanProximalCanary',required=False)
print(out[-11000:],flush=True)
fixed()
