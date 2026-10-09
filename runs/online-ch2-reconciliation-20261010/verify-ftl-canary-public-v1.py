from ftl_canary_proof import *
canary_fixed()
code,out=capture('ftl-canary-lake-build-v1','lake','build','Tests.OnlineFTLSelectorCanary',required=False)
print(out)
assert code==0
canary_fixed()
code,out=capture('ftl-canary-public-and-axioms-v1','lake','env','lean',RUN/'FTLCanaryPublicProbeV1.lean',required=False)
print(out)
assert code==0
canary_fixed()
