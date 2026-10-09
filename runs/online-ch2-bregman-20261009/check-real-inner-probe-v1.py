from common import *
fixed()
rc,out=capture('real-inner-API-probe-v1','lake','env','lean',RUN/'RealInnerProbe-v1.lean',required=False)
print(out[-12000:],flush=True)
fixed()
