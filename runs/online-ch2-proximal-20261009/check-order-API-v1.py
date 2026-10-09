from common import *
fixed()
code,out=capture('order-API-v1','lake','env','lean',RUN/'OrderAPIProbe.lean',required=False)
print(out)
