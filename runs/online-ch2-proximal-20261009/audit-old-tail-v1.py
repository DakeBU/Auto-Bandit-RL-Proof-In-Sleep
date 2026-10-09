from common import *
fixed()
assert sha(ROOT/'Tests/OnlineProximalComparisonCanary.lean')=='d7e8e04a4d0502428fd8a2805fe9c80b457d117559213ed2bd586a4ba385d441'
code,out=capture('numeric-old-tail-command-v1','lake','env','lean','--run',RUN/'audit-numeric-tail-v1.lean',RUN/'numeric-old-tail-data-v1.json',required=False)
print(out[-6000:])
if code==0:print([(x['declaration'],x['selected_tail_head'],x['public_helper_in_selected_tail']) for x in load(RUN/'numeric-old-tail-data-v1.json')['rows']])
