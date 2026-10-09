from common import *
fixed()
p=ROOT/'Tests/OnlineBregmanProximalCanary.lean'
write(RUN/'canary-implementation-repair-v2.json',dict(failed_receipt='focused-canary-build-v1.json',actual_exit=1,causes=['Actual strict-convex power API is in pinned SpecificFunctions.Deriv and has no generic scalar argument','Polynomial derivative convert leaves id z unreduced','Real inner simplification requires its concrete instance/API from InnerProductSpace.Basic'],repair='Add pinned imports; remove inapplicable scalar named argument; dsimp id in polynomial derivative conversions.',theorem_headers_changed=False,production_changed=False,source_changed=False))
write(RUN/'canary-attempt-v2.lean',p.read_bytes())
rc,out=capture('focused-canary-build-v2','lake','build','Tests.OnlineBregmanProximalCanary',required=False)
print(out[-11000:],flush=True)
fixed()
