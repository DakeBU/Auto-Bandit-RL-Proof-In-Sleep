from common_v2 import *
fixed();r=bind_review('public-body-receipt-v1.json','public-body-inputs-v1.json','body-binding-audit-v1.json')
assert r['source_convention_verdict']['verdict']=='accepted-with-explicit-delta'
for row in load(RUN/'prior-contract-binding-v1.json')['rows']:assert sha(row['resolved'])==row['sha256']
print('Actual BODY fixed inputs and all immutable original CONTRACT bindings verified; convention qualified.')
