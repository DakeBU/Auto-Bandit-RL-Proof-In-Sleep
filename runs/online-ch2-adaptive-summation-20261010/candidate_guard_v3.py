from candidate_guard_v2 import *
from gate_receipt_guard_v3 import actual_gates_fixed, gate_binding_review_fixed
prior_candidate_fixed=candidate_fixed

def candidate_fixed():
    prior_candidate_fixed()
    gate_binding_review_fixed(after=True)
