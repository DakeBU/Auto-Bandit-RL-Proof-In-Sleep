from common import *
from candidate_execution_guard_v2 import candidate_plan_fixed
for label,helper in [('candidate-restage-driver-v2','restage-candidate-v2.py'),('full-harness-retry-driver-v2','run-full-harness-v2.py')]:
    candidate_plan_fixed();capture(label,sys.executable,'-B','-X','utf8',RUN/helper)
