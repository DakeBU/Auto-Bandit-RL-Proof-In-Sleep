from common import *
import runpy
v=runpy.run_path(str(RUN/'verify-candidate-plan-v1.py'))['verify_candidate_plan']
for label,helper in [('candidate-stage-driver-v1','stage-candidate-v1.py'),('full-harness-retry-driver-v2','run-full-harness-v2.py')]:
    v();capture(label,sys.executable,'-B','-X','utf8',RUN/helper)
