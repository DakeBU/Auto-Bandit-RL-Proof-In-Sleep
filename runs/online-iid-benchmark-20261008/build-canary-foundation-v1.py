from common_reviewed_v2 import *
headers_fixed(8)
write(RUN / 'eight-compiled-public-v2.lean.raw', PUBLIC.read_bytes())
write(RUN / 'canary-foundation-candidate-v1.lean.raw', CANARY.read_bytes())
write(RUN / 'canary-foundation-scope-v1.json', dict(
    scope='Actual fair real-coordinate IID infinite product; positive variance, a.s.-only support, exact expected fixed minimum and actual strict-past meanPredict excess.',
    theorem_count=18, public_headers_unchanged=True, package_accepted=False, chapter_complete=False, goal_complete=False))
gate('canary-foundation-focused-build-v1', 'lake', 'build', 'Tests.OnlineGuessingIIDBenchmarkCanary')
