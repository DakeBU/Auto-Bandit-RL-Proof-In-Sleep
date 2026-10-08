from common_v1 import *

write(RUN/'acceptance-guard-schema-repair-v3.json',dict(
    failed_helper='common_accepted_v2.py via read-only accepted_fixed probe',actual_outer_exit=1,
    failure="KeyError before_after_raw_hashes_match; actual reviewer receipt uses raw_input_checks and actual_pixel_review",
    native_acceptance_executed=False,raw_outer_stderr_saved=False,
    repair='Check every actual before/after SHA pair and unchanged flag, actual8pixel rows; preserve original helper. Correct unused acceptance retrieval provenance to actual canary-focused-v2-exit.json.',
    mathematical_target_unchanged=True,goal_complete=False))
s=(RUN/'common_accepted_v2.py').read_text(encoding='utf8')
s=s.replace("assert final['inputs_unchanged'] and final['before_after_raw_hashes_match']",
    "assert final['inputs_unchanged']\n    checks=final['raw_input_checks']\n    assert len(checks)==475 and all(x['unchanged'] and x['before_sha256']==x['after_sha256'] for x in checks)")
s=s.replace("final['actual_original_pixel_reviews']","final['actual_pixel_review']")
write(RUN/'common_accepted_v3.py',s)
s=(RUN/'record-acceptance-v2.py').read_text(encoding='utf8').replace('from common_accepted_v2 import *','from common_accepted_v3 import *')
s=s.replace('canary-focused-build-v2-exit.json','canary-focused-v2-exit.json')
write(RUN/'record-acceptance-v3.py',s)
s=(RUN/'prepare-post-native-review-v2.py').read_text(encoding='utf8').replace('from common_accepted_v2 import *','from common_accepted_v3 import *')
write(RUN/'prepare-post-native-review-v3.py',s)
from common_accepted_v3 import accepted_fixed
assert accepted_fixed()['verdict']=='accepted-with-explicit-delta'
print('Actual FINAL receipt schema checked with475 individual raw pairs and8actual pixel rows; no native command yet.',flush=True)
