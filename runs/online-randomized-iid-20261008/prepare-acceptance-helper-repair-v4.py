from common_integrated_v2 import *

fixed_integrated()
old = RUN/'record-acceptance-v3.py'
new = RUN/'record-acceptance-v4.py'
before = b'Distinct staged decoder/CONTRACT1143/BODY1582/FINAL1822 accepted with exactR1-R7;'
after = b'Decoder reconstruction recorded; distinct CONTRACT1143/BODY1582/FINAL1822 source reviews accepted-with-explicit-delta with exactR1-R7;'
raw = old.read_bytes()
assert raw.count(before) == 1
write(new, raw.replace(before, after))
write(RUN/'acceptance-helper-review-repair-v4.json', dict(
    original_unexecuted_helper=old.name, original_sha256=sha(old),
    operative_helper=new.name, operative_sha256=sha(new),
    delta='Only digest wording distinguishes decoder reconstruction from source-review acceptance.',
    native_output_version='v3 phase labels remain prospective and have never executed.',
    prior_helper_must_never_execute=True, FINAL_pending=True, native_acceptance_pending=True,
    public_canary_readers_unchanged=True, chapter_complete=False, goal_complete=False))
print('Distinct review roles clarified in a new unexecuted helper; original bytes retained.')
