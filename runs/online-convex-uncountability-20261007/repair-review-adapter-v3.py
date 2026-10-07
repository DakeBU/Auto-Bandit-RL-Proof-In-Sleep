"""Preserve a failed packet-version adapter and correct only an older receipt reference."""
from common_v1 import *
fixed();assert load(RUN/'prepare-contract-review-v2-01-exit.json')['exit_code']==1
p=RUN/'prepare-review-v2.py';text=p.read_text(encoding='utf-8')
assert "'final-reader-receipt-v2.json'" in text
text=text.replace("'final-reader-receipt-v2.json'","'final-reader-receipt-v1.json'")
text=text.replace("mode.lower()+'-v2-reviewed-'","mode.lower()+'-v3-reviewed-'")
for stem in ['inputs','native-snapshot-bindings','packet','review','receipt']:
 text=text.replace("stem+'-"+stem+'-v2',"stem+'-"+stem+'-v3').replace('{stem}-'+stem+'-v2','{stem}-'+stem+'-v3')
write(RUN/'prepare-review-v3.py',text)
write(RUN/'review-adapter-repair-v3.json',dict(status='adapter-reference-repair-only',failed_attempt='prepare-contract-review-v2-01',error='Blind/context output-version substitution also changed the referenced PRIOR accepted dependency final-reader-receipt filename.',repair='Reference actual prior final-reader-receipt-v1.json; use unique v3 own packet/input/snapshot outputs, retain blind v2 and frozen math contract v1.',original_failed_generator_sha256=sha(p),effective_generator_sha256=sha(RUN/'prepare-review-v3.py'),all_failed_partial_outputs_preserved=True,mathematical_targets_unchanged=True,source_package_accepted=False,chapter_complete=False,goal_complete=False))
print('Actual packet adapter failure preserved; prior receipt reference corrected in v3 before use.')
