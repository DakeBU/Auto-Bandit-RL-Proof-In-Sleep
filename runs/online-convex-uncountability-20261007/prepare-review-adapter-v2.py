"""Version packet generator after actual neutral-context repair, original reviewed bytes kept."""
from common_v1 import *
fixed();passed('repair-neutral-context-v2-01');passed('neutral-context-v2-01')
p=RUN/'prepare-review-v1.py';text=p.read_text(encoding='utf-8')
for stem in ['blind-packet','blind-reconstruction','blind-receipt']:text=text.replace(stem+'-v1',stem+'-v2')
text=text.replace("mode.lower()+'-reviewed-'","mode.lower()+'-v2-reviewed-'")
for stem in ['inputs','native-snapshot-bindings','packet','review','receipt']:
 text=text.replace('-'+stem+'-v1','-'+stem+'-v2')
extra='''
The original CONTRACTv1 source-target mathematical review was accepted before a subsequent independent actual standalone-neutral-context audit discovered a missing explicit calculus import (Unknown identifier DifferentiableAt). Original inputs/reconstruction/receipt/log remain immutable. The actual source-qualified target propositions had compiled; no mathematical/header/definition change. Neutral packet revision2 adds pinned Deriv.Abs import, standalone context actual v2 elaborates both exact propositions, and a distinct decoder reconstructed revision2. Separately review repair M1 scoped-context completeness; only mark satisfied with these actual outputs/current v2 reconstruction. The v1 diagnostic unresolved sorry is compiler error output, not a production placeholder/proof closure. Reject if context still incomplete. Frozen mathematical contract remains v1 unchanged; this is version2 review of metadata repair, not a silently weakened terminal.
'''
text=text.replace("if mode=='CONTRACT':packet+=",'packet+='+repr(extra)+"\nif mode=='CONTRACT':packet+=")
write(RUN/'prepare-review-v2.py',text)
write(RUN/'review-adapter-before-first-use-v2.json',dict(original_generator=p.as_posix(),original_sha256=sha(p),effective_generator=(RUN/'prepare-review-v2.py').as_posix(),effective_sha256=sha(RUN/'prepare-review-v2.py'),change='Only neutral packet/receipt/reconstruction v2 and unique v2 outputs/snapshot names; separate actual context-repair review instructions; math targets and contract unchanged.',source_package_accepted=False,chapter_complete=False,goal_complete=False))
print('Version2 bounded review adapter prepared before first use; original reviewed generator unchanged.')
