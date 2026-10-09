from proof_driver import *
import re
fixed()
TEST=ROOT/'Tests/OnlinePrescientBregmanSourceCanary.lean'
st=load(CONTRACT/'stabilized-v1.json');cs=load(CONTRACT/'canary-headers-draft-v2.json')
names=[t['name'] for t in st['six_targets']+cs['targets']]
assert load(RUN/'selected-graph-export-v1.json')['actual_exit']==0
old=load(RUN/'two-numeric-branches-v1.json')
assert len(old['rows'])==2 and all(r['required_present'] for r in old['rows'])
write(RUN/'public-audit-orchestration-failure-v1.json',dict(stage='numeric proof selector v1 subprocess completed and wrote output, then capture failed',reason='Command receipt label collided with generated graph output filename. The output JSON exists with two successful required VALUE branches, but subprocess exit was not durably recorded. Do not infer exit0 from output existence. Rerun selector with separate command receipt/output names; preserve all v1 outputs and no production/Test edits.',existing_result=rows([RUN/'two-numeric-branches-v1.json']), prior_driver=rows([RUN/'audit-public-values-v1.py'])))
capture('two-numeric-branches-command-v2','lake','env','lean','--run',RUN/'audit-two-numeric-branches-v1.lean',RUN/'two-numeric-branches-v2.json')
tail=(RUN/'audit-public-values-v1.py').read_text(encoding='utf8').split("g=load(RUN/'selected-value-graph-v1.json')",1)[1]
tail="g=load(RUN/'selected-value-graph-v1.json')"+tail
assert tail.count("load(RUN/'two-numeric-branches-v1.json')")==1
tail=tail.replace("load(RUN/'two-numeric-branches-v1.json')","load(RUN/'two-numeric-branches-v2.json')")
exec(compile(tail,str(RUN/'audit-public-values-v1.py')+' CONTINUATION-v2','exec'))
