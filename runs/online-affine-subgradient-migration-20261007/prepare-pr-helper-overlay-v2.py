"""Before payload generation, carry the actual post-FINAL adapter repair into the PR."""
from common_v2 import *
passed('record-acceptance-v2-01');assert load(RUN/'native-acceptance-overlay-v1.json')['status']=='passed'
src=(RUN/'prepare-pr-payload-v1.py').read_text(encoding='utf-8')
old='A task-local -text rule preserves raw evidence.'
new='The actual acceptance-adapter v1 failure also remains: historical CONTRACT/BODY R1-R7 reader obligations were incorrectly required to be empty. Version2 explicitly hash-binds the unchanged original requirements to the actual FINAL satisfied verdicts before native acceptance; no original receipt/report or mathematical byte is rewritten. See acceptance-adapter-repair-v2.json and acceptance-reader-discharge-v2.json. A task-local -text rule preserves raw evidence.'
assert src.count(old)==1;src=src.replace(old,new)
write(RUN/'prepare-pr-payload-v2.py',src);compile(src,str(RUN/'prepare-pr-payload-v2.py'),'exec');generated('pr-helper-overlay-before-use-v2.json',[RUN/'prepare-pr-payload-v2.py'])
print('Current accepted evidence and actual adapter repair included before payload generation.')
