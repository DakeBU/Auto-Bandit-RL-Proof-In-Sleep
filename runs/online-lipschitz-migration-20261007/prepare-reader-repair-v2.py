"""Repair ordinary-comment prose only after actual lexical guard rejected before writes."""
from common_v2 import *
f=fixed();assert load(RUN/'integrate-reader-v1-01-exit.json')['exit_code']!=0
assert not (RUN/'public-comment-qualification-v1.json').exists()
snap={r['path']:r for r in load(RUN/'historical-raw-supersession-v1.json')['rows']}
for p in ['website/content/readings.json','website/content/highlights.json','website/content/chapters.json']:assert sha(p)==snap[p]['raw_sha256']
p=RUN/'integrate-reader-v1.py';t=p.read_text(encoding='utf-8');assert t.count('+1at2/-1at-2')==1
t=t.replace('+1at2/-1at-2','+1 at2 and -1 at-2');write(RUN/'integrate-reader-v2.py',t);compile(t,str(RUN/'integrate-reader-v2.py'),'exec');generated('reader-repair-before-use-v2.json',[RUN/'integrate-reader-v2.py'])
write(RUN/'reader-repair-v2.json',dict(status='repair-prepared-fresh-integration-required',actual_failed_attempt='integrate-reader-v1-01',cause='Positive/negative scalar-support prose contained /- and triggered ordinary-comment lexical guard BEFORE any public/reader write.',resolution='Describe the two slopes using and, with guard unchanged; original unused/failed helper/log and reviewed source kept, version2 retryrequired.',mathematical_repairs=[],public_original_canary_headers_shared_unchanged=True,reader_JSON_unchanged_at_failure=True,combined_gate_not_started=True,chapter_complete=False,goal_complete=False))
event('repair',dict(failure='ordinary leading-comment lexical delimiter in slope prose beforewrite',resolution='newversion ordinary prose, exact mathematical suffix/header/canary fixed',frozen_headers=f['headers'],mathematical_repairs=[],source_package_accepted=False),'reader-comment-v2')
print('Version2 prose-only repair prepared; no mathematical source or reader data was written on failedattempt.')
