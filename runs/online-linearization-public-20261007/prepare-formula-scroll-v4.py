from common_v2 import *
s=(RUN/'capture-reader-v3.py').read_text(encoding='utf-8').replace('capture-reader-v3.cjs','capture-formula-scroll-v4.cjs').replace('formula-render-v3','formula-scroll-v4').replace('online-linearization-public-playwright-v3-profile','online-linearization-public-scroll-v4-profile')
s=s[:s.index('assert sha(page)==before')]+"""assert sha(page)==before
r=load(RUN/'formula-scroll-v4-browser.json');assert r['after']['left']>0 and r['after']['MathJaxErrors']==0
files=['proof-bridge-step4-left-v4.png','proof-bridge-step4-right-v4.png']
write(RUN/'formula-scroll-v4.json',dict(status='actual-left-right-horizontal-scroll-awaiting-pixel-review',actual_command=command,generated_page_sha256=before,site_source_commit=load(RUN/'registry-v1.json')['source_commit'],browser_report_sha256=sha(RUN/'formula-scroll-v4-browser.json'),images=[dict(path=(RUN/f).as_posix(),sha256=sha(RUN/f)) for f in files],actual_scroll_only=True,no_source_DOM_CSS_or_generated_file_edit=True,profile_preserved=profile.as_posix(),task_owned_server_stopped=True))
print('Actual left/right formula scroll captured; both pixel views pending, site/DOM/CSS unchanged.')
"""
write(RUN/'capture-formula-scroll-v4.py',s)
