"""Repair actual browser capture geometry, preserve original clipped-header images."""
from common_v1 import *
fixed(True)
write(RUN/'capture-repair-v2.json',dict(original='formula-render-v1 images',finding='ROOT actual pixel inspection: page sticky On This Page bar occludes source-card heading in tall element screenshots. Math/body and DOM horizontal geometry pass; original captures do not establish unobscured full cards.',repair='Use actual larger browser viewport for each whole tall card, scroll card below fixed navigation and screenshot only after whole card lies within viewport. No DOM/CSS/source/proof edits.',mathematical_type_body_or_reader_change=False,site_source_commit=load(RUN/'registry-v1.json')['source_commit'],original_images_preserved=True))
native('capture-repair-event-v2','lifecycle-event','--session',TASK,'--event','repair','--payload-json',json.dumps(dict(run_id=RUN.name,contract_version=1,reason='Actual pixel source-card heading occluded by sticky navigation',repair='Versioned actual viewport/scroll capture only, original v1 retained',statement_and_body_unchanged=True,chapter_complete=False,goal_complete=False)))
text=(RUN/'render-source-card-v1.cjs').read_text(encoding='utf-8')
needle="   const g=await card.evaluate(el=>"
assert needle in text
insert="   const cardHeight=await card.evaluate(el=>Math.ceil(el.getBoundingClientRect().height)); await page.setViewportSize({width:1440,height:Math.max(1800,cardHeight+350)}); await page.evaluate(el=>window.scrollTo(0,window.scrollY+el.getBoundingClientRect().top-180),await card.elementHandle()); await page.waitForTimeout(100); const captureBox=await card.boundingBox(); if(!captureBox||captureBox.y<140||captureBox.y+captureBox.height>Math.max(1800,cardHeight+350)-30)throw Error('Whole card not safely below sticky navigation in actual viewport: '+JSON.stringify(captureBox));\n"
text=text.replace(needle,insert+needle).replace("+'-v1.png'","+'-v2.png'").replace('formula-render-v1-dom.html','formula-render-v2-dom.html').replace('formula-render-v1-browser.json','formula-render-v2-browser.json')
assert "+'-v1.png'" not in text
write(RUN/'render-source-card-v2.cjs',text)
py=(RUN/'render-source-card-v1.py').read_text(encoding='utf-8').replace('render-source-card-v1.cjs','render-source-card-v2.cjs').replace('formula-render-v1','formula-render-v2').replace('source-card-%02d-v1.png','source-card-%02d-v2.png').replace('playwright-v1-profile','playwright-v2-profile')
write(RUN/'render-source-card-v2.py',py)
gate('formula-render-v2-01',sys.executable,'-B','-X','utf8',RUN/'render-source-card-v2.py')
native('capture-repair-resume-v2','lifecycle-event','--session',TASK,'--event','proving','--payload-json',json.dumps(dict(run_id=RUN.name,contract_version=1,capture='v2 actual larger viewport safely below sticky navigation',statement_and_body_unchanged=True,chapter_complete=False,goal_complete=False)))
native('capture-repaired-candidate-v2','lifecycle-event','--session',TASK,'--event','candidate','--payload-json',json.dumps(dict(run_id=RUN.name,contract_version=1,capture_v2=RUN.joinpath('formula-render-v2.json').as_posix(),ROOT_and_distinct_FINAL_pixel_reviews='pending',statement_and_body_unchanged=True,chapter_complete=False,goal_complete=False)))
fixed(True);print('Capture v2 renders six unobscured fullcards by actual viewport/scroll only; pixel review pending, original v1 retained.')
