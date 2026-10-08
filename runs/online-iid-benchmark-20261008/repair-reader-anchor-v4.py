from common_integrated_v2 import *
fixed_integrated()
assert load(RUN/'current-reader-capture-v2-exit.json')['exit_code']==1
write(RUN/'reader-before-anchor-layout-v2.json.raw',Path('website/content/readings.json').read_bytes())
data=load('website/content/readings.json')
row=next(x for x in data['readings'] if x['slug']==ROUTE)
assert len(row['source_theorems'])==12
card=row['source_theorems'][-1]
old=dict(card)
assert card['pages']=='printed pp.1–2 / PDF pp.13–14: guessing-game IID square loss, equations(1.1)/(1.2), fixed comparator outside expectation'
card['pages']='printed pp.1–2 / PDF pp.13–14'
assert {k:v for k,v in old.items() if k!='pages'}=={k:v for k,v in card.items() if k!='pages'}
Path('website/content/readings.json').write_bytes((json.dumps(data,ensure_ascii=False,indent=2)+'\n').encode('utf8'))
write(RUN/'reader-anchor-layout-repair-v4.json',dict(actual_failed_browser_exit=1,
    geometry_sha256=sha(RUN/'overflow-diagnostic-v3.json'),actual_failed_pixels_sha256=sha(RUN/'overflow-diagnostic-v3.png'),
    ROOT_individually_viewed_actual_failed_image=True,
    obstruction='Long nonwrapping source-page link pushed the entire source card beyond the viewport; actual card width1225.25 while viewport1440 also has sidebar/margins.',
    repair='Shorten ONLY latest source-card pages text to exact printed/PDF page span. Full source intent/equations/comparator placement remain in unchanged relationship/model/assumptions/guarantee/formula fields.',
    new_pages=card['pages'],changed_reader_fields=1,all_old_cards_links_notes_preserved=True,math_formula_unchanged=True,
    public_sha256=sha(PUBLIC),canary_sha256=sha(CANARY),Lean_bodies_imports_targets_context_unchanged=True,
    applicable_Lean='Existing actual current combined-root-v2/Tests/fullharness gate; reader-anchor-only repair creates no Lean input change.',
    old_failed_site_retained=True,generated_site_not_edited=True,package_accepted=False,chapter_complete=False,goal_complete=False))
for name in ['verify-registry','capture-reader']:
    suffixes=['.py','.cjs'] if name=='capture-reader' else ['.py']
    for suffix in suffixes:
        text=(RUN/(name+'-v2'+suffix)).read_text(encoding='utf8')
        text=text.replace('-site-v2','-site-v4').replace('registry-v2','registry-v4').replace('capture-reader-v2','capture-reader-v4')
        text=text.replace('formula-render-v2','formula-render-v4').replace('-viewport-v2','-viewport-v4')
        text=text.replace('source-card-v2','source-card-v4').replace('note-${i+1}-v2','note-${i+1}-v4').replace('declaration-${i+1}-v2','declaration-${i+1}-v4')
        write(RUN/(name+'-v4'+suffix),text)
text=(RUN/'build-clean-site-v2.py').read_text(encoding='utf8')
text=text.replace('-site-v2','-site-v4').replace('site-build-v2','site-build-v4').replace('site-check-v2','site-check-v4')
text=text.replace('registry-check-v2','registry-check-v4').replace('verify-registry-v2','verify-registry-v4').replace('current-reader-capture-v2','current-reader-capture-v4').replace('capture-reader-v2','capture-reader-v4')
write(RUN/'build-clean-site-v4.py',text)
fixed_integrated()
print('One source-page label repaired; source formulas/types/bodies/old cards unchanged. Clean rebuilt site/current pixels required.')
