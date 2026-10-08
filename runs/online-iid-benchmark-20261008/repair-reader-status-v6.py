from common_integrated_v2 import *
fixed_integrated()
assert load(RUN/'current-reader-capture-v4-exit.json')['exit_code']==1
diagnostic=load(RUN/'overflow-diagnostic-v5.json')
badge=next(x for x in diagnostic['statusLayout'] if x['cls']=='status compiled')
assert badge['whiteSpace']=='nowrap' and badge['width']>750
write(RUN/'reader-before-status-layout-v4.json.raw',Path('website/content/readings.json').read_bytes())
data=load('website/content/readings.json')
card=next(x for x in data['readings'] if x['slug']==ROUTE)['source_theorems'][-1]
old=dict(card['local_status'])
assert card['local_status']['label']=='Eight derived expected-fixed/causal IID bodies locally compiled and BODY reviewed; package gates pending'
card['local_status']['label']='8 derived IID proofs compiled; gates pending'
assert {k:v for k,v in old.items() if k!='label'}=={k:v for k,v in card['local_status'].items() if k!='label'}
Path('website/content/readings.json').write_bytes((json.dumps(data,ensure_ascii=False,indent=2)+'\n').encode('utf8'))
write(RUN/'reader-status-layout-repair-v6.json',dict(actual_second_failed_browser_exit=1,geometry_sha256=sha(RUN/'overflow-diagnostic-v5.json'),
    actual_badge_width=badge['width'],actual_badge_whiteSpace=badge['whiteSpace'],
    prior_v4_diagnosis='Anchor-only hypothesis was incomplete: shorter page link did not fix the actual759.59px nowrap status pill. Prior inference/failure retained without rewriting.',
    repair='Shorten ONLY newest local-status label; full source intent/model/conclusion/formulas/hypotheses/remaining boundaries unchanged in adjacent fields.',
    new_label=card['local_status']['label'],old_source_cards_notes_links_unchanged=True,public_sha256=sha(PUBLIC),canary_sha256=sha(CANARY),
    Lean_inputs_unchanged=True,old_failed_sites_v2_v4_preserved=True,generated_site_not_edited=True,
    package_accepted=False,chapter_complete=False,goal_complete=False))
for name in ['verify-registry','capture-reader']:
    for suffix in (['.py','.cjs'] if name=='capture-reader' else ['.py']):
        text=(RUN/(name+'-v4'+suffix)).read_text(encoding='utf8')
        text=text.replace('-site-v4','-site-v6').replace('registry-v4','registry-v6').replace('capture-reader-v4','capture-reader-v6')
        text=text.replace('formula-render-v4','formula-render-v6').replace('-viewport-v4','-viewport-v6')
        text=text.replace('source-card-v4','source-card-v6').replace('note-${i+1}-v4','note-${i+1}-v6').replace('declaration-${i+1}-v4','declaration-${i+1}-v6')
        write(RUN/(name+'-v6'+suffix),text)
text=(RUN/'build-clean-site-v4.py').read_text(encoding='utf8')
text=text.replace('-site-v4','-site-v6').replace('site-build-v4','site-build-v6').replace('site-check-v4','site-check-v6')
text=text.replace('registry-check-v4','registry-check-v6').replace('verify-registry-v4','verify-registry-v6').replace('current-reader-capture-v4','current-reader-capture-v6').replace('capture-reader-v4','capture-reader-v6')
text=text.replace('public/canary/imports/readers unchanged since source commit.',
    'public/canary/imports/Lean source hashes unchanged; only two newest reader presentation labels repaired after the gate, exact equations/semantics unchanged.')
write(RUN/'build-clean-site-v6.py',text)
fixed_integrated()
print('Actual nowrap759.59px badge repaired; complete source meaning and math inputs preserved.')
