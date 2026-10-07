"""Repair actual source-card assumption omissions found in root's current pixels."""
from common_v2 import *
fixed(True);passed('source-site-gates-v2-01')
write(RUN/'initial-reader-pixel-repair-v1.json',dict(status='repair needed after actual root viewing',actor='/root',images=[dict(path=(RUN/f'source-card-{i:02}-v1.png').as_posix(),sha256=sha(RUN/f'source-card-{i:02}-v1.png')) for i in range(1,7)],first_viewport_sha256=sha('tmp/online-osd-public-reader-v1.png'),finding='Standalone single-step regret field misleadingly mentions trajectory sum; tuned assumptions omit explicit feasible initial point and proper/subdifferentiable played losses. Coarse card should explicitly repeat fixed hypotheses. Actual formulas render correctly; no TeX change, overflow or mathematical header defect.',source_FINAL_separate_repair_review_required=True))
p=Path('website/content/readings.json');write(RUN/'snapshots/before-reader-contract-repair-v2.txt',p.read_bytes());d=load(p);x=next(a for a in d['readings'] if a['slug']==ROUTE)
old=[a['math'] for a in x['source_theorems']]
x['source_theorems'][0]['contract']['regret']='Finite real single-step loss gap f(x)-f(u), justified by properness and actual global supports. This standalone lemma assumes no online regret sum or algorithm trajectory.'
x['source_theorems'][4]['contract']['assumptions']='T>=1,D>0,G>0; prescribed feasible x1 in V; every played loss proper and subdifferentiable on V; all feasible pair distances<=D; actual chosen supports on this very eta-dependent trajectory have norms<=G.'
x['source_theorems'][5]['contract']['assumptions']='eta>0; feasible prescribed x1 and comparator u; each played loss proper and subdifferentiable on V. T0 is admitted and no bounded-domain premise is added.'
assert old==[a['math'] for a in x['source_theorems']]
before=load(RUN/'snapshots/before-reader-contract-repair-v2.txt');assert [a for a in before['readings'] if a['slug']!=ROUTE]==[a for a in d['readings'] if a['slug']!=ROUTE]
p.write_bytes((json.dumps(d,ensure_ascii=False,indent=2)+'\n').encode())
write(RUN/'reader-contract-repair-v2.json',dict(M5=dict(finding='Current reader single-step field conflated loss gap with online sum; tuned card omitted explicit initial feasibility/played regularity, coarse card used only a cross-reference.',repair='Three exact contract fields corrected to the unchanged accepted actual public hypotheses; all formulas, links and other reader routes unchanged.',source_and_public_mathematical_contracts_unchanged=True,separate_source_FINAL_repair_verdict_required=True),original_pixels_site1_logs_and_reader_snapshot_preserved=True,current_full_harness3_and_site2_pending=True))
for src,dst in [('browser-v1.py','browser-v2.py'),('render-source-card-v1.py','render-source-card-v2.py'),('render-source-card-v1.cjs','render-source-card-v2.cjs'),('verify-registry-v1.py','verify-registry-v2.py')]:
 text=(RUN/src).read_text(encoding='utf-8').replace('-v1','-v2');write(RUN/dst,text)
text=(RUN/'source-site-gates-v2.py').read_text(encoding='utf-8').replace("passed('full-harness-v2-01')","passed('full-harness-v3-01')")
for s in ['contributor-exact-v2-01','scoped-diff-v2-01','source-scope-v2-01']:text=text.replace(s,s.replace('v2','v3'))
text=text.replace("RUN/'check-scoped-diff-v1.py','v2'","RUN/'check-scoped-diff-v1.py','v3'")
for s in ['online-osd-public-site-v1','site-build-v1-01','site-check-v1-01','registry-v1-01','verify-registry-v1.py','browser-v1-01','browser-v1.py','formula-render-v1-01','render-source-card-v1.py']:text=text.replace(s,s.replace('v1','v2'))
text=text.replace("q=subprocess.run(","q=subprocess.run(").replace('main-relative-diagnostic-v1','main-relative-diagnostic-v2')
write(RUN/'source-site-gates-v3.py',text)
text=(RUN/'task-shadow-v2.py').read_text(encoding='utf-8').replace("passed('project-gates-v1-01')","passed('project-gates-v1-01');passed('full-harness-v3-01')")
for s in ['candidate-scoped-trials-v2','memory-digest-candidate-v2','candidate-frontier-refresh-v2','candidate-frontier-shadow-v2','candidate-frontier-v2']:text=text.replace(s,s.replace('v2','v3'))
write(RUN/'task-shadow-v3.py',text)
text=(RUN/'prepare-final-evidence-v4.py').read_text(encoding='utf-8')
for s in ['contributor-exact-v2-01','scoped-diff-v2-01','source-scope-v2-01','source-site-gates-v2-01','full-harness-v2-01','task-shadow-v2-01','candidate-frontier-refresh-v2','candidate-frontier-shadow-v2']:text=text.replace(s,s.replace('v2','v3'))
for s in ['site-build-v1-01','site-check-v1-01','registry-v1-01','browser-v1-01','formula-render-v1-01','registry-v1.json','formula-render-v1.json','browser-v1-binding.json','source-card-01 through06-v1.png','main-relative-diagnostic-v1.json']:text=text.replace(s,s.replace('v1','v2'))
text=text.replace("'Exact-base contributor schema rejected", "'Reader M5: three contract fields corrected to unchanged public hypotheses after actual first pixel review; original site1/pixels/snapshot retained, current harness3/site2 and separate FINAL M5 required.','Exact-base contributor schema rejected")
text=text.replace('All R1-R8 separately required;','All R1-R8 and separate reader repair M5 verdict required;')
write(RUN/'prepare-final-evidence-v5.py',text)
text=(RUN/'record-acceptance-v2.py').read_text(encoding='utf-8').replace("passed('task-shadow-v2-01')","passed('task-shadow-v3-01')")
text=text.replace("con=load(RUN/'source-contract-receipt-v2.json')","assert final['repair_verdict']['M5']['verdict']=='satisfied'\ncon=load(RUN/'source-contract-receipt-v2.json')");write(RUN/'record-acceptance-v3.py',text)
text=(RUN/'prepare-pr-payload-v4.py').read_text(encoding='utf-8').replace('registry-v1.json','registry-v2.json').replace('current full harness2 and contributor2 pass','current full harness3 and contributor3 pass').replace('All R1-R8 discharged','Root pixel review found and repaired three reader contract fields (single-step loss gap, tuned initial feasibility/played regularity and explicit coarse hypotheses); original site/pixels/snapshot retained, source formulas/headers unchanged, separate FINAL M5 satisfied. Current reader full harness3/site2 and all R1-R8 discharged');write(RUN/'prepare-pr-payload-v5.py',text)
text=(RUN/'complete-delivery-gates-v5.py').read_text(encoding='utf-8').replace("passed('record-acceptance-v2-01')","passed('record-acceptance-v3-01')").replace("passed('prepare-pr-payload-v4-01')","passed('prepare-pr-payload-v5-01')");write(RUN/'complete-delivery-gates-v6.py',text)
text=(RUN/'prepare-delivery-v1.py').read_text(encoding='utf-8').replace('registry-v1.json','registry-v2.json').replace('formula-render-v1.json','formula-render-v2.json');write(RUN/'prepare-delivery-v2.py',text)
event('repair',dict(kind='source-reader contract fields only',repair=(RUN/'reader-contract-repair-v2.json').as_posix(),public_and_canary_unchanged=True),attempt='reader-v2')
fixed(True);print('Three actual reader contract fields repaired, formulas/public targets unchanged; original pixels preserved, latest harness3/site2 and separate FINAL M5 pending.')
