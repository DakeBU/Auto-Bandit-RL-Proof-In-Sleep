from common_nonsmooth_publication_v4 import *
import copy
fixed()
diag=load(RUN/'nonsmooth-browser-diagnostic-v2.json')
d=diag['diagnostics'];assert d['sourceCards']==2 and d['sourceMathContainers']==d['sourceMathTex']==8
assert d['mathErrors']==0 and diag['errors']==diag['failed']==[]
assert d['sourceMathDetails'][-1]['parentClientWidth']==1606
assert d['sourceMathDetails'][-1]['renderedWidth']>1440
old=load(RUN/'nonsmooth-reader-proposal-v4.json');new=copy.deepcopy(old)
parts=old['card']['math'].split(r'.\qquad ');assert len(parts)==3
new['card']['math']=r'\begin{aligned} &'+parts[0]+r'.\\ &'+parts[1]+r'.\\ &'+parts[2]+r'\end{aligned}'
write(RUN/'nonsmooth-reader-proposal-v5.json',new)
p=ROOT/'website/content/readings.json';rr=load(p)
route=next(r for r in rr['readings'] if r['slug']==old['route']);assert route['source_theorems'][-1]==old['card']
route['source_theorems'][-1]=new['card']
snapshot=RUN/'nonsmooth-readings-formula-lines-v5.json';write(snapshot,rr)
plan=dict(before_proposal_sha256=sha(RUN/'nonsmooth-reader-proposal-v4.json'),after_proposal_sha256=sha(RUN/'nonsmooth-reader-proposal-v5.json'),
    exact_change='Only new source card math display: replace the two between-formula qquad separators with aligned row breaks; retain all three formulas and punctuation in order.',
    rows=[dict(path=p.as_posix(),before_sha256=sha(p),after_snapshot=snapshot.as_posix(),after_sha256=sha(snapshot))],
    no_mathematical_or_other_scalar_change=True,renderer_or_site_policy_unchanged=True,
    actual_source_cards=2,actual_source_formulas=8,old_proof_bridge_formulas=6,
    next_site=(ROOT/'tmp/online-ch2-nonsmooth-site-v4').as_posix(),chapter_complete=False,whole_Goal_status='ACTIVE')
write(CONTRACT/'nonsmooth-formula-linebreak-plan-v5.json',plan)
write(RUN/'nonsmooth-browser-diagnosis-classification-v2.json',dict(
    initial_timeout_receipt_sha256=sha(RUN/'nonsmooth-browser-node-v1.json'),
    actual_diagnostic_command_receipt_sha256=sha(RUN/'nonsmooth-browser-diagnostic-command-v2.json'),
    actual_diagnostics_sha256=sha(RUN/'nonsmooth-browser-diagnostic-v2.json'),
    count_repair='Capture expects8 total source-guide formulas, consisting of6 preexisting proof-bridge formulas plus2 source cards. Not2; exact observed DOM count, no renderer-error waiver.',
    actual_source_formula_parent_width=1606,actual_desktop_viewport_width=1440,
    layout_repair='One new source card combines three formulas on one line and expands the source grid; propose semantic-preserving3-row aligned display. Do not waive horizontal geometry checks.',
    canonical_reader_still_unchanged_pending_review=True,mathematical_repair=False,
    chapter_complete=False,whole_Goal_status='ACTIVE'))
paths=[PUBLIC,CANARY,ROOT/'BanditRLProof.lean',ROOT/'Tests.lean',p,ROOT/'website/content/highlights.json',ROOT/'website/content/chapters.json',
    RUN/'common_nonsmooth_publication_v4.py',CONTRACT/'nonsmooth-formula-linebreak-plan-v5.json',
    RUN/'nonsmooth-reader-proposal-v4.json',RUN/'nonsmooth-reader-proposal-v5.json',snapshot,
    RUN/'nonsmooth-reader-layout-repair-review-v4.json',RUN/'nonsmooth-reader-link-repair-review-v3.json',
    RUN/'nonsmooth-production-BODY-review-v1.json',RUN/'nonsmooth-canary-publication-review-v1.json',
    RUN/'nonsmooth-full-harness-inspected-v1.json',RUN/'nonsmooth-site-check-v3.json',RUN/'nonsmooth-registry-inspected-v1.json',
    RUN/'nonsmooth-browser-node-v1.json',RUN/'nonsmooth-browser-diagnostic-v2.json',RUN/'nonsmooth-browser-diagnosis-classification-v2.json']
write(RUN/'nonsmooth-formula-linebreak-review-input-v5.json',dict(files=rows(paths),scope=plan,
    requested_actor='/root/source_reviewer',requested_effort='medium',runtime_attested=False,FINAL_pending=True))
fixed()
print('Actual8-formula diagnosis and one-field3-line display repair proposed; canonical source and all mathematical formulas unchanged pending review.')
