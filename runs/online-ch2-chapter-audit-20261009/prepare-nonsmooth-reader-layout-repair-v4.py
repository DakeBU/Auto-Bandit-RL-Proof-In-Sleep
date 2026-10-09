from common_nonsmooth_publication_v3 import *
import copy,base64

fixed()
receipt=load(RUN/'nonsmooth-site-check-v2.json')
message=base64.b64decode(receipt['stdout_base64']).decode('utf8')
assert receipt['actual_exit']==1 and 'online-subgradient-differentiability needs one to six explicit featured teaching notes' in message
old=load(RUN/'nonsmooth-reader-proposal-v3.json');new=copy.deepcopy(old)
assert all(n['featured'] is False for n in new['notes'])
for n in new['notes']:n['featured']=True
assert new['card']['local_status']['label']=='Exact example bodies compiled; package integration pending'
new['card']['local_status']['label']='Exact example bodies compiled; Chapter2 incomplete'
write(RUN/'nonsmooth-reader-proposal-v4.json',new)
high=ROOT/'website/content/highlights.json';hr=load(high)
for note in new['notes']:
    i=next(i for i,n in enumerate(hr['highlights']) if n['full_name']==note['full_name'])
    assert hr['highlights'][i]==next(n for n in old['notes'] if n['full_name']==note['full_name'])
    hr['highlights'][i]=note
hs=RUN/'nonsmooth-highlights-layout-repair-v4.json';write(hs,hr)
read=ROOT/'website/content/readings.json';rr=load(read)
route=next(r for r in rr['readings'] if r['slug']==old['route'])
assert route['source_theorems'][-1]==old['card'];route['source_theorems'][-1]=new['card']
rs=RUN/'nonsmooth-readings-status-repair-v4.json';write(rs,rr)
plan=dict(before_proposal_sha256=sha(RUN/'nonsmooth-reader-proposal-v3.json'),after_proposal_sha256=sha(RUN/'nonsmooth-reader-proposal-v4.json'),
    exact_scalar_changes=['Three new notes: featured false -> true','New source card only: label -> Exact example bodies compiled; Chapter2 incomplete'],
    rows=[dict(path=p.as_posix(),before_sha256=sha(p),after_snapshot=s.as_posix(),after_sha256=sha(s)) for p,s in [(high,hs),(read,rs)]],
    old_notes_cards_source_proofs_formulas_links_unchanged=True,
    true_featured_count_after=3,site_policy_unchanged=True,mathematical_repair=False,
    next_site=(ROOT/'tmp/online-ch2-nonsmooth-site-v3').as_posix(),
    chapter_complete=False,whole_Goal_status='ACTIVE')
write(CONTRACT/'nonsmooth-reader-layout-repair-plan-v4.json',plan)
write(RUN/'nonsmooth-site-check-failure-classification-v2.json',dict(actual_receipt_sha256=sha(RUN/'nonsmooth-site-check-v2.json'),
    actual_exit=1,actual_message=message,
    classification='existing-reader-featured-threshold-crossed-six-to-nine',
    repair='Keep all six old notes and all three new notes; feature the three new notes so the route has3 explicit primary teaching notes. Also replace the new source card transient pending label with a durable compiled/Chapter2-incomplete label.',
    full_Lean_gate_still_applicable=True,no_generated_site_or_checker_edit=True,
    independently_review_pending=True,chapter_complete=False,whole_Goal_status='ACTIVE'))
paths=[PUBLIC,CANARY,ROOT/'BanditRLProof.lean',ROOT/'Tests.lean',high,read,ROOT/'website/content/chapters.json',
    ROOT/'website/scripts/check_site.py',ROOT/'website/scripts/build_site.py',
    CONTRACT/'nonsmooth-reader-layout-repair-plan-v4.json',RUN/'nonsmooth-reader-proposal-v3.json',RUN/'nonsmooth-reader-proposal-v4.json',hs,rs,
    RUN/'nonsmooth-reader-link-repair-review-v3.json',RUN/'nonsmooth-reader-repair-review-v2.json',
    RUN/'nonsmooth-production-BODY-review-v1.json',RUN/'nonsmooth-canary-publication-review-v1.json',
    RUN/'nonsmooth-full-harness-inspected-v1.json',RUN/'nonsmooth-site-build-v2.json',RUN/'nonsmooth-site-check-v2.json',RUN/'nonsmooth-site-check-failure-classification-v2.json']
write(RUN/'nonsmooth-reader-layout-repair-review-input-v4.json',dict(files=rows(paths),scope=plan,
    requested_actor='/root/source_reviewer',requested_effort='medium',runtime_attested=False,FINAL_pending=True))
fixed()
print('Four exact new-reader scalar changes proposed; all canonical bytes unchanged pending distinct review.')
