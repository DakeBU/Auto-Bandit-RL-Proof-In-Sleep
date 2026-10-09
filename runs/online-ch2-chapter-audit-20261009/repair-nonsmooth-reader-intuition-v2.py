from lower_common_v1 import *

reviewed(); headers(3)
old=RUN/'nonsmooth-reader-proposal-v1.json'
p=load(old)
assert p['notes'][0]['full_name']=='BanditRL.OnlineConvex.shifted_absolute_convex_differentiable_iff'
before=p['notes'][0]['intuition']
assert before=='The kink concerns the ambient function at a margin point; zero effective normal removes the kink.'
p['notes'][0]['intuition']='For every real center c, the translated absolute value has a genuine kink at c and is differentiable on both open sides.'
write(RUN/'nonsmooth-reader-proposal-v2.json',p)
s=load(CONTRACT/'nonsmooth-future-publication-scope-v1.json')
s['reader_proposal_sha256']=sha(RUN/'nonsmooth-reader-proposal-v2.json')
write(CONTRACT/'nonsmooth-future-publication-scope-v2.json',s)
write(RUN/'nonsmooth-reader-intuition-repair-delta-v2.json',dict(
    original_proposal_sha256=sha(old),repaired_proposal_sha256=sha(RUN/'nonsmooth-reader-proposal-v2.json'),
    exact_AST_changed_path='notes[0].intuition',old_value=before,new_value=p['notes'][0]['intuition'],
    reason='Distinct reviewer identified an incorrect hinge-only zero-normal intuition on the shifted-absolute note. The shifted absolute has a true kink at every center, with no normal parameter.',
    production_or_canary_types_or_BODIES_changed=False,canonical_readers_roots_changed=False,
    original_scope_sha256=sha(CONTRACT/'nonsmooth-future-publication-scope-v1.json'),
    repaired_scope_sha256=sha(CONTRACT/'nonsmooth-future-publication-scope-v2.json'),
    repair_review_pending=True,chapter_complete=False,whole_Goal_status='ACTIVE'))
check=load(old);check['notes'][0]['intuition']=p['notes'][0]['intuition'];assert check==p
check=load(CONTRACT/'nonsmooth-future-publication-scope-v1.json');check['reader_proposal_sha256']=s['reader_proposal_sha256'];assert check==s
reviewed();headers(3)
print('Only one reader intuition corrected in separate v2; original review inputs and all mathematical bodies/types immutable.')
