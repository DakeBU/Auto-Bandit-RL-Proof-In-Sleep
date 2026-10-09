from common_nonsmooth_publication_v3 import *
fixed()
p=RUN/'nonsmooth-reader-layout-repair-review-v4.json'
assert sha(p)=='2d4cd8b0447e9cf095c5e96f593cdf474afd901d66e9575bacf35b1c66d153dc'
r=load(p);assert r['verdict']==r['materialization_verdict']=='accepted' and not r['required_repairs']
for row in r['raw_input_checks']:assert sha(row['path'])==row['before_sha256']==row['after_sha256']
for a in r['approved_exact_materialization']:
    assert sha(a['path'])==a['before_sha256'] and sha(a['after_snapshot'])==a['after_sha256']
    Path(a['path']).write_bytes(Path(a['after_snapshot']).read_bytes())
import common_nonsmooth_publication_v4 as current
current.fixed()
write(RUN/'nonsmooth-reader-layout-repair-applied-v4.json',dict(actual_review_sha256=sha(p),
    exact_materialization=r['approved_exact_materialization'],proof_source_canary_roots_unchanged=True,
    old_six_notes_preserved=True,three_new_notes_featured=True,chapter_complete=False,whole_Goal_status='ACTIVE'))
for oldname,newname in [('verify-nonsmooth-registry-v2.py','verify-nonsmooth-registry-v3.py'),('capture-nonsmooth-reader-v2.py','capture-nonsmooth-reader-v3.py')]:
    old=(RUN/oldname).read_text('utf8');assert old.count('from common_nonsmooth_publication_v3 import *')==1
    write(RUN/newname,old.replace('from common_nonsmooth_publication_v3 import *','from common_nonsmooth_publication_v4 import *'))
old=(RUN/'checkpoint-nonsmooth-site-v4.py').read_text('utf8')
for a,b in [('common_nonsmooth_publication_v3','common_nonsmooth_publication_v4'),('nonsmooth-link-repair','nonsmooth-layout-repair'),
    ('nonsmooth-contributor-stack-v4','nonsmooth-contributor-stack-v5'),('nonsmooth-contributor-main-v4','nonsmooth-contributor-main-v5'),
    ('nonsmooth-site-build-v2','nonsmooth-site-build-v3'),('nonsmooth-site-check-v2','nonsmooth-site-check-v3'),
    ('nonsmooth-clean-candidate-binding-v2','nonsmooth-clean-candidate-binding-v3'),
    ('verify-nonsmooth-registry-v2.py','verify-nonsmooth-registry-v3.py'),
    ('Use public registry parents in nonsmooth teaching links','Feature nonsmooth teaching notes and clarify chapter boundary')]:
    assert a in old,a;old=old.replace(a,b)
write(RUN/'checkpoint-nonsmooth-site-v5.py',old)
print('Approved exact four-scalar metadata repair applied; fresh site3 helpers created, all previous failure evidence retained.')
