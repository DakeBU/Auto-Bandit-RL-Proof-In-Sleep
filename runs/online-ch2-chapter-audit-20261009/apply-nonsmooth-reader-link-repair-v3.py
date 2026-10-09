from common_nonsmooth_publication_v2 import *
fixed()
p=RUN/'nonsmooth-reader-link-repair-review-v3.json'
assert sha(p)=='9201b6d99f6fb771ca68cb07c317425158b0b97837001248ddcfa622164e32b1'
r=load(p);assert r['verdict']==r['materialization_verdict']=='accepted' and not r['required_repairs']
for row in r['raw_input_checks']:assert sha(row['path'])==row['before_sha256']==row['after_sha256']
a=r['approved_exact_materialization'];assert sha(a['mutable_path'])==a['before_sha256']
assert sha(a['after_snapshot'])==a['after_sha256']
Path(a['mutable_path']).write_bytes(Path(a['after_snapshot']).read_bytes())
import common_nonsmooth_publication_v3 as current
current.fixed()
write(RUN/'nonsmooth-reader-link-repair-applied-v3.json',dict(actual_review_sha256=sha(p),
    exact_materialization=a,complete_compiled_graph_unchanged=True,proof_source_canary_roots_unchanged=True,
    site_and_FINAL_pending=True,chapter_complete=False,whole_Goal_status='ACTIVE'))
for name in ['verify-nonsmooth-registry-v1.py','capture-nonsmooth-reader-v1.py']:
    old=(RUN/name).read_text('utf8')
    assert old.count('from common_nonsmooth_publication_v2 import *')==1
    write(RUN/name.replace('-v1.py','-v2.py'),old.replace('from common_nonsmooth_publication_v2 import *','from common_nonsmooth_publication_v3 import *'))
print('Approved exact one-link replacement applied; unchanged compiled evidence/proofs; new guarded site2 helpers created.')
