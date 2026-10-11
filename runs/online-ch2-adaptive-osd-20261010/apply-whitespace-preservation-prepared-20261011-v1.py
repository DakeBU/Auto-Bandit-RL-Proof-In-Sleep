from common import *
import argparse, subprocess
ap=argparse.ArgumentParser();ap.add_argument('--review',required=True);args=ap.parse_args()
planpath=RUN/'whitespace-preservation-proposal-20261011-v2.json';plan=load(planpath);review=load(args.review)
assert review['verdict']=='accepted' and review['blocking_repairs']==[]
assert review['approved_plan_raw_sha256']==sha(planpath)
assert review['approved_helper_raw_sha256']==sha(Path(__file__))
assert review['ordinary_archival_waiver_approved'] is True
for item in plan['files']: assert sha(ROOT/item['path'])==item['sha256'],item['path']
for item in plan['attribute_changes']:
    assert sha(ROOT/item['path'])==item['before_sha256']
    assert sha(ROOT/item['after_snapshot'])==item['after_sha256']
    assert (ROOT/item['after_snapshot']).read_bytes().startswith((ROOT/item['path']).read_bytes())
write(RUN/'whitespace-preservation-apply-started-20261011-v1.json',dict(plan_sha256=sha(planpath),review_path=args.review,review_sha256=sha(args.review)))
for item in plan['attribute_changes']: (ROOT/item['path']).write_bytes((ROOT/item['after_snapshot']).read_bytes())
code,out=capture('whitespace-preservation-postapply-diffcheck-20261011-v1','git','diff','--cached','--check',required=False)
receipt=load(RUN/'whitespace-preservation-postapply-diffcheck-20261011-v1.json')
expected=RUN/'whitespace-exact-archival-diagnostics-20261011-v1.bin'
assert code==2 and receipt['stdout_sha256']==sha(expected), 'Unexpected diagnostics; retained failure, no blanket waiver'
for item in plan['files']: assert sha(ROOT/item['path'])==item['sha256']
write(RUN/'whitespace-preservation-apply-result-20261011-v1.json',dict(status='exact seven historical ordinary-space diagnostics retained',actual_diffcheck_exit=2,diagnostic_sha256=sha(expected),originals_unchanged=True,ordinary_errors_suppressed=False))
