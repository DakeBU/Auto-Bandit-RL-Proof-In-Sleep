from common import *
import argparse, subprocess
ap=argparse.ArgumentParser();ap.add_argument('--review',required=True);ap.add_argument('--verify-final-staged',action='store_true');args=ap.parse_args()
planpath=RUN/'whitespace-preservation-proposal-20261011-v3.json';plan=load(planpath);review=load(args.review)
assert review['verdict']=='accepted' and review['blocking_repairs']==[]
assert review['approved_plan_raw_sha256']==sha(planpath)
assert review['approved_helper_raw_sha256']==sha(Path(__file__))
assert review['ordinary_archival_waiver_approved'] is True
for item in plan['files']: assert sha(ROOT/item['path'])==item['sha256'],item['path']
assert sha(RUN/'common.py')==plan['common_raw_sha256']
assert sha(ROOT/plan['raw_machine_capture']['path'])==plan['raw_machine_capture']['sha256']
if args.verify_final_staged:
    scopes=[RUN.relative_to(ROOT).as_posix(),CONTRACT.relative_to(ROOT).as_posix()]
    other=subprocess.check_output(['git','ls-files','--others','--exclude-standard','-z','--']+scopes,cwd=ROOT)
    assert not other, 'Untracked OWN files remain; parent must finish explicit staging first'
    entries=subprocess.check_output(['git','ls-files','--stage','-z','--']+scopes,cwd=ROOT)
    for entry in entries.split(b'\0'):
        if not entry:continue
        meta,name=entry.split(b'\t',1);mode,oid,stage=meta.split();assert stage==b'0' and mode in [b'100644',b'100755']
        raw=(ROOT/name.decode('utf8')).read_bytes()
        actual=hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest().encode()
        assert actual==oid, name
    for item in plan['attribute_changes']:assert sha(ROOT/item['path'])==item['after_sha256']
    label='whitespace-preservation-final-staged-diffcheck-20261011-v3'
else:
    for item in plan['attribute_changes']:
        assert sha(ROOT/item['path'])==item['before_sha256']
        assert sha(ROOT/item['after_snapshot'])==item['after_sha256']
        assert (ROOT/item['after_snapshot']).read_bytes().startswith((ROOT/item['path']).read_bytes())
    write(RUN/'whitespace-preservation-apply-started-20261011-v3.json',dict(plan_sha256=sha(planpath),review_path=args.review,review_sha256=sha(args.review)))
    for item in plan['attribute_changes']: (ROOT/item['path']).write_bytes((ROOT/item['after_snapshot']).read_bytes())
    label='whitespace-preservation-postapply-diffcheck-20261011-v3'
code,out=capture(label,'git','diff','--cached','--check',required=False)
receipt=load(RUN/(label+'.json'))
expected=RUN/'whitespace-exact-archival-diagnostics-20261011-v1.bin'
assert code==2 and receipt['stdout_sha256']==sha(expected), 'Unexpected diagnostics; retained failure, no blanket waiver'
for item in plan['files']: assert sha(ROOT/item['path'])==item['sha256']
write(RUN/(label+'-result.json'),dict(status='exact seven historical ordinary-space diagnostics retained',final_staged_precheck=args.verify_final_staged,result_receipts_created_after_index_check=True,actual_diffcheck_exit=2,diagnostic_sha256=sha(expected),originals_unchanged=True,ordinary_errors_suppressed=False))
