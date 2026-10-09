from common_nonsmooth_roots_v1 import *
import base64,re

fixed()
assert not subprocess.check_output(['git','diff','--cached','--name-only'],encoding='utf8').strip()
capture('nonsmooth-stage-two-new-Lean-v1','git','add',PUBLIC.relative_to(ROOT).as_posix(),CANARY.relative_to(ROOT).as_posix())
results=[]
for label,target in [('nonsmooth-combined-root-v1','BanditRLProof'),('nonsmooth-combined-Tests-v1','Tests')]:
    code,out=capture(label,'lake','build',target,required=False)
    assert code==0,label
    jobs=re.findall(r'Build completed successfully \((\d+) jobs\)',out)
    assert jobs and 'error: build failed' not in out and 'Lean exited with code 1' not in out
    results.append(dict(label=label,actual_exit=code,actual_cached_inclusive_success_jobs=list(map(int,jobs)),receipt_sha256=sha(RUN/(label+'.json'))))
    fixed()
write(RUN/'nonsmooth-combined-root-Tests-inspected-v1.json',dict(
    rows=results,actual_root_Tests_passed=True,production_sha256=sha(PUBLIC),canary_sha256=sha(CANARY),
    root_sha256=sha(ROOT/'BanditRLProof.lean'),Tests_root_sha256=sha(ROOT/'Tests.lean'),
    full_harness_reader_registry_site_FINAL_delivery_pending=True,chapter_complete=False,whole_Goal_status='ACTIVE'))
print('Actual combined shared root and Tests compiler markers inspected; full harness and all publication gates still pending.')
