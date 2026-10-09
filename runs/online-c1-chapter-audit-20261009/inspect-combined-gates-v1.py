from common_proving_v2 import *
import re
fixed()
v=load(RUN/'combined-gates-v1.json');assert v['actual_exit_codes']==[0,0,0]
out=[]
for label in ['combined-root-v1','combined-Tests-v1','combined-full-harness-v1']:
    raw=(RUN/(label+'.log')).read_text('utf8')
    receipt=load(RUN/(label+'-exit.json'))
    assert receipt['actual_exit']==0 and receipt['log_sha256']==sha(RUN/(label+'.log'))
    jobs=list(map(int,re.findall(r'Build completed successfully \((\d+) jobs\)',raw)))
    assert jobs and 'error: build failed' not in raw and 'Lean exited with code 1' not in raw,label
    row=dict(label=label,actual_successful_build_jobs=jobs,actual_exit=0,log_sha256=sha(RUN/(label+'.log')))
    if label=='combined-full-harness-v1':
        found=re.findall(r'Ran (\d+) tests in ([\d.]+)s',raw)
        assert found and re.search(r'\nOK(?: \(skipped=\d+\))?\s',raw) and 'check passed' in raw
        assert 'forbidden placeholder scan failed' not in raw
        row['unittest_runs']=[dict(test_count=int(n),seconds=float(s)) for n,s in found]
        row['skip_markers']=re.findall(r'OK \(skipped=(\d+)\)',raw)
        row['actual_check_passed_marker']=True
        row['actual_exporter_compile_command_in_log']='tools/ProofGraphExport.lean' in raw
        assert row['actual_exporter_compile_command_in_log']
    out.append(row)
write(RUN/'combined-gates-inspected-v1.json',dict(rows=out,actual_shared_root_Tests_fullharness_passed=True,applicable_public_sha256=sha(ROOT/'BanditRLProof/OnlineFTLInitializationRegret.lean'),applicable_Test_sha256=sha(ROOT/'Tests/OnlineLearningChapterAuditCanary.lean'),pins=v['source_pins'],source_gate_separate=True,chapter_complete=False,goal_complete=False))
fixed()
print('Actual compiler/Test/unittest/exporter/check markers inspected; source/chapter acceptance still separate.',flush=True)
