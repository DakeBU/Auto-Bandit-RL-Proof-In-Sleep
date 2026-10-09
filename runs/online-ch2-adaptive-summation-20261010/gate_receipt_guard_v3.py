from common import *

def actual_gates_fixed():
    d=load(RUN/'full-harness-inspected-v1.json')
    assert d['actual_exit']==0 and d['actual_check_passed'] and d['actual_ProofGraphExport_compile_present']
    assert d['unittest_runs'] and d['cached_inclusive_successful_build_jobs']
    receipt=Path(d['actual_success_command_receipt'])
    assert receipt==RUN/'combined-full-harness-v2.json'
    assert sha(receipt)==d['command_receipt_sha256']
    failed=RUN/'combined-full-harness-v1.json'
    assert sha(failed)==d['retained_failed_v1_sha256'] and load(failed)['actual_exit']==1
    actual=load(receipt);assert actual['actual_exit']==0
    assert actual['command'][-2:]==['tools/bandit.py','check'] and actual['cwd']==ROOT.as_posix()
    out=base64.b64decode(actual['stdout_base64']).decode('utf8')
    import re
    assert hashlib.sha256(base64.b64decode(actual['stdout_base64'])).hexdigest()==actual['stdout_sha256']
    assert 'check passed' in out and 'tools/ProofGraphExport.lean' in out
    assert re.search(r'Build completed successfully \(\d+ jobs\)',out) and re.search(r'Ran \d+ tests in ',out) and re.search(r'\nOK(?: \(skipped=\d+\))?\s',out)
    assert all(s not in out for s in ['error: build failed','Lean exited with code 1','forbidden placeholder scan failed'])
    for key,p in [('production_sha256',MODULE),('Test_sha256',TEST),('root_sha256',ROOT/'BanditRLProof.lean'),('Test_root_sha256',ROOT/'Tests.lean')]: assert sha(p)==d[key]
    for p,h in d['source_pins'].items(): assert sha(ROOT/p)==h
    roots=load(RUN/'combined-root-Tests-inspected-v1.json')
    assert roots['root_Tests_passed'] and {r['target'] for r in roots['rows']}=={'BanditRLProof','Tests'}
    for r in roots['rows']: assert r['actual_exit']==0 and r['cached_inclusive_jobs'] and sha(RUN/('combined-root-v1.json' if r['target']=='BanditRLProof' else 'combined-Tests-v1.json'))==r['receipt_sha256']


def gate_binding_review_fixed(after):
    p=RUN/'candidate-gate-binding-review-v3.json';r=load(p)
    assert r['verdict'] in ['accepted','accepted-with-explicit-delta'] and not r['required_repairs']
    assert sha(r['report'])==r['report_sha256'] and sha(r['input_manifest'])==r['input_manifest_sha256']
    assert r['approved_success_receipt']==(RUN/'combined-full-harness-v2.json').as_posix()
    for row in load(r['input_manifest'])['rows']:
        if after:
            from integration_guard_v2 import repair_row
            repair_row(row)
        else: assert sha(row['path'])==row['sha256'],row['path']
    for row in r['approved_helper_hashes']: assert sha(row['path'])==row['sha256'],row['path']
