from common import *

def verify_candidate_plan():
    p=RUN/'candidate-git-site-plan-review-v1.json'
    assert sha(p)=='ff2d8854b7e320e4b94a38958d958eacfaf34a8cc029e11fb7b3b915ed113585'
    r=load(p);assert r['verdict']=='accepted-with-explicit-delta' and not r['required_repairs']
    assert sha(r['report'])==r['report_sha256'] and sha(r['input_manifest'])==r['input_manifest_sha256']
    for row in load(r['input_manifest'])['rows']:assert sha(row['path'])==row['sha256'],row['path']
    for row in r['approved_helper_hashes']:assert sha(row['path'])==row['sha256'],row['path']
    return r
