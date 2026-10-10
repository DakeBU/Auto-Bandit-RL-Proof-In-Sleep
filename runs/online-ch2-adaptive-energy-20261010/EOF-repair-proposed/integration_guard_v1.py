from common import *

TEST=ROOT/'Tests/OnlineAdaptiveEnergyCanary.lean'
PLAN=CONTRACT/'exact-integration-plan-v2.json'
CONTRIBUTION=ROOT/'research-wiki/contribution-contracts'/(TASK+'.json')
OLD_ALLOWED=['BanditRLProof.lean','Tests.lean','website/content/chapters.json',
             'website/content/readings.json','website/content/highlights.json',
             'docs/contracts/online-book-v1/coverage.json']

def approved_review():
    r=load(RUN/'integration-review-v1.json')
    assert r['verdict'] in ['accepted','accepted-with-explicit-delta'] and not r['required_repairs']
    assert sha(r['report'])==r['report_sha256'] and sha(r['input_manifest'])==r['input_manifest_sha256']
    assert r['approved_plan_sha256']==sha(PLAN)
    for row in r['approved_helper_hashes']: assert sha(row['path'])==row['sha256'],row['path']
    return r

def fixed_integration(after=True,full_old_baseline=False,review_inputs=False):
    assert Path.cwd()==ROOT and sha(PDF)==PDF_SHA
    assert subprocess.check_output(['git','branch','--show-current'],encoding='utf8').strip()==BRANCH
    plan=load(PLAN); allowed={r['path']:r for r in plan['rows']}
    assert len(allowed)==6 and set(allowed)=={(ROOT/p).as_posix() for p in OLD_ALLOWED}
    for row in allowed.values():
        assert sha(row['before_snapshot'])==row['before_sha256']
        assert sha(row['after_snapshot'])==row['after_sha256']
        assert sha(row['path'])==row['after_sha256' if after else 'before_sha256']
    assert sha(PUBLIC)==plan['production_sha256'] and sha(TEST)==plan['Test_sha256']
    assert sha(RUN/plan['prospective_manifest'])==plan['prospective_manifest_sha256']
    assert sha(CONTRACT/'shared-book-mapping-v1.json')==plan['mapping_sha256']
    r=approved_review()
    if review_inputs:
        for row in load(r['input_manifest'])['rows']:
            if after and row['path'] in allowed:
                assert row['sha256']==allowed[row['path']]['before_sha256']
            else: assert sha(row['path'])==row['sha256'],row['path']
    if full_old_baseline:
        for row in load(RUN/'baseline-v1.json')['rows']:
            if row['path'] in allowed: assert row['sha256']==allowed[row['path']]['before_sha256']
            else: assert sha(row['path'])==row['sha256'],row['path']
    if after: assert sha(CONTRIBUTION)==plan['prospective_manifest_sha256']
    else: assert not CONTRIBUTION.exists()
