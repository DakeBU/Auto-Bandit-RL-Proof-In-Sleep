from common import *
sys.path.insert(0,str(ROOT))
from tools import abrl_lifecycle as lifecycle
MODULE=PUBLIC
TEST=ROOT/'Tests/OnlineAdaptiveSummationCanary.lean'
CONTRIBUTION=ROOT/'research-wiki/contribution-contracts'/(TASK+'.json')
SITE=ROOT/'tmp/online-ch2-adaptive-summation-site-v1'
OLD_ALLOWED=['BanditRLProof.lean','Tests.lean','website/content/chapters.json','website/content/readings.json','website/content/highlights.json','docs/contracts/online-book-v1/coverage.json']

REPAIR_PLAN=RUN/'candidate-whitespace-repair-plan-v2.json'
REPAIR_REVIEW=RUN/'candidate-whitespace-repair-review-v2.json'

def repair_row(row):
    changes={r['path']:r for r in load(REPAIR_PLAN)['rows']}
    if row['path'] in changes:
        a=changes[row['path']]
        original=base64.b64decode(a['before_raw_base64'])
        assert hashlib.sha256(original).hexdigest()==a['before_sha256']==row['sha256']
        assert sha(a['path'])==a['after_sha256']==sha(a['after_snapshot'])
    else: assert sha(row['path'])==row['sha256'],row['path']

def repair_review_fixed():
    r=load(REPAIR_REVIEW)
    assert r['verdict'] in ['accepted','accepted-with-explicit-delta'] and not r['required_repairs']
    assert sha(r['report'])==r['report_sha256'] and sha(r['input_manifest'])==r['input_manifest_sha256']
    assert r['approved_repair_plan_sha256']==sha(REPAIR_PLAN)
    for row in load(r['input_manifest'])['rows']: repair_row(row)
    for row in r['approved_helper_hashes']: assert sha(row['path'])==row['sha256'],row['path']
    for row in load(REPAIR_PLAN)['retained_CRLF_metadata']: assert sha(row['path'])==row['sha256']

def verify_review(path,allowed,after):
    d=load(path)
    assert d['verdict'] in ['accepted','accepted-with-explicit-delta'] and not d['required_repairs']
    assert sha(d['report'])==d['report_sha256'] and sha(d['input_manifest'])==d['input_manifest_sha256']
    for row in load(d['input_manifest'])['rows']:
        if after and row['path'] in allowed:
            a=allowed[row['path']]
            assert row['sha256']==a['before_sha256']==sha(a['before_snapshot'])
            assert sha(row['path'])==a['after_sha256']==sha(a['after_snapshot'])
        else: repair_row(row)
    return d

def fixed(after=True):
    repair_review_fixed()
    assert Path.cwd()==ROOT and sha(PDF)==PDF_SHA
    assert subprocess.check_output(['git','branch','--show-current'],encoding='utf8').strip()==BRANCH
    plan_path=CONTRACT/'exact-integration-plan-v1.json';plan=load(plan_path)
    allowed={r['path']:r for r in plan['rows']}
    assert set(allowed)=={(ROOT/p).as_posix() for p in OLD_ALLOWED} and len(allowed)==6
    for a in allowed.values():
        assert sha(a['before_snapshot'])==a['before_sha256'] and sha(a['after_snapshot'])==a['after_sha256']
        assert sha(a['path'])==a['after_sha256' if after else 'before_sha256']
    for row in load(RUN/'baseline-v1.json')['rows']:
        if row['path'] in allowed: assert row['sha256']==allowed[row['path']]['before_sha256']
        else: assert sha(row['path'])==row['sha256'],row['path']
    body=verify_review(RUN/'canary-BODY-review-v1.json',allowed,after)
    assert body['canary_BODY_accepted'] and sha(MODULE)==body['production_sha256'] and sha(TEST)==body['Test_sha256']
    review=verify_review(RUN/'integration-plan-review-v1.json',allowed,after)
    assert review['approved_plan_sha256']==sha(plan_path) and review['approved_rows']==plan['rows']
    assert review['integration_helper_verdict'] in ['accepted','accepted-with-explicit-delta']
    for row in review['approved_helper_hashes']: assert sha(row['path'])==row['sha256'],row['path']
    assert sha(RUN/'reader-proposal-v1.json')==plan['reader_proposal_sha256']
    assert sha(CONTRACT/'shared-book-mapping-v1.json')==plan['mapping_sha256']
    assert sha(RUN/'prospective-contribution-v1.json')==plan['prospective_manifest_sha256']
    for file,ctx,end,headers in [
        (MODULE,CONTRACT/'definition-context-v2.lean.txt','end BanditRL.OnlineAdaptiveSummation\n',CONTRACT/'frozen-headers-draft-v2.json'),
        (TEST,CONTRACT/'canary-v1/definition-context-draft-v1.lean.txt','end Tests.OnlineAdaptiveSummationCanary\n',CONTRACT/'canary-v1/frozen-headers-draft-v1.json')]:
        source=file.read_text(encoding='utf8');context=ctx.read_text(encoding='utf8')
        assert source.startswith(context[:-len(end)]) and source.endswith(end)
        assert not any(t in source.split() for t in ['sorry','admit','axiom','postulate'])
        for row in load(headers)['rows']:
            assert row['exact_header']+' := by' in source
            assert lifecycle.statement_hash(lifecycle.lean_declaration_header(file,row['declaration']))==row['normalized_header_sha256']
    if after: assert sha(CONTRIBUTION)==plan['prospective_manifest_sha256']
    else: assert not CONTRIBUTION.exists()
