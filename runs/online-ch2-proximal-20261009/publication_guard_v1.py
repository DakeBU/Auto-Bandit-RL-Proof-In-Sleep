from common import *
CANARY=ROOT/'Tests/OnlineProximalComparisonCanary.lean'
CONTRIBUTION=ROOT/'research-wiki/contribution-contracts'/ (TASK+'.json')
SITE=ROOT/'tmp/online-ch2-proximal-site-v1'
sys.path.insert(0,str(ROOT))
from tools.abrl_lifecycle import statement_hash,lean_declaration_header
def fixed():
    assert Path.cwd()==ROOT and sha(PDF)==PDF_SHA
    assert subprocess.check_output(['git','branch','--show-current'],encoding='utf8').strip()==BRANCH
    review=RUN/'canary-BODY-publication-review-v2.json';r=load(review)
    assert sha(review)=='aa02adcdbacb70f6f0d0c9cd2566260aed27e46e373420e1db6c575aaf83203f'
    assert r['BODY_verdict']==r['materialization_verdict']=='accepted' and not r['required_repairs']
    plan=CONTRACT/'exact-publication-plan-v1.json';assert sha(plan)==r['approved_plan_sha256']
    assert load(plan)['rows']==r['approved_five_rows'] and sha(RUN/'reader-proposal-v1.json')==r['approved_proposal_sha256']
    allowed={x['path']:x for x in r['approved_five_rows']};assert len(allowed)==5
    for row in load(RUN/'baseline-v1.json')['rows']:
        if row['path'] not in allowed:assert sha(row['path'])==row['sha256'],row['path']
        else:
            a=allowed[row['path']];assert a['before_sha256']==row['sha256']
            assert sha(a['after_snapshot'])==sha(a['path'])==a['after_sha256']
            assert Path(a['path']).read_bytes()==Path(a['after_snapshot']).read_bytes()
    assert sha(PUBLIC)==r['production_sha256'] and sha(CANARY)==r['test_sha256']
    for p,c in [(PUBLIC,CONTRACT/'stabilized-v1.json'),(CANARY,CONTRACT/'canary-stabilized-v1.json')]:
        for t in load(c)['targets']:assert statement_hash(lean_declaration_header(p,t['declaration']))==t['statement_hash']
    assert sha(RUN/'selected-compiled-dependencies-data-v3.json')==r['selected_graph_sha256']
