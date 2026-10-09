from common import *
sys.path.insert(0,str(ROOT))
from tools.abrl_lifecycle import lean_declaration_header,statement_hash
CANARY=ROOT/'Tests/OnlinePrescientLinearCanary.lean'
CONTRIBUTION=ROOT/'research-wiki/contribution-contracts/ONLINE-CH2-PRESCIENT-20261009.json'
SITE=ROOT/'tmp/online-ch2-prescient-site-v1'
def fixed():
    assert Path.cwd()==ROOT and sha(PDF)==PDF_SHA
    assert subprocess.check_output(['git','branch','--show-current'],encoding='utf8').strip()==BRANCH
    review=RUN/'canary-BODY-publication-review-v1.json'
    assert sha(review)=='f8bf6e7dba1313581617c2f47df9521c34f0dffb0eda26b9a1e4ef49751e250d'
    r=load(review);assert r['BODY_verdict']==r['materialization_verdict']=='accepted' and not r['required_repairs']
    plan=CONTRACT/'exact-publication-plan-v1.json'
    assert sha(plan)==r['approved_publication_plan_sha256'] and load(plan)['rows']==r['approved_five_rows']
    assert sha(RUN/'reader-proposal-v1.json')==r['reader_proposal_sha256']
    allowed={Path(x['path']).resolve().as_posix():x for x in load(plan)['rows']};assert len(allowed)==5
    for row in load(RUN/'baseline-v1.json')['rows']:
        key=Path(row['path']).resolve().as_posix()
        if key not in allowed:assert sha(row['path'])==row['sha256'],row['path']
        else:
            a=allowed[key];assert a['before_sha256']==row['sha256']
            assert sha(a['after_snapshot'])==sha(a['path'])==a['after_sha256']
            assert Path(a['path']).read_bytes()==Path(a['after_snapshot']).read_bytes()
    assert sha(PUBLIC)==r['production_sha256'] and sha(CANARY)==r['test_sha256']
    for p,c in [(PUBLIC,CONTRACT/'stabilized-v1.json'),(CANARY,CONTRACT/'canary-stabilized-v1.json')]:
        for t in load(c)['targets']:assert statement_hash(lean_declaration_header(p,t['declaration']))==t['statement_hash']
