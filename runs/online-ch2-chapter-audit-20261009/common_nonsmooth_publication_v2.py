from common_v1 import *
from lower_common_v1 import capture,event
sys.path.insert(0,str(ROOT))
from tools.abrl_lifecycle import lean_declaration_header,statement_hash

PUBLIC=ROOT/'BanditRLProof/OnlineNonsmoothExamples.lean'
CANARY=ROOT/'Tests/OnlineNonsmoothExamplesCanary.lean'
CONTRIBUTION=ROOT/'research-wiki/contribution-contracts/ONLINE-CH2-NONSMOOTH-20261009.json'
SITE=ROOT/'tmp/online-ch2-nonsmooth-site-v1'

def fixed():
    """Exact reviewed publication stage; earlier guards remain historical."""
    assert Path.cwd()==ROOT and sha(PDF)==PDF_SHA
    assert subprocess.check_output(['git','branch','--show-current'],encoding='utf8').strip()==BRANCH
    review=RUN/'nonsmooth-reader-repair-review-v2.json'
    assert sha(review)=='bdf4567d876282b9d4936c87bfd9f8ebe55ca4438b49d049fab4289e639b6708'
    r=load(review)
    assert r['verdict']==r['reader_repair_verdict']==r['future_publication_scope_verdict']=='accepted'
    assert r['required_repairs']==[]
    assert r['approved_scope_sha256']==sha(CONTRACT/'nonsmooth-future-publication-scope-v2.json')
    assert r['approved_reader_proposal_sha256']==sha(RUN/'nonsmooth-reader-proposal-v2.json')
    materialized=load(CONTRACT/'nonsmooth-materialized-future-bytes-v1.json')
    assert sha(CONTRACT/'nonsmooth-materialized-future-bytes-v1.json')==r['materialized_manifest_sha256']
    assert materialized['rows']==r['approved_materialized_bytes']
    allowed={Path(x['path']).resolve().as_posix():x for x in materialized['rows']}
    assert len(allowed)==5
    for row in load(RUN/'baseline-v1.json')['rows']:
        key=Path(row['path']).resolve().as_posix()
        if key not in allowed:
            assert sha(row['path'])==row['sha256'],row['path']
        else:
            a=allowed[key]
            assert a['before_sha256']==row['sha256']
            assert sha(a['after_snapshot'])==a['after_sha256']==sha(a['path'])
            assert Path(a['path']).read_bytes()==Path(a['after_snapshot']).read_bytes()
    assert sha(PUBLIC)==r['reused_body_scope']['production_sha256']
    assert sha(CANARY)==r['reused_body_scope']['canary_sha256']
    for path,contract in [(PUBLIC,CONTRACT/'nonsmooth-targets-draft-v1.json'),(CANARY,CONTRACT/'nonsmooth-canary-contracts-v2.json')]:
        for t in load(contract)['targets']:
            assert statement_hash(lean_declaration_header(path,t['declaration']))==t['statement_hash']
    for row in load(RUN/'source-contract-repair-review-v1.json')['raw_input_checks']:
        assert sha(row['path'])==row['before_sha256']==row['after_sha256']
