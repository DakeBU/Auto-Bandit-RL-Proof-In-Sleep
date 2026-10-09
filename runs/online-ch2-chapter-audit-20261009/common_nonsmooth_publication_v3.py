from common_nonsmooth_publication_v2 import *

SITE=ROOT/'tmp/online-ch2-nonsmooth-site-v2'

def fixed():
    assert Path.cwd()==ROOT and sha(PDF)==PDF_SHA
    assert subprocess.check_output(['git','branch','--show-current'],encoding='utf8').strip()==BRANCH
    rp=RUN/'nonsmooth-reader-link-repair-review-v3.json'
    assert sha(rp)=='9201b6d99f6fb771ca68cb07c317425158b0b97837001248ddcfa622164e32b1'
    r3=load(rp);assert r3['verdict']==r3['materialization_verdict']=='accepted' and r3['required_repairs']==[]
    assert sha(CONTRACT/'nonsmooth-reader-link-repair-plan-v3.json')==r3['plan_sha256']
    assert sha(RUN/'nonsmooth-reader-proposal-v3.json')==r3['proposal_sha256']
    patch=r3['approved_exact_materialization'];changed=Path(patch['mutable_path']).resolve()
    assert sha(patch['after_snapshot'])==sha(changed)==patch['after_sha256']
    assert Path(patch['after_snapshot']).read_bytes()==changed.read_bytes()
    assert sha(RUN/'nonsmooth-compiled-selected-graph-data-v2.json')==patch['compiled_graph_must_remain_exact']
    for row in r3['raw_input_checks']:
        expected=patch['after_sha256'] if Path(row['path']).resolve()==changed else row['sha256']
        assert sha(row['path'])==expected,row['path']
    review=RUN/'nonsmooth-reader-repair-review-v2.json'
    assert sha(review)=='bdf4567d876282b9d4936c87bfd9f8ebe55ca4438b49d049fab4289e639b6708'
    r=load(review)
    assert r['verdict']==r['reader_repair_verdict']==r['future_publication_scope_verdict']=='accepted' and r['required_repairs']==[]
    assert r['approved_scope_sha256']==sha(CONTRACT/'nonsmooth-future-publication-scope-v2.json')
    assert r['approved_reader_proposal_sha256']==sha(RUN/'nonsmooth-reader-proposal-v2.json')
    materialized=load(CONTRACT/'nonsmooth-materialized-future-bytes-v1.json')
    assert sha(CONTRACT/'nonsmooth-materialized-future-bytes-v1.json')==r['materialized_manifest_sha256']
    assert materialized['rows']==r['approved_materialized_bytes']
    allowed={Path(x['path']).resolve().as_posix():dict(x) for x in materialized['rows']}
    assert len(allowed)==5
    a=allowed[changed.as_posix()];assert a['after_sha256']==patch['before_sha256']
    assert sha(a['after_snapshot'])==patch['before_sha256']
    a.update(after_sha256=patch['after_sha256'],after_snapshot=patch['after_snapshot'])
    for row in load(RUN/'baseline-v1.json')['rows']:
        key=Path(row['path']).resolve().as_posix()
        if key not in allowed:assert sha(row['path'])==row['sha256'],row['path']
        else:
            a=allowed[key];assert a['before_sha256']==row['sha256']
            assert sha(a['after_snapshot'])==a['after_sha256']==sha(a['path'])
            assert Path(a['path']).read_bytes()==Path(a['after_snapshot']).read_bytes()
    assert sha(PUBLIC)==r['reused_body_scope']['production_sha256']
    assert sha(CANARY)==r['reused_body_scope']['canary_sha256']
    for path,contract in [(PUBLIC,CONTRACT/'nonsmooth-targets-draft-v1.json'),(CANARY,CONTRACT/'nonsmooth-canary-contracts-v2.json')]:
        for t in load(contract)['targets']:
            assert statement_hash(lean_declaration_header(path,t['declaration']))==t['statement_hash']
    for row in load(RUN/'source-contract-repair-review-v1.json')['raw_input_checks']:
        assert sha(row['path'])==row['before_sha256']==row['after_sha256']
