from common_nonsmooth_publication_v2 import *

SITE=ROOT/'tmp/online-ch2-nonsmooth-site-v4'

def fixed():
    """Replay only exact independently reviewed byte transitions; old guards stay immutable."""
    assert Path.cwd()==ROOT and sha(PDF)==PDF_SHA
    assert subprocess.check_output(['git','branch','--show-current'],encoding='utf8').strip()==BRANCH
    p2=RUN/'nonsmooth-reader-repair-review-v2.json'
    assert sha(p2)=='bdf4567d876282b9d4936c87bfd9f8ebe55ca4438b49d049fab4289e639b6708'
    r2=load(p2);assert r2['verdict']==r2['reader_repair_verdict']==r2['future_publication_scope_verdict']=='accepted' and not r2['required_repairs']
    assert r2['approved_scope_sha256']==sha(CONTRACT/'nonsmooth-future-publication-scope-v2.json')
    assert r2['approved_reader_proposal_sha256']==sha(RUN/'nonsmooth-reader-proposal-v2.json')
    mat=load(CONTRACT/'nonsmooth-materialized-future-bytes-v1.json')
    assert sha(CONTRACT/'nonsmooth-materialized-future-bytes-v1.json')==r2['materialized_manifest_sha256']
    assert mat['rows']==r2['approved_materialized_bytes']
    allowed={Path(x['path']).resolve().as_posix():dict(x) for x in mat['rows']};assert len(allowed)==5
    history={k:{x['before_sha256'],x['after_sha256']} for k,x in allowed.items()}
    for a in allowed.values():assert sha(a['after_snapshot'])==a['after_sha256']
    p3=RUN/'nonsmooth-reader-link-repair-review-v3.json'
    assert sha(p3)=='9201b6d99f6fb771ca68cb07c317425158b0b97837001248ddcfa622164e32b1'
    r3=load(p3);assert r3['verdict']==r3['materialization_verdict']=='accepted' and not r3['required_repairs']
    assert r3['plan_sha256']==sha(CONTRACT/'nonsmooth-reader-link-repair-plan-v3.json')
    assert r3['proposal_sha256']==sha(RUN/'nonsmooth-reader-proposal-v3.json')
    patch=r3['approved_exact_materialization']
    assert sha(RUN/'nonsmooth-compiled-selected-graph-data-v2.json')==patch['compiled_graph_must_remain_exact']
    p4=RUN/'nonsmooth-reader-layout-repair-review-v4.json'
    assert sha(p4)=='2d4cd8b0447e9cf095c5e96f593cdf474afd901d66e9575bacf35b1c66d153dc'
    r4=load(p4);assert r4['verdict']==r4['repair_verdict']==r4['materialization_verdict']=='accepted' and not r4['required_repairs']
    assert r4['plan_sha256']==sha(CONTRACT/'nonsmooth-reader-layout-repair-plan-v4.json')
    assert r4['proposal_sha256']==sha(RUN/'nonsmooth-reader-proposal-v4.json')
    p5=RUN/'nonsmooth-formula-linebreak-review-v5.json'
    assert sha(p5)=='c054b274af7b16c323f30690bb836d512fff6fc3fa8899d7139c5a2da45b3c5c'
    r5=load(p5);assert r5['verdict']==r5['materialization_verdict']=='accepted' and not r5['required_repairs']
    assert r5['plan_sha256']==sha(CONTRACT/'nonsmooth-formula-linebreak-plan-v5.json')
    assert r5['proposal_sha256']==sha(RUN/'nonsmooth-reader-proposal-v5.json')
    transitions=[dict(path=patch['mutable_path'],before_sha256=patch['before_sha256'],after_snapshot=patch['after_snapshot'],after_sha256=patch['after_sha256']),*r4['approved_exact_materialization'],*r5['approved_exact_materialization']]
    assert len(transitions)==4
    for t in transitions:
        key=Path(t['path']).resolve().as_posix();a=allowed[key]
        assert a['after_sha256']==t['before_sha256'] and sha(t['after_snapshot'])==t['after_sha256']
        history[key].add(t['after_sha256']);a.update(after_snapshot=t['after_snapshot'],after_sha256=t['after_sha256'])
    for row in load(RUN/'baseline-v1.json')['rows']:
        key=Path(row['path']).resolve().as_posix()
        if key not in allowed:assert sha(row['path'])==row['sha256'],row['path']
        else:
            a=allowed[key];assert a['before_sha256']==row['sha256']
            assert sha(a['after_snapshot'])==sha(a['path'])==a['after_sha256']
            assert Path(a['path']).read_bytes()==Path(a['after_snapshot']).read_bytes()
    for review in [r3,r4,r5]:
        for row in review['raw_input_checks']:
            key=Path(row['path']).resolve().as_posix()
            if key in allowed:
                assert row['sha256'] in history[key] and sha(row['path'])==allowed[key]['after_sha256']
            else:assert sha(row['path'])==row['sha256'],row['path']
    assert sha(PUBLIC)==r2['reused_body_scope']['production_sha256']
    assert sha(CANARY)==r2['reused_body_scope']['canary_sha256']
    for path,contract in [(PUBLIC,CONTRACT/'nonsmooth-targets-draft-v1.json'),(CANARY,CONTRACT/'nonsmooth-canary-contracts-v2.json')]:
        for t in load(contract)['targets']:
            assert statement_hash(lean_declaration_header(path,t['declaration']))==t['statement_hash']
    for row in load(RUN/'source-contract-repair-review-v1.json')['raw_input_checks']:
        assert sha(row['path'])==row['before_sha256']==row['after_sha256']
