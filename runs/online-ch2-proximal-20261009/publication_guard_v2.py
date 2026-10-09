from publication_guard_v1 import *

def fixed():
    assert Path.cwd()==ROOT and sha(PDF)==PDF_SHA
    assert subprocess.check_output(['git','branch','--show-current'],encoding='utf8').strip()==BRANCH
    review=RUN/'canary-BODY-publication-review-v2.json';r=load(review)
    assert sha(review)=='aa02adcdbacb70f6f0d0c9cd2566260aed27e46e373420e1db6c575aaf83203f'
    sr=RUN/'publication-status-review-v2.json';s=load(sr)
    assert sha(sr)=='8ea3f8c6cc779abc9cc619d7a8fa83e55e5420a7c178e81d32e42913887f0eb3'
    assert not s['required_repairs']
    delta=s['approved_materialization']
    assert sha(RUN/'publication-status-proposal-v2.json')==s['approved_proposal_sha256']
    assert sha(delta['before_snapshot'])==delta['before_sha256']
    assert sha(delta['path'])==sha(delta['after_snapshot'])==delta['after_sha256']
    assert Path(delta['path']).read_bytes()==Path(delta['after_snapshot']).read_bytes()
    assert r['BODY_verdict']==r['materialization_verdict']=='accepted' and not r['required_repairs']
    plan=CONTRACT/'exact-publication-plan-v1.json';assert sha(plan)==r['approved_plan_sha256']
    assert load(plan)['rows']==r['approved_five_rows'] and sha(RUN/'reader-proposal-v1.json')==r['approved_proposal_sha256']
    allowed={x['path']:x for x in r['approved_five_rows']};assert len(allowed)==5
    for row in load(RUN/'baseline-v1.json')['rows']:
        if row['path'] not in allowed:assert sha(row['path'])==row['sha256'],row['path']
        else:
            a=allowed[row['path']];assert a['before_sha256']==row['sha256']
            if a['path']==delta['path']:
                assert sha(a['after_snapshot'])==a['after_sha256']==delta['before_sha256']
            else:
                assert sha(a['after_snapshot'])==sha(a['path'])==a['after_sha256']
                assert Path(a['path']).read_bytes()==Path(a['after_snapshot']).read_bytes()
    assert sha(PUBLIC)==r['production_sha256'] and sha(CANARY)==r['test_sha256']
    for p,c in [(PUBLIC,CONTRACT/'stabilized-v1.json'),(CANARY,CONTRACT/'canary-stabilized-v1.json')]:
        for t in load(c)['targets']:assert statement_hash(lean_declaration_header(p,t['declaration']))==t['statement_hash']
    assert sha(RUN/'selected-compiled-dependencies-data-v3.json')==r['selected_graph_sha256']
    for x in s['approved_RAW_EOF_exceptions']:assert sha(x['path'])==x['sha256']
