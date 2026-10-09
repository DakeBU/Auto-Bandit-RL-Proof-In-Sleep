from publication_guard_v2 import *
SITE=ROOT/'tmp/online-ch2-prescient-site-v2'
def fixed():
    assert Path.cwd()==ROOT and sha(PDF)==PDF_SHA
    assert subprocess.check_output(['git','branch','--show-current'],encoding='utf8').strip()==BRANCH
    r1=load(RUN/'canary-BODY-publication-review-v1.json')
    assert sha(RUN/'canary-BODY-publication-review-v1.json')=='f8bf6e7dba1313581617c2f47df9521c34f0dffb0eda26b9a1e4ef49751e250d'
    assert not r1['required_repairs'] and r1['BODY_verdict']==r1['materialization_verdict']=='accepted'
    plan=CONTRACT/'exact-publication-plan-v1.json'
    assert sha(plan)==r1['approved_publication_plan_sha256'] and load(plan)['rows']==r1['approved_five_rows']
    allowed={Path(x['path']).resolve().as_posix():dict(x) for x in load(plan)['rows']};assert len(allowed)==5
    r2=load(RUN/'reader-status-and-RAW-review-v2.json')
    assert sha(RUN/'reader-status-and-RAW-review-v2.json')=='2c5fe701af837b64a2488e4979bb356ecdcb741acbeaba0fc6daf9ccf9c6084e'
    assert r2['verdict']=='accepted-with-explicit-delta' and not r2['required_repairs']
    assert sha(r2['approved_plan']['path'])==r2['approved_plan']['sha256']
    p=load(CONTRACT/'reader-status-and-RAW-plan-v2.json');assert p['reader_delta']==r2['approved_materialization']
    assert sha(RUN/'reader-proposal-status-v2.json')==r2['approved_proposal_sha256']
    delta=p['reader_delta'];key=Path(delta['path']).resolve().as_posix();a=allowed[key]
    assert a['after_sha256']==delta['before_sha256'] and sha(delta['after_snapshot'])==delta['after_sha256']
    a.update(after_snapshot=delta['after_snapshot'],after_sha256=delta['after_sha256'])
    r3=load(RUN/'reader-link-repair-review-v3.json')
    assert sha(RUN/'reader-link-repair-review-v3.json')=='8a19c46c9e007c03b8c3604110c7cfe43e42c52e7601a3bcc5a949afe06b3a0d'
    assert r3['verdict']=='accepted-with-explicit-delta' and not r3['required_repairs']
    assert sha(r3['approved_plan']['path'])==r3['approved_plan']['sha256']
    assert sha(r3['approved_proposal']['path'])==r3['approved_proposal']['sha256']
    p3=load(CONTRACT/'reader-link-repair-plan-v3.json');d3=r3['approved_materialization']
    assert all(p3[k]==d3[k] for k in d3)
    key3=Path(d3['mutable_path']).resolve().as_posix();a3=allowed[key3]
    assert a3['after_sha256']==d3['before_sha256'] and sha(d3['after_snapshot'])==d3['after_sha256']
    a3.update(after_snapshot=d3['after_snapshot'],after_sha256=d3['after_sha256'])
    assert sha(RUN/'complete-combined-selected-graph-data-v1.json')==p3['compiled_graph_sha256']
    for row in load(RUN/'baseline-v1.json')['rows']:
        key=Path(row['path']).resolve().as_posix()
        if key not in allowed:assert sha(row['path'])==row['sha256'],row['path']
        else:
            a=allowed[key];assert a['before_sha256']==row['sha256']
            assert sha(a['after_snapshot'])==sha(a['path'])==a['after_sha256']
            assert Path(a['path']).read_bytes()==Path(a['after_snapshot']).read_bytes()
    assert sha(PUBLIC)==r1['production_sha256'] and sha(CANARY)==r1['test_sha256']
    for p,c in [(PUBLIC,CONTRACT/'stabilized-v1.json'),(CANARY,CONTRACT/'canary-stabilized-v1.json')]:
        for t in load(c)['targets']:assert statement_hash(lean_declaration_header(p,t['declaration']))==t['statement_hash']
    assert r2['approved_RAW_EOF_exceptions']==load(CONTRACT/'reader-status-and-RAW-plan-v2.json')['immutable_RAW_EOF_exceptions']
    for row in r2['approved_RAW_EOF_exceptions']:assert sha(row['path'])==row['sha256']
