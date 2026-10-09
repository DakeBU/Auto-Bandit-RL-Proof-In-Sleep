from common import *
CANARY=ROOT/'Tests/OnlinePrescientBregmanRegretCanary.lean'
CONTRIBUTION=ROOT/'research-wiki/contribution-contracts'/(TASK+'.json')
SITE=ROOT/'tmp/online-ch2-prescient-cumulative-site-v1'
sys.path.insert(0,str(ROOT))
from tools.abrl_lifecycle import statement_hash,lean_declaration_header

def fixed():
    assert Path.cwd()==ROOT and sha(PDF)==PDF_SHA
    assert subprocess.check_output(['git','branch','--show-current'],encoding='utf8').strip()==BRANCH
    binding=load(RUN/'publication-review-binding-v1.json')
    br=RUN/'five-BODY-review-v1.json'; pr=RUN/'publication-plan-review-v3.json'
    assert sha(br)==binding['BODY_review_sha256'] and sha(pr)==binding['publication_review_sha256']
    for rp in [br,pr]:
        r=load(rp)
        assert r['verdict'] in ['accepted','accepted-with-explicit-delta'] and not r['required_repairs']
        assert sha(r['report'])==r['report_sha256']
    plan=CONTRACT/'exact-publication-plan-v2.json'
    assert sha(plan)==binding['plan_sha256']
    allowed={r['path']:r for r in load(plan)['rows']}
    assert set(allowed)=={(ROOT/p).as_posix() for p in ['BanditRLProof.lean','Tests.lean','website/content/chapters.json','website/content/readings.json','website/content/highlights.json']}
    for row in load(RUN/'baseline-v1.json')['rows']:
        if row['path'] not in allowed:
            assert sha(row['path'])==row['sha256'],row['path']
        else:
            a=allowed[row['path']]
            assert a['before_sha256']==row['sha256']
            assert sha(a['before_snapshot'])==a['before_sha256']
            assert sha(a['after_snapshot'])==sha(a['path'])==a['after_sha256']
    c=load(RUN/'canary-public-VALUE-inspected-v2.json')
    assert sha(PUBLIC)==c['production_sha256'] and sha(CANARY)==c['canary_sha256']
    for p,cp in [(PUBLIC,CONTRACT/'stabilized-v1.json'),(CANARY,CONTRACT/'canary-stabilized-v1.json')]:
        for t in load(cp)['targets']:
            assert t['exact_header'] in p.read_text(encoding='utf8')
            assert hashlib.sha256(t['exact_header'].encode('utf8')).hexdigest()==t['statement_sha256']
            fence=next(load(f) for f in CONTRACT.glob('*fence-v1.json') if load(f).get('declaration')==t['declaration'])
            assert statement_hash(lean_declaration_header(p,t['declaration']))==fence['statement_hash']
    assert sha(RUN/'selected-value-graph-v2.json')==binding['selected_graph_sha256']
