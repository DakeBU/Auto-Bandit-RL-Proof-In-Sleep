from common import *
sys.path.insert(0,str(ROOT))
from tools import abrl_lifecycle as lifecycle
TEST=ROOT/'Tests/OnlineUnboundedOSDCanary.lean'
CONTRIBUTION=ROOT/'research-wiki/contribution-contracts'/(TASK+'.json')
SITE=ROOT/'tmp/online-ch2-unbounded-osd-site-v1'

def fixed():
    assert Path.cwd()==ROOT and sha(PDF)==PDF_SHA
    assert subprocess.check_output(['git','branch','--show-current'],encoding='utf8').strip()==BRANCH
    binding=load(RUN/'publication-review-binding-v1.json')
    for file,key in [('canary-BODY-review-v1.json','BODY_review_sha256'),('publication-plan-review-v1.json','publication_review_sha256')]:
        p=RUN/file;r=load(p)
        assert sha(p)==binding[key] and r['verdict'] in ['accepted','accepted-with-explicit-delta'] and not r['required_repairs']
        assert sha(r['report'])==r['report_sha256'] and sha(r['input_manifest'])==r['input_manifest_sha256']
        repair=load(RUN/'guard-whitespace-repair-review-v2.json')
        assert repair['verdict'] in ['accepted','accepted-with-explicit-delta'] and not repair['required_repairs']
        assert sha(repair['report'])==repair['report_sha256'] and sha(repair['input_manifest'])==repair['input_manifest_sha256']
        for rr in load(repair['input_manifest'])['rows']:assert sha(rr['path'])==rr['sha256'],rr['path']
        delta=load(RUN/'guard-whitespace-exact-plan-v2.json')
        assert repair['approved_plan_sha256']==sha(RUN/'guard-whitespace-exact-plan-v2.json')
        for row in load(r['input_manifest'])['rows']:
            if row['path']==delta['guard_path']:
                assert row['sha256']==delta['guard_before_sha256']
                raw=base64.b64decode(load(RUN/'guard-whitespace-before-v1.json')['before_raw_base64'])
                assert hashlib.sha256(raw).hexdigest()==row['sha256']
                assert sha(row['path'])==delta['guard_after_sha256']
            else:assert sha(row['path'])==row['sha256'],row['path']
    plan=CONTRACT/'exact-publication-plan-v1.json'
    assert sha(plan)==binding['plan_sha256']
    allowed={r['path']:r for r in load(plan)['rows']}
    assert set(allowed)=={(ROOT/p).as_posix() for p in ['BanditRLProof.lean','Tests.lean','website/content/chapters.json','website/content/readings.json','website/content/highlights.json']}
    for row in load(RUN/'baseline-v1.json')['rows']:
        if row['path'] in allowed:
            a=allowed[row['path']]
            assert row['sha256']==a['before_sha256']==sha(a['before_snapshot'])
            assert sha(a['path'])==a['after_sha256']==sha(a['after_snapshot'])
        else:assert sha(row['path'])==row['sha256'],row['path']
    assert sha(PUBLIC)==binding['production_sha256'] and sha(TEST)==binding['Test_sha256']
    st=load(CONTRACT/'stabilized-v1.json');cs=load(CONTRACT/'canary-headers-draft-v2.json')
    for row in st['targets']+cs['targets']:
        file=PUBLIC if row in st['targets'] else TEST
        assert lifecycle.statement_hash(lifecycle.lean_declaration_header(file,row['name']))==load(CONTRACT/('frozen-'+row['name'].rsplit('.',1)[1]+'-v1.json'))['statement_hash']
    assert PUBLIC.read_bytes().startswith(base64.b64decode(load(CONTRACT/'definitions-frozen-v1.json')['raw_base64']))
