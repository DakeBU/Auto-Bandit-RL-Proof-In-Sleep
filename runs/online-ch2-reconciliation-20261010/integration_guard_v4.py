from common import *
sys.path.insert(0,str(ROOT))
from tools import abrl_lifecycle as lifecycle
MODULE=ROOT/'BanditRLProof/OnlineFTLSelector.lean'
TEST=ROOT/'Tests/OnlineFTLSelectorCanary.lean'
LEAF=CONTRACT/'generic-ftl-v1'
CANARY=LEAF/'canary-v2'
CONTRIBUTION=ROOT/'research-wiki/contribution-contracts'/(TASK+'.json')
SITE=ROOT/'tmp/online-ch2-reconciliation-site-v1'
OLD_ALLOWED=['BanditRLProof.lean','Tests.lean','website/content/chapters.json',
             'website/content/readings.json','website/content/highlights.json','docs/contracts/online-book-v1/coverage.json']

def verify_review(path,allowed,after):
    r=load(path)
    assert r['verdict'] in ['accepted','accepted-with-explicit-delta'] and not r['required_repairs']
    assert sha(r['report'])==r['report_sha256'] and sha(r['input_manifest'])==r['input_manifest_sha256']
    for row in load(r['input_manifest'])['rows']:
        if after and row['path'] in allowed:
            a=allowed[row['path']]
            assert row['sha256']==a['before_sha256']==sha(a['before_snapshot'])
            assert sha(row['path'])==a['after_sha256']==sha(a['after_snapshot'])
        else:assert sha(row['path'])==row['sha256'],row['path']
    return r

def fixed(after=True):
    assert Path.cwd()==ROOT and sha(PDF)==PDF_SHA
    assert subprocess.check_output(['git','branch','--show-current'],encoding='utf8').strip()==BRANCH
    plan_path=CONTRACT/'exact-integration-plan-v1.json';plan=load(plan_path)
    allowed={r['path']:r for r in plan['rows']}
    assert len(allowed)==6 and set(allowed)=={(ROOT/p).as_posix() for p in OLD_ALLOWED}
    for a in allowed.values():
        assert sha(a['before_snapshot'])==a['before_sha256'] and sha(a['after_snapshot'])==a['after_sha256']
        assert sha(a['path'])==a['after_sha256' if after else 'before_sha256']
    for row in load(RUN/'baseline-v1.json')['rows']:
        if row['path'] in allowed:
            assert row['sha256']==allowed[row['path']]['before_sha256']
        else:assert sha(row['path'])==row['sha256'],row['path']
    br=verify_review(RUN/'ftl-canary-BODY-review-v1.json',allowed,after)
    assert br['canary_BODY_accepted'] and sha(MODULE)==br['production_sha256'] and sha(TEST)==br['Test_sha256']
    pr=verify_review(RUN/'integration-plan-review-v2.json',allowed,after)
    assert pr['approved_plan_sha256']==sha(plan_path) and pr['approved_rows']==plan['rows']
    assert pr['integration_helper_verdict'] in ['accepted','accepted-with-explicit-delta']
    for row in pr['approved_helper_hashes']:
        assert sha(row['path'])==row['sha256'],row['path']
    # This explicitly bounded conversion preserves old review inputs in BEFORE snapshots.
    # In particular the prior production review indexed the shared coverage file.
    verify_review(RUN/'production-BODY-canary-CONTRACT-repair-review-v1.json',allowed,after)
    assert sha(RUN/'reader-proposal-v1.json')==plan['reader_proposal_sha256']
    assert sha(CONTRACT/'qualified-source-reconciliation-draft-v4.json')==plan['source_join_sha256']
    for file,ctx,end,headers in [
        (MODULE,LEAF/'definition-context-v1.lean.txt','end BanditRL.OnlineFTLSelector\n',LEAF/'frozen-headers-draft-v1.json'),
        (TEST,CANARY/'definition-context-v2.lean.txt','end Tests.OnlineFTLSelector\n',CANARY/'frozen-headers-draft-v2.json')]:
        source=file.read_text(encoding='utf8');context=ctx.read_text(encoding='utf8')
        assert source.startswith(context[:-len(end)]) and source.endswith(end)
        assert not any(t in source.split() for t in ['sorry','admit','axiom'])
        for row in load(headers)['rows']:
            assert row['exact_header']+' := by' in source
            expected=row.get('normalized_header_sha256',row.get('header_sha256'))
            if expected is None:expected=lifecycle.statement_hash(row['exact_header'])
            assert lifecycle.statement_hash(lifecycle.lean_declaration_header(file,row['declaration']))==expected
    if after:
        assert sha(CONTRIBUTION)==sha(RUN/'prospective-contribution-v3.json')
        before=load(RUN/'prospective-contribution-v2.json');current=load(CONTRIBUTION)
        assert isinstance(before['verification']['focused_checks'],str)
        assert current['verification']['focused_checks']==[before['verification']['focused_checks']]
        current['verification']['focused_checks']=before['verification']['focused_checks']
        assert current==before
