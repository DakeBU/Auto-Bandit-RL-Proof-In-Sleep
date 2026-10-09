from common_v1 import *
PUBLIC=ROOT/'BanditRLProof/OnlineFTLInitializationRegret.lean'
CANARY=ROOT/'Tests/OnlineLearningChapterAuditCanary.lean'
CONTRIBUTION=ROOT/('research-wiki/contribution-contracts/'+TASK+'.json')
SITE=ROOT/'tmp/online-c1-chapter-audit-site-v4'

def fixed():
    assert Path.cwd()==ROOT and sha(PDF)==PDF_SHA
    assert subprocess.check_output(['git','branch','--show-current'],encoding='utf8').strip()==BRANCH
    assert sha(PUBLIC)=='bff3a313509aa19051a6f3f2cb912aec33ff61f5de8f88d9edd16e7964e3b614'
    assert sha(CANARY)==load(RUN/'chapter-canary-BODY-receipt-v1.json')['test_module_sha256']=='746fc763bf61afffbe57fa2542edf2c77a2e55ca1ea3306b25ff0e2e5f0d3d31'
    assert sha(RUN/'general-init-BODY-receipt-v1.json')=='ab038b4c25f861d2c0a10b102e1450a89c3a19a515d1c24e97838d3ffa467381'
    assert sha(RUN/'chapter-canary-BODY-receipt-v1.json')=='387496d0a7ddf05a3dac7568d053e8d9bfba67e620ae9a2614e80df8d0abbe1a'
    assert sha(RUN/'publication-scope-receipt-v4.json')=='55daad9c2492f90d36dca59365fab26d49c21d86de5b549dead91f5a0cd72095'
    roots={Path(r['path']).resolve().as_posix():r for r in load(CONTRACT/'exact-import-plans-draft-v3.json')['rows']}
    readers={Path(r['path']).resolve().as_posix():r for r in load(RUN/'reader-integration-bindings-v6.json')['rows']}
    assert len(roots)==2 and len(readers)==4
    for r in load(RUN/'baseline-v2.json')['rows']:
        actual=sha(r['path']);p=Path(r['path']).resolve().as_posix()
        if actual==r['sha256']:continue
        if p in roots:
            a=roots[p];assert sha(a['snapshot'])==r['sha256']==a['baseline_sha256']
            assert Path(p).read_bytes()==Path(a['snapshot']).read_bytes()+a['append_exact_utf8'].encode('utf8')
            assert actual==a['permitted_result_sha256']
        elif p in readers:
            a=readers[p];assert sha(a['before'])==r['sha256']==a['before_sha256']
            assert sha(a['planned_result_snapshot'])==actual==a['result_sha256']
            assert Path(p).read_bytes()==Path(a['planned_result_snapshot']).read_bytes()
        else:raise AssertionError(('Unapproved baseline mutation',p))
    for a in readers.values():
        assert sha(a['planned_result_snapshot'])==sha(a['path'])==a['result_sha256']
    g=load(RUN/'combined-gates-inspected-v1.json')
    assert g['actual_shared_root_Tests_fullharness_passed'] and g['applicable_public_sha256']==sha(PUBLIC) and g['applicable_Test_sha256']==sha(CANARY)
    assert g['pins']=={p:sha(ROOT/p) for p in ['lean-toolchain','lakefile.lean','lake-manifest.json']}

def native(label,*args):return gate(label,sys.executable,'-B','-X','utf8',RUN/'native-scoped-v1.py',*args)
