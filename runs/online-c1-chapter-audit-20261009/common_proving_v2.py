from common_v1 import *
def fixed():
    assert Path.cwd()==ROOT and sha(PDF)==PDF_SHA
    assert subprocess.check_output(['git','branch','--show-current'],encoding='utf8').strip()==BRANCH
    plans=load(CONTRACT/'exact-import-plans-draft-v3.json')['rows']
    allowed={Path(r['path']).resolve().as_posix():r for r in plans}
    for r in load(RUN/'baseline-v2.json')['rows']:
        actual=sha(r['path'])
        if actual==r['sha256']:continue
        p=Path(r['path']).resolve().as_posix()
        assert p in allowed,('unapproved baseline mutation',p)
        a=allowed[p]
        assert sha(a['snapshot'])==r['sha256']==a['baseline_sha256']
        assert Path(p).read_bytes()==Path(a['snapshot']).read_bytes()+a['append_exact_utf8'].encode('utf8')
        assert actual==a['permitted_result_sha256']
        # A later canary integration must additionally supply its own BODY receipt.
        if Path(p).name=='Tests.lean':
            assert (RUN/'chapter-canary-BODY-receipt-v1.json').exists()
            assert load(RUN/'chapter-canary-BODY-receipt-v1.json')['verdict'] in ['accepted','accepted-with-explicit-delta']
    assert sha(RUN/'general-init-BODY-receipt-v1.json')=='ab038b4c25f861d2c0a10b102e1450a89c3a19a515d1c24e97838d3ffa467381'
    assert sha(ROOT/'BanditRLProof/OnlineFTLInitializationRegret.lean')=='bff3a313509aa19051a6f3f2cb912aec33ff61f5de8f88d9edd16e7964e3b614'
