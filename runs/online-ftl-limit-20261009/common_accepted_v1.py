from common_body_v1 import *

APPEND_METADATA=[ROOT/d/(TASK+'.md') for d in ['tasks','proof-obligations','conversion-windows']]

def accepted_fixed():
    integrated_fixed()
    final=load(RUN/'final-reader-receipt-v1.json')
    assert final['verdict'] in ['accepted','accepted-with-explicit-delta']
    assert final['inputs_unchanged'] and not final['required_blocking_repairs']
    assert final['report_sha256']==sha(RUN/'final-reader-review-v1.md')
    index=RUN/'FINAL-review-inputs-v1.json'
    inputs=load(index)['rows']
    checks={x['path']:x for x in final['raw_input_checks']}
    assert len(inputs)==final['fixed_input_count'] and set(checks)=={x['path'] for x in inputs}
    reviewed={x['path']:x['sha256'] for x in final['reviewed_files']}
    assert reviewed[index.as_posix()]==sha(index)
    assert final['permitted_future_metadata']==load(RUN/'FINAL-future-metadata-scope-v1.json')
    req=load(CONTRACT/'reader-requirements-v1.json')
    assert set(final['reader_requirement_verdicts'])==set(req)
    for k,v in req.items():
        r=final['reader_requirement_verdicts'][k]
        assert r['requirement']==v and r['verdict']=='satisfied'
    binding=RUN/'accepted-metadata-bindings-v1.json'
    bindings=load(binding)['rows'] if binding.exists() else []
    mutable={r['path']:r for r in bindings}
    for row in inputs:
        p=Path(row['path']);h=row['sha256'];c=checks[row['path']]
        assert c['unchanged'] and c['before_sha256']==c['after_sha256']==h
        if sha(p)==h:continue
        b=mutable[p.as_posix()]
        before=Path(b['snapshot']).read_bytes()
        assert hashlib.sha256(before).hexdigest()==h==b['original_sha256']
        assert sha(p)==b['current_sha256']
        if p==CONTRIBUTION:
            old=json.loads(before.decode('utf8'));now=load(p)
            assert [x['field'] for x in b['exact_six_fields']]==final['permitted_future_metadata']['manifest_fields']
            for x in b['exact_six_fields']:
                a,k=x['field'].split('.')
                assert old[a][k]==x['old'] and now[a][k]==x['new'];now[a][k]=x['old']
            assert now==old
        else:
            after=p.read_bytes();assert after.startswith(before)
            suffix=after[len(before):];assert hashlib.sha256(suffix).hexdigest()==b['suffix_sha256']
            if p in APPEND_METADATA:assert suffix.decode('utf8')==b['exact_owned_suffix']
            else:
                assert p==ROOT/'runs/lifecycle_sessions.jsonl'
                entries=[json.loads(s) for s in suffix.decode('utf8').splitlines() if s.strip()]
                assert entries==b['exact_owned_entries']
                assert all(x.get('task',x.get('session_id'))==TASK for x in entries)
    expected=load(RUN/'formula-render-v1.json')['images']
    actual=final['actual_pixel_review']
    assert len(actual)==len(expected)==12
    assert {x['path']:x['sha256'] for x in actual}=={x['path']:x['sha256'] for x in expected}
    assert all(x['actually_viewed'] and sha(x['path'])==x['sha256'] for x in actual)
    return final
