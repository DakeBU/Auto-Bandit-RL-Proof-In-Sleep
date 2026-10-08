from common_canary_v1 import *
READERS=[ROOT/'website/content'/(name+'.json') for name in ['readings','highlights','chapters']]
CONTRIBUTION=ROOT/'research-wiki/contribution-contracts/online-ftl-limit-20261009.json'
SITE=ROOT/'tmp/online-ftl-limit-site-v1'

def body_fixed():
    canary_contract_fixed()
    r=load(RUN/'public-body-receipt-v1.json')
    assert r['verdict'] in ['accepted','accepted-with-explicit-delta']
    assert r['inputs_unchanged'] and not r['required_blocking_repairs']
    assert r['report_sha256']==sha(RUN/'public-body-review-v1.md')
    original=load(RUN/'body-review-inputs-v1.json')['rows']
    checks={x['path']:x for x in r['raw_input_checks']}
    assert len(original)==r['fixed_input_count']==287 and set(checks)=={x['path'] for x in original}
    mutable={x['path']:x for x in load(RUN/'stabilized-contract-v1.json')['snapshots']}
    for row in original:
        c=checks[row['path']]
        assert c['unchanged'] and c['before_sha256']==c['after_sha256']==row['sha256']
        if row['path'] in mutable:
            before=Path(mutable[row['path']]['snapshot']).read_bytes()
            assert hashlib.sha256(before).hexdigest()==row['sha256']
            assert Path(row['path']).read_bytes().startswith(before)
        else:
            assert sha(row['path'])==row['sha256'],row['path']
    assert r['approved_future_exact_scope']==load(RUN/'body-future-integration-scope-v1.json')
    assert r['required_reader_corrections']==load(CONTRACT/'reader-requirements-v1.json')
    audit=load(RUN/'compiled-audit-v1.json')
    assert sha(PUBLIC)==audit['public_sha256'] and sha(CANARY)==audit['canary_sha256']
    return r

def integrated_fixed():
    r=body_fixed()
    proposal=load(RUN/'reader-proposal-v1.json')
    names=[t['name'] for t in load(CONTRACT/'targets-v1.json')['targets']]
    baselines=load(RUN/'integration-baseline-v1.json')['rows']
    for row in baselines:
        old=Path(row['snapshot']).read_bytes()
        assert hashlib.sha256(old).hexdigest()==row['sha256']
        current=(ROOT/row['path']).read_bytes()
        additions=r['approved_future_exact_scope']['exact_root_additions']
        if row['path'] in additions:
            assert current==old+additions[row['path']].encode('utf8')
        elif row['path'].startswith('website/content/'):
            before,now=json.loads(old.decode('utf8')),json.loads(current.decode('utf8'))
            label=Path(row['path']).stem
            if label=='highlights':
                assert now[label]==before[label]+proposal['notes']
                now[label]=before[label]
            else:
                oldrow=next(x for x in before[label] if x['slug']=='online-foundations')
                newrow=next(x for x in now[label] if x['slug']=='online-foundations')
                if label=='readings':
                    assert newrow['source_theorems']==oldrow['source_theorems']+[proposal['card']]
                    newrow['source_theorems']=oldrow['source_theorems']
                else:
                    for k in ['open_gaps','completion_blockers']:
                        assert newrow[k]==oldrow[k]+[proposal['boundary']]
                        newrow[k]=oldrow[k]
                    assert newrow['module_globs']==oldrow['module_globs']+[PUBLIC.relative_to(ROOT).as_posix()]
                    newrow['module_globs']=oldrow['module_globs']
            assert now==before,row['path']
        else:
            assert current==old,row['path']
    return r
