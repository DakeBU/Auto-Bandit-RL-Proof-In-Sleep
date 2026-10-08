from common_proving_v1 import *
READERS=[ROOT/'website/content'/(name+'.json') for name in ['readings','highlights','chapters']]
CONTRIBUTION=ROOT/'research-wiki/contribution-contracts/online-ftl-obstruction-20261009.json'
SITE=ROOT/'tmp/online-ftl-obstruction-site-v1'

def verify_reader_delta():
    proposal=load(RUN/'reader-proposal-v1.json')
    for row in load(RUN/'integration-baseline-v1.json')['rows']:
        if row['path'] not in [p.relative_to(ROOT).as_posix() for p in READERS]:continue
        old=Path(row['snapshot']).read_bytes();assert hashlib.sha256(old).hexdigest()==row['sha256']
        before,now=json.loads(old.decode('utf8')),load(ROOT/row['path']);label=Path(row['path']).stem
        if label=='highlights':
            assert now[label]==before[label]+proposal['notes'];now[label]=before[label]
        else:
            oldrow=next(x for x in before[label] if x['slug']=='online-foundations')
            newrow=next(x for x in now[label] if x['slug']=='online-foundations')
            if label=='readings':
                assert newrow['source_theorems']==oldrow['source_theorems']+[proposal['card']]
                newrow['source_theorems']=oldrow['source_theorems']
            else:
                for k in ['open_gaps','completion_blockers']:
                    assert newrow[k]==oldrow[k]+[proposal['boundary']];newrow[k]=oldrow[k]
                assert newrow['module_globs']==oldrow['module_globs']+[PUBLIC.relative_to(ROOT).as_posix()]
                newrow['module_globs']=oldrow['module_globs']
        assert now==before,row['path']

def checked_current_row(row,integrated,scope):
    p=Path(row['path']);p=p if p.is_absolute() else ROOT/p
    rel=p.resolve().relative_to(ROOT.resolve()).as_posix() if ROOT.resolve() in p.resolve().parents else None
    if integrated and rel in scope['exact_root_additions']:
        br=next(x for x in load(RUN/'integration-baseline-v1.json')['rows'] if x['path']==rel)
        old=Path(br['snapshot']).read_bytes()
        assert hashlib.sha256(old).hexdigest()==row['sha256']==br['sha256']
        assert p.read_bytes()==old+scope['exact_root_additions'][rel].encode('utf8')
    elif integrated and rel in scope['reader_files']:
        br=next(x for x in load(RUN/'integration-baseline-v1.json')['rows'] if x['path']==rel)
        assert br['sha256']==row['sha256'];verify_reader_delta()
    elif rel in [d+'/'+TASK+'.md' for d in ['tasks','proof-obligations','conversion-windows']]:
        snapshots=load(RUN/'stabilized-contract-v1.json')['snapshots']
        br=next(x for x in snapshots if Path(x['path']).resolve()==p.resolve())
        old=Path(br['snapshot']).read_bytes()
        assert hashlib.sha256(old).hexdigest()==row['sha256']
        assert p.read_bytes().startswith(old)
    else:assert sha(p)==row['sha256'],row['path']

def body_fixed(integrated=False):
    assert Path.cwd()==ROOT and sha(PDF)==PDF_SHA
    assert subprocess.check_output(['git','branch','--show-current'],encoding='utf8').strip()==BRANCH
    r=load(RUN/'public-body-receipt-v1.json');scope=load(RUN/'body-future-integration-scope-v1.json')
    assert r['verdict'] in ['accepted','accepted-with-explicit-delta']
    assert r['inputs_unchanged'] and not r['required_blocking_repairs']
    assert r['report_sha256']==sha(RUN/'public-body-review-v1.md')
    assert r['approved_future_exact_scope']==scope
    assert r['required_reader_corrections']==load(CONTRACT/'reader-requirements-v1.json')
    owninputs=load(RUN/'body-review-inputs-v1.json')['rows'];checks={x['path']:x for x in r['raw_input_checks']}
    assert len(owninputs)==r['fixed_input_count'] and set(checks)=={x['path'] for x in owninputs}
    for row in owninputs:
        c=checks[row['path']];assert c['unchanged'] and c['before_sha256']==c['after_sha256']==row['sha256']
        checked_current_row(row,integrated,scope)
    for row in load(RUN/'baseline-v2.json')['rows']:checked_current_row(row,integrated,scope)
    for row in load(RUN/'source-contract-review-inputs-v1.json')['rows']:checked_current_row(row,integrated,scope)
    for row in load(RUN/'canary-contract-review-inputs-v1.json')['rows']:checked_current_row(row,integrated,scope)
    audit=load(RUN/'compiled-audit-v1.json')
    assert sha(PUBLIC)==audit['public_sha256'] and sha(CANARY)==audit['canary_sha256']
    for file,targets in [(PUBLIC,load(CONTRACT/'targets-v1.json')['targets']),(CANARY,load(CONTRACT/'canary-targets-v1.json')['targets'])]:
        for t in targets:assert statement_hash(lean_declaration_header(file,t['name']))==t['statement_hash']
    if integrated:
        verify_reader_delta()
        for row in load(RUN/'integration-baseline-v1.json')['rows']:checked_current_row(row,True,scope)
    return r

def integrated_fixed():return body_fixed(integrated=True)
