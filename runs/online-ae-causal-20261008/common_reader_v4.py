from common_body_v1 import *

def fixed_integrated():
    body_fixed(True)
    for rel,addition in [('BanditRLProof.lean',b'\nimport BanditRLProof.OnlineGuessingAECausal\n'),
        ('Tests.lean',b'\nimport Tests.OnlineGuessingAECausalCanary\n')]:assert (ROOT/rel).read_bytes()==baseline(rel)+addition
    proposal=load(RUN/'reader-proposal-v3.json')
    original=load(RUN/'reader-proposal-v1.json')
    expected=json.loads(json.dumps(original))
    del expected['card']['local_status']['declarations']
    for i in [0,1]:
        n=expected['notes'][i]
        external=[x for x in n['dependencies'] if not x.startswith('BanditRL.')]
        n['dependencies']=[x for x in n['dependencies'] if x.startswith('BanditRL.')]
        if i==0:n['dependencies']=['BanditRL.OnlineLearning.privateSeedPastInformation']
        n['lean_notes']+=' Actual pinned mathlib proof APIs: '+', '.join(external)+'. These names are in the compiled VALUE audit; the reader dependency links use the existing ABRL registry.'
    assert proposal==expected
    assert sha(RUN/'reader-proposal-v3.json')==load(RUN/'reader-integration-bindings-v3.json')['reader_proposal_sha256']
    for label in ['readings','highlights','chapters']:
        old=json.loads(baseline('website/content/'+label+'.json').decode('utf8'))
        new=load(ROOT/'website/content'/(label+'.json'))
        assert set(old)==set(new)
        assert {k:v for k,v in old.items() if k!=label}=={k:v for k,v in new.items() if k!=label}
        if label=='highlights':assert new[label]==old[label]+proposal['notes']
        else:
            assert len(old[label])==len(new[label])
            for a,b in zip(old[label],new[label]):
                if a['slug']!=ROUTE:assert a==b
                elif label=='readings':
                    assert {k:v for k,v in a.items() if k!='source_theorems'}=={k:v for k,v in b.items() if k!='source_theorems'}
                    assert b['source_theorems']==a['source_theorems']+[proposal['card']]
                else:
                    assert {k:v for k,v in a.items() if k not in ['completion_blockers','open_gaps','module_globs']}=={k:v for k,v in b.items() if k not in ['completion_blockers','open_gaps','module_globs']}
                    assert b['module_globs']==a['module_globs']+[PUBLIC.relative_to(ROOT).as_posix()]
                    for k in ['completion_blockers','open_gaps']:assert b[k]==a[k]+[proposal['boundary']]
    assert load(MANIFEST)['id']==TASK
    assert load(MANIFEST)['declarations']==[t['name'] for t in load(CONTRACT/'targets-v1.json')['targets']]
    assert load(MANIFEST)['affected_files']==[PUBLIC.relative_to(ROOT).as_posix(),'BanditRLProof.lean']+[p.relative_to(ROOT).as_posix() for p in READERS]
    return True
