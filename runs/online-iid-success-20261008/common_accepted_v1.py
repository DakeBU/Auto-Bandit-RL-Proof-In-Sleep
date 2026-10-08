from common_integrated_v2 import *

SIX_FIELDS=[('semantic_roundtrip','remaining_semantic_delta'),('graph_contribution','visual_review')]+[
    ('verification',k) for k in ['independent_review','bandit_check','site_build','site_check']]

def accepted_fixed():
    headers_fixed(4)
    assert sha(RUN/'public-body-receipt-v1.json') == BODY_SHA
    assert sha(RUN/'public-body-review-v1.md') == BODY_REPORT_SHA
    b=load(RUN/'body-bindings-v1.json')
    assert sha(PUBLIC)==b['public_sha256'] and sha(CANARY)==b['canary_sha256']
    receipt=load(RUN/'final-reader-receipt-v1.json')
    assert receipt['actor']['task']=='/root/source_reviewer'
    assert receipt['verdict'] in ['accepted','accepted-with-explicit-delta']
    assert receipt['inputs_unchanged'] and receipt['before_after_raw_hashes_match']
    assert sha(receipt['report'])==receipt['report_sha256']
    for k in ['required_repairs','required_mathematical_repairs','required_metadata_repairs','required_blocking_reader_repairs']:
        assert not receipt[k],k
    requirements=load(RUN/'stabilized-contract-v1.json')['reader_requirements']
    assert set(receipt['reader_requirement_verdicts'])==set(requirements)
    for k,text in requirements.items():
        v=receipt['reader_requirement_verdicts'][k]
        assert v['requirement']==text and v['verdict']=='satisfied',k
    index=load(RUN/'FINAL-review-inputs-v1.json')
    assert receipt['fixed_input_count']==index['fixed_input_count']==len(index['rows'])
    reviewed={Path(x['path']).resolve().as_posix():x.get('sha256',x.get('sha256_raw_bytes')) for x in receipt['reviewed_files']}
    resolutions={x['live_path']:x for x in load(RUN/'FINAL-metadata-snapshots-v1.json')}
    bindings_path=RUN/'accepted-metadata-bindings-v1.json'
    bindings={x['path']:x for x in load(bindings_path)['rows']} if bindings_path.exists() else {}
    for row in index['rows']:
        p=Path(row['path']);key=p.resolve().as_posix()
        assert reviewed[key]==row['sha256'],p
        if sha(p)==row['sha256']: continue
        resolution=resolutions[key]
        original_bytes=Path(resolution['snapshot']).read_bytes()
        assert sha(resolution['snapshot'])==row['sha256']==resolution['sha256']
        # Every permitted mutation needs an exact newly versioned byte binding, not prefix-only admission.
        binding=bindings[key]
        assert binding['original_sha256']==row['sha256'] and sha(p)==binding['current_sha256'],p
        if p.resolve()==MANIFEST.resolve():
            old=json.loads(original_bytes.decode('utf8'));now=load(p)
            for top,k in SIX_FIELDS: now[top][k]=old[top][k]
            assert now==old,'Only six reviewed metadata fields may change'
        else:
            assert p.read_bytes().startswith(original_bytes)
            suffix=p.read_bytes()[len(original_bytes):]
            assert hashlib.sha256(suffix).hexdigest()==binding['suffix_sha256']
            if p in APPEND_METADATA or p.resolve() in {x.resolve() for x in APPEND_METADATA}:
                assert suffix.decode('utf8')==binding['exact_owned_suffix']
                assert TASK in suffix.decode('utf8')
            elif p.suffix=='.jsonl':
                entries=[json.loads(s) for s in suffix.decode('utf8').splitlines() if s.strip()]
                assert all(x.get('task',x.get('session_id'))==TASK for x in entries)
                assert entries==binding['exact_owned_entries']
            else: assert p.name=='MANIFEST.md' and not suffix
    proposal=load(RUN/'proposed-publication-v1.json')
    for k in ['title','body']: assert sha(proposal[k+'_path'])==proposal[k+'_sha256']
    for row in load(RUN/'formula-render-v1.json')['images']:
        assert sha(row['path'])==row['sha256']==reviewed[Path(row['path']).resolve().as_posix()]
    assert receipt['permitted_future_metadata']
    if not bindings_path.exists(): fixed_integrated()
    return receipt
