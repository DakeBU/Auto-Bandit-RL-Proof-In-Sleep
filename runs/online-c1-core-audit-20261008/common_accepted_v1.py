from commit_owned_v1 import *

def accepted_fixed():
    fixed_integrated()
    final=load(RUN/'final-reader-receipt-v1.json')
    assert final['verdict'] in ['accepted','accepted-with-explicit-delta']
    assert final['inputs_unchanged'] and final['before_after_raw_hashes_match']
    assert final['fixed_input_count']==419
    assert not final['required_blocking_repairs']
    requirements=load(CONTRACT/'reader-requirements-v1.json')
    assert set(final['reader_requirement_verdicts'])==set(requirements)
    for key,text in requirements.items():
        v=final['reader_requirement_verdicts'][key]
        assert v['requirement']==text and v['verdict']=='satisfied',key
    assert final['permitted_future_metadata']==load(RUN/'FINAL-future-metadata-scope-v1.json')
    reviewed={r['path']:r['sha256'] for r in final['reviewed_files']}
    assert reviewed[str((RUN/'FINAL-review-inputs-v1.json').resolve()).replace('\\','/')]==sha(RUN/'FINAL-review-inputs-v1.json')
    assert final['report_sha256']==sha(RUN/'final-reader-review-v1.md')
    original={r['live_path']:r for r in load(RUN/'FINAL-metadata-snapshots-v1.json')}
    bindings=load(RUN/'accepted-metadata-bindings-v1.json') if (RUN/'accepted-metadata-bindings-v1.json').exists() else None
    now={r['path']:r for r in bindings['rows']} if bindings else {}
    for r in load(RUN/'FINAL-review-inputs-v1.json')['rows']:
        if sha(r['path'])==r['sha256']:continue
        assert r['path'] in original and r['path'] in now,r['path']
        assert sha(original[r['path']]['snapshot'])==r['sha256']
        assert sha(r['path'])==now[r['path']]['current_sha256']
    images=final['actual_original_pixel_reviews']
    assert len(images)==26 and all(r['actually_viewed'] and sha(r['path'])==r['sha256'] for r in images)
    if bindings:
        assert bindings['exact_owned_suffixes'] and bindings['original_source16_unchanged']
        assert bindings['required_proof_total_null'] and bindings['globalSGB_unchanged']
    return final
