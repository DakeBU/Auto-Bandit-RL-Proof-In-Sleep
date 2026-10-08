from common_accepted_v4 import *

def delivery_fixed():
    accepted_fixed()
    r=reviewer_receipt('delivery-reader-receipt-v5.json')
    assert r.get('before_after_raw_hashes_match')
    inputs=load(RUN/'delivery-reader-inputs-v5.json')
    assert inputs['fixed_input_count'] == r['fixed_input_count'] == 64
    reviewed={x['path']:x.get('sha256',x.get('sha256_raw_bytes')) for x in r['reviewed_files']}
    for row in inputs['rows']:
        assert reviewed[row['path']] == row['sha256'] == sha(row['path']),row['path']
    return r
