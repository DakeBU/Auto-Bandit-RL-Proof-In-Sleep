from publication_guard_v1 import *
fixed()
oldmeta=load(RUN/'pre-stabilization-exact-own-metadata-v1.json')
snapshots={row['path']:row for row in oldmeta['rows']}
plans={row['path']:row for row in load(CONTRACT/'exact-publication-plan-v2.json')['rows']}
results=[]
for manifest in ['contract-review-inputs-v1.json','BODY-canary-contract-review-inputs-v1.json','canary-BODY-publication-review-inputs-v2.json']:
    unchanged=0;changed=[]
    for row in load(RUN/manifest)['rows']:
        actual=sha(row['path'])
        if actual==row['sha256']:unchanged+=1;continue
        if row['path'] in snapshots:
            before=snapshots[row['path']]
            assert before['sha256']==row['sha256']
            raw=base64.b64decode(before['raw_base64'])
            assert hashlib.sha256(raw).hexdigest()==row['sha256']
            resolution=dict(snapshot='pre-stabilization-exact-own-metadata-v1.json',raw_entry=row['path'],kind='Explicit OWN draft-to-stabilized/proving metadata only')
        elif row['path'] in plans:
            before=plans[row['path']]
            assert sha(before['before_snapshot'])==row['sha256']==before['before_sha256']
            assert actual==before['after_sha256']
            resolution=dict(snapshot=before['before_snapshot'],kind='Exact distinct-reviewed5path materialization')
        else:raise AssertionError(('Unexplained historical binding change',manifest,row))
        changed.append(dict(path=row['path'],historical_sha256=row['sha256'],current_sha256=actual,resolution=resolution))
    results.append(dict(manifest=manifest,manifest_sha256=sha(RUN/manifest),unchanged_current_RAW_inputs=unchanged,explicit_historical_resolutions=changed))
write(RUN/'historical-binding-resolution-v1.json',dict(rows=results,all_other_historical_inputs_current_unchanged=True,scope='Historical stage fingerprints resolve through exact immutable snapshots; no false unchanged-live assertion.',source_container_closed=False,chapter_complete=False,whole_Goal_status='ACTIVE'))
fixed()
print('Historical source/statement/RAW stage bindings resolved without rewriting originals.')
