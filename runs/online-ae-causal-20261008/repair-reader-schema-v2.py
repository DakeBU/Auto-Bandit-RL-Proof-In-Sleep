from common_body_v1 import *
fixed_integrated()
assert load(RUN/'site-build-v1-exit.json')['actual_exit']==1
old=load(RUN/'reader-proposal-v1.json')
new=json.loads(json.dumps(old))
assert new['card']['local_status']['declarations']==[t['name'] for t in load(CONTRACT/'targets-v1.json')['targets']]
del new['card']['local_status']['declarations']
assert set(new['card']['local_status'])=={'status','label','boundary'}
write(RUN/'reader-proposal-v2.json',new)
p=ROOT/'website/content/readings.json'
write(RUN/'snapshots/readings-before-schema-repair-v1.raw',p.read_bytes())
d=load(p);row=next(x for x in d['readings'] if x['slug']==ROUTE)
assert row['source_theorems'][-1]==old['card']
row['source_theorems'][-1]=new['card']
p.write_bytes((json.dumps(d,ensure_ascii=False,indent=2)+'\n').encode('utf8'))
b=load(RUN/'reader-integration-bindings-v1.json')
b['reader_proposal_sha256']=sha(RUN/'reader-proposal-v2.json')
b['reader_proposal_version']=2
write(RUN/'reader-integration-bindings-v2.json',b)
write(RUN/'reader-schema-repair-v2.json',dict(actual_failed_site_receipt='site-build-v1-exit.json',
    actual_error='Own local_status contained an unsupported declarations key. Builder requires exactly status/label/boundary.',
    exact_delta='Remove only own card.local_status.declarations; three actual declaration notes and shared registry targets unchanged.',
    before_snapshot='snapshots/readings-before-schema-repair-v1.raw',before_sha256=sha(RUN/'snapshots/readings-before-schema-repair-v1.raw'),
    current_readings_sha256=sha(p),old_proposal_sha256=sha(RUN/'reader-proposal-v1.json'),new_proposal_sha256=sha(RUN/'reader-proposal-v2.json'),
    mathematical_text_or_public_header_or_proof_change=False,combined_Lean_gate_remains_applicable=True))
print('Actual source-card schema repaired only; mathematical statements/proofs unchanged.',flush=True)
