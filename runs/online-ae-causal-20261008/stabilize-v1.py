from common_v1 import *
baseline_fixed(mutable=['MANIFEST.md','runs/lifecycle_sessions.jsonl'])
receipt=load(RUN/'source-contract-receipt-v1.json')
assert sha(RUN/'source-contract-receipt-v1.json')=='867a15110f9584827546d2a62292fd3e19a3f58eb63312cacc0481810c50892a'
assert receipt['verdict']=='accepted-with-explicit-delta' and receipt['inputs_unchanged']
assert not receipt['required_blocking_repairs']
assert receipt['report_sha256']==sha(RUN/'source-contract-review-v1.md')
assert receipt['approved_future_exact_scope']==load(CONTRACT/'future-proof-edit-scope-v1.json')
index=load(RUN/'source-contract-review-inputs-v1.json')
mutable={'MANIFEST.md','runs/lifecycle_sessions.jsonl','runs/trials.jsonl'}
mutable.update(d+'/'+TASK+'.md' for d in ['tasks','proof-obligations','proof-blueprints','conversion-windows'])
snapshots=[]
for row in index['rows']:
    assert sha(row['path'])==row['sha256']
    rel=Path(row['path']).resolve().relative_to(ROOT).as_posix()
    if rel in mutable:
        p=RUN/'snapshots'/('contract-mutable-'+str(len(snapshots))+'.raw')
        write(p,Path(row['path']).read_bytes())
        snapshots.append(dict(path=row['path'],original_sha256=row['sha256'],snapshot=p.as_posix()))
targets=load(CONTRACT/'targets-v1.json')['targets']
write(RUN/'stabilized-contract-v1.json',dict(source_sha256=PDF_SHA,
    receipt_sha256=sha(RUN/'source-contract-receipt-v1.json'),report_sha256=sha(RUN/'source-contract-review-v1.md'),
    targets_sha256=sha(CONTRACT/'targets-v1.json'),headers_sha256=sha(CONTRACT/'targets-v1.lean.txt'),
    source_intent_sha256=sha(CONTRACT/'source-intent-v1.md'),targets=targets,
    approved_scope=receipt['approved_future_exact_scope'],mutable_reviewed_snapshots=snapshots,
    approved_contract_only=True,proof_bodies_compiled=0,chapter_complete=False,goal_complete=False))
native('lifecycle-stabilized-v1','lifecycle-event','--session',TASK,'--event','stabilized',
    '--payload-json',json.dumps(dict(run_id=RUN.name,contract_version=1,
        source_sha256=PDF_SHA,target_statement_hashes=[t['statement_hash'] for t in targets],
        source_contract_receipt_sha256=sha(RUN/'source-contract-receipt-v1.json'),obligations=3,compiled=0,
        source_delta=receipt['source_delta'],chapter_complete=False,goal_complete=False)))
write(RUN/'proving-leaf-L1-v1.json',dict(id='L1',terminal_name=targets[0]['name'],
    statement_hash=targets[0]['statement_hash'],dependency_ready=True,route='representative -> comap factorization -> projIcc -> all-time AE',
    public_edit_scope=PUBLIC.relative_to(ROOT).as_posix(),phase='proving',actual_theorem_body_compiled=False,
    L2='ready, not selected until L1 focused build',L3='awaits actual L2 focused build'))
native('lifecycle-proving-L1-v1','lifecycle-event','--session',TASK,'--event','proving',
    '--payload-json',json.dumps(dict(run_id=RUN.name,selected_leaf='L1',statement_hash=targets[0]['statement_hash'],
        permitted_file=PUBLIC.relative_to(ROOT).as_posix(),single_lower_route=True,terminal_type_edits=False,compiled=0)))
print('Reviewed contract stabilized; one ready L1 selected; no proof yet')
