from common_v1 import *
fixed()
r=load(RUN/'source-contract-receipt-v1.json')
assert r['verdict'] in ['accepted','accepted-with-explicit-delta']
assert r['inputs_unchanged'] and not r['required_blocking_repairs']
assert r['report_sha256']==sha(RUN/'source-contract-review-v1.md')
inputs=load(RUN/'source-contract-review-inputs-v1.json')['rows']
checks={x['path']:x for x in r['raw_input_checks']}
assert len(inputs)==r['fixed_input_count']==189 and set(checks)=={x['path'] for x in inputs}
for row in inputs:
    c=checks[row['path']]
    assert c['unchanged'] and c['before_sha256']==c['after_sha256']==row['sha256']==sha(row['path'])
assert r['permitted_future_proof_scope']==load(RUN/'contract-mutable-scope-v1.json')
assert r['required_reader_corrections']==load(CONTRACT/'reader-requirements-v1.json')
snapshots=[]
for rel in r['permitted_future_proof_scope']['own_task_append_only']:
    p=ROOT/rel;q=RUN/'snapshots'/('reviewed-'+p.parent.name+'-v1.raw')
    write(q,p.read_bytes());snapshots.append(dict(path=p.as_posix(),snapshot=q.as_posix(),sha256=sha(p)))
write(RUN/'stabilized-contract-v1.json',dict(version=1,targets=load(CONTRACT/'targets-v1.json')['targets'],
    receipt_sha256=sha(RUN/'source-contract-receipt-v1.json'),report_sha256=sha(RUN/'source-contract-review-v1.md'),
    headers_sha256=sha(CONTRACT/'targets-v1.lean.txt'),context_sha256=sha(CONTRACT/'context-v1.lean.txt'),
    source_intent_sha256=sha(CONTRACT/'source-intent-v1.md'),snapshots=snapshots,scope=r['permitted_future_proof_scope'],
    contract_accepted=True,body_accepted=False,new_bodies_compiled=0,chapter_complete=False,goal_complete=False))
native('stabilized-lifecycle-v1','lifecycle-event','--session',TASK,'--event','stabilized','--payload-json',
    json.dumps(dict(run_id=RUN.name,contract_version=1,contract_receipt_sha256=sha(RUN/'source-contract-receipt-v1.json'),obligations=4,compiled=0,chapter_complete=False,goal_complete=False)))
native('proving-D1-lifecycle-v1','lifecycle-event','--session',TASK,'--event','proving','--payload-json',
    json.dumps(dict(run_id=RUN.name,leaf='D1',dependency_ready=True,
        statement_hash=load(CONTRACT/'targets-v1.json')['targets'][0]['statement_hash'],allowed_file=PUBLIC.relative_to(ROOT).as_posix(),terminal_edit_allowed=False,single_lower_route=True)))
write(RUN/'proving-D1-v1.json',dict(leaf='D1',actual_dependency_ready=True,
    retrieved_dependencies=['meanPredict_fixedRegret_limit_iff','meanPredict_limitNoRegret_of_mean_converges','empiricalMean_mem'],
    route='Actual comparator0/1 squared-distance limits reconstruct one mean limit; conditional producer proves sufficiency.',
    lower_count=1,allowed_file=PUBLIC.relative_to(ROOT).as_posix(),terminal_edit_allowed=False,new_compiled=False))
print('Reviewed four targets stabilized; dependency-ready D1 selected.',flush=True)
