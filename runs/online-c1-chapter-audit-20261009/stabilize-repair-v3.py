from common_v1 import *
fixed()
receipt=RUN/'source-contract-receipt-v3.json'
assert sha(receipt)=='264ef5d139323bdd0fa32048d3ea1299a2a6ed65610edb70f6c07b6848626da8'
r=load(receipt)
assert r['contract_verdict']==r['inventory_verdict']=='accepted-with-explicit-delta'
assert not r['required_blocking_repairs'] and not r['required_repairs']
assert sha(r['report'])==r['report_sha256']
assert sha(r['input_index'])==r['input_index_sha256']
indexed=load(r['input_index'])['rows']
assert len(indexed)==196
for row in indexed:assert sha(row['path'])==row['sha256'],row['path']
assert r['approved_future_exact_scope']==load(CONTRACT/'future-mutation-scope-draft-v3.json')
assert not (ROOT/'BanditRLProof/OnlineFTLInitializationRegret.lean').exists()
targets=load(CONTRACT/'general-initialization-targets-draft-v3.json')
targets['phase']='stabilized exact v3; proving G001 first'
for t in targets['new_targets']:t['phase']='stabilized; actual body pending'
targets['source_review']=dict(receipt=receipt.as_posix(),sha256=sha(receipt),verdict=r['verdict'])
write(CONTRACT/'general-initialization-targets-stabilized-v3.json',targets)
write(CONTRACT/'stabilization-decision-v3.json',dict(contract_verdict=r['verdict'],inventory_verdict=r['inventory_verdict'],receipt_sha256=sha(receipt),review_input_count_verified=196,review_inputs_raw_verified_before_native_append=True,source_audit_objects=17,new_required_source_objects=1,new_public_targets=4,first_dependency_ready_leaf='G001',fixed_old_targets=50,old_fifty_unchanged=True,proof_total=None,chapter_complete=False,goal_complete=False,semantic_roles='distinct reused automated actors; requested Astra/medium, no runtime/human/external/absolute-blind attestation',permitted_future_scope=r['approved_future_exact_scope']))
mutable=[RUN/'trials.jsonl',RUN/'own-artifact-journal.md',RUN/'lifecycle-sessions.jsonl',RUN/'lifecycle-state.json']
mutable += [ROOT/folder/(TASK+'.md') for folder in ['tasks','conversion-windows','proof-obligations']]
snapshots=[]
for n,p in enumerate(mutable):
    before=RUN/'snapshots'/('before-stabilized-v3-%02d.raw'%n)
    write(before,p.read_bytes())
    snapshots.append(dict(path=p.as_posix(),before=before.as_posix(),before_sha256=sha(before)))
def native(label,*args):return gate(label,sys.executable,'-B','-X','utf8',RUN/'native-scoped-v1.py',*args)
native('stabilized-native-contract-v3','lifecycle-event','--session',TASK,'--event','stabilized','--payload-json',json.dumps(dict(contract=sha(CONTRACT/'general-initialization-targets-stabilized-v3.json'),review_receipt=sha(receipt),source_objects=17,proof_total=None,frozen_new_targets=4,first_leaf='G001',chapter_complete=False,goal_complete=False)))
native('stabilized-native-review-v3','trial-log','--task',TASK,'--role','reviewer','--kind','review','--status','accepted','--run-id',RUN.name,'--attempt-id','C1-CONTRACT-REPAIR-V3','--progress-class','diagnostic','--notes','Distinct CONTRACT/INVENTORY stabilization only; 196 RAW inputs verified. Required any-initial finite1+tail and upper family appended as17th source object. Four actual proofs and whole chapter gates pending.','--verifier-evidence',str(receipt),'--verifier-evidence',str(RUN/'source-contract-review-v3.md'))
native('proving-native-G001-v3','lifecycle-event','--session',TASK,'--event','proving','--payload-json',json.dumps(dict(leaf='G001',terminal_hash=targets['new_targets'][0]['statement_hash'],owning_module=targets['owning_public_path'],approved_scope=sha(CONTRACT/'future-mutation-scope-draft-v3.json'),ready_dependencies='same actual predictor/half, range-succ and identical comparator infimum; no performance oracle',chapter_complete=False,goal_complete=False)))
append=('\n\n## Stabilized v3 / first proving leaf\n\nDistinct source CONTRACT/INVENTORY receipt '+sha(receipt)+' accepted-with-explicit-delta, stabilization only. Original16 source rows remain immutable;17th any-initial performance source object adds four exact frozen terminals, proof total null. G001 positive-horizon actual first-loss correction is dependency ready; G002 exact1+tail, G003 upper-epsilon and G004 TRUE-best average-zero remain unproved. This changes the prior draft status without erasing v1 rejection/v2 loose proposal. Source report R1-R10, BODY, separately roundtripped chapter canaries, shared root/Tests/full harness, two-base nonempty contributor/shadow/registry/site/FINAL/native/delivery all mandatory. Old50 math, global frontiers and all historical evidence unchanged. Whole1-16 Goal ACTIVE, no chapter acceptance/merge/deploy.\n').encode('utf8')
for p in mutable[4:]:p.write_bytes(p.read_bytes()+append)
for row in snapshots:row['after_sha256']=sha(row['path'])
write(RUN/'stabilized-own-mutation-receipt-v3.json',dict(approved_scope_sha256=sha(CONTRACT/'future-mutation-scope-draft-v3.json'),source_receipt_sha256=sha(receipt),before_bindings=snapshots,actual_native_commands=3,all_actual_exit_zero=True,only_OWN_native_task_files_changed=True,phase='stabilized/proving; no new proof yet',chapter_complete=False,goal_complete=False))
fixed()
print('196 RAW verified; v3 exact contract stabilized and G001 selected; OWN native appends preserved.',flush=True)
