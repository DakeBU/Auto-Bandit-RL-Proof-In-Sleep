from common_proving_v2 import *
fixed()
receipt=RUN/'chapter-canary-CONTRACT-receipt-v1.json'
assert sha(receipt)=='e73ce0ddabcb71aff166ad5f381204b7d7b17b078af704830681f48354adbd0c'
r=load(receipt);assert r['verdict']=='accepted-with-explicit-delta' and not r['required_blocking_repairs']
assert sha(r['report'])==r['report_sha256'] and sha(r['input_index'])==r['input_index_sha256']
for row in load(r['input_index'])['rows']:assert sha(row['path'])==row['sha256'],row['path']
draft=load(CONTRACT/'chapter-canary-targets-draft-v1.json')
scope=r['permitted_future_canary_scope']
assert scope['exact_setup']==draft['setup']
assert [(t['id'],t['header'],t['statement_hash']) for t in scope['exact_headers']]==[(t['id'],t['header'],t['statement_hash']) for t in draft['targets']]
assert not (ROOT/'Tests/OnlineLearningChapterAuditCanary.lean').exists()
draft['phase']='stabilized exact27 Test headers,2probe definitions; proving'
for t in draft['targets']:t['phase']='stabilized; actual canary body pending'
draft['contract_receipt_sha256']=sha(receipt)
write(CONTRACT/'chapter-canary-targets-stabilized-v1.json',draft)
mutable=[RUN/'trials.jsonl',RUN/'own-artifact-journal.md',RUN/'lifecycle-sessions.jsonl',RUN/'lifecycle-state.json']
snaps=[]
for n,p in enumerate(mutable):
    s=RUN/'snapshots'/('before-canary-stabilized-v1-%02d.raw'%n);write(s,p.read_bytes())
    snaps.append(dict(path=p.as_posix(),before=s.as_posix(),before_sha256=sha(s)))
def native(label,*args):return gate(label,sys.executable,'-B','-X','utf8',RUN/'native-scoped-v1.py',*args)
native('canary-stabilized-native-v1','lifecycle-event','--session',TASK,'--event','stabilized','--payload-json',json.dumps(dict(scope='27exactcanarytypes/2testprobes only',contract=sha(CONTRACT/'chapter-canary-targets-stabilized-v1.json'),source_review=sha(receipt),phase='Test proving; canonical4module unchanged',chapter_complete=False,goal_complete=False)))
native('canary-contract-native-review-v1','trial-log','--task',TASK,'--role','reviewer','--kind','review','--status','accepted','--run-id',RUN.name,'--attempt-id','C1-CANARY-CONTRACT-V1','--progress-class','diagnostic','--notes','Distinct source CANARY CONTRACT accepted-with-explicit-delta,372RAW verified. Exact27types/2probes stabilized; no actualcanaryproof orchapteracceptance.','--verifier-evidence',str(receipt),'--verifier-evidence',str(RUN/'chapter-canary-CONTRACT-review-v1.md'))
native('canary-proving-native-v1','lifecycle-event','--session',TASK,'--event','proving','--payload-json',json.dumps(dict(leaf='C1-CHAPTER-CANARIES',ready='public54types/values, fourBODYreviewedactualproducers and oldpublicTest instantiations',frozen27=sha(CONTRACT/'chapter-canary-targets-stabilized-v1.json'),Test_import_pending_BODY=True,chapter_complete=False,goal_complete=False)))
for row in snaps:row['after_sha256']=sha(row['path'])
write(RUN/'canary-stabilized-own-mutation-receipt-v1.json',dict(before_bindings=snaps,source_receipt_sha256=sha(receipt),actual_native_commands=3,all_actual_exit_zero=True,current_raw_inputs_verified_before_OWNappend=372,chapter_complete=False,goal_complete=False))
fixed()
print('372RAW verified;27canarytypes stabilized and actual body phase selected under exact scope.',flush=True)
