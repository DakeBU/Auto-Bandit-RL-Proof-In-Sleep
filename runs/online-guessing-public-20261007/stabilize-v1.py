from common_v1 import *
fixed()
decoder=load(RUN/'blind-decoder-receipt-v1.json')
assert decoder['actor']['task']=='/root/osd_blind' and decoder['input']['sha256_raw_bytes']==sha(RUN/'blind-packet-v1.md')
assert decoder['report']['sha256_raw_bytes']==sha(RUN/'blind-decoder-v1.md')
assert decoder['proposition_ids']==['Q%02d'%i for i in range(1,13)] and decoder['semantic_slots_per_proposition']==7
assert decoder['runtime_model_attested'] is False and decoder['requested_reasoning_effort']=='medium'
r=load(RUN/'source-contract-receipt-v1.json')
assert r['actor']['task']=='/root/source_reviewer' and r['verdict'] in ['accepted','accepted-with-explicit-delta']
assert sha(r['report'])==r['report_sha256']
for k in ['required_repairs','required_mathematical_repairs','required_metadata_repairs']:assert not r.get(k,[]),(k,r.get(k))
reviewed={x['path']:x['sha256'] for x in r['reviewed_files']}
for x in load(RUN/'source-contract-inputs-v1.json')['rows']:assert reviewed[x['path']]==x['sha256']==sha(x['path']),x['path']
write(RUN/'stabilized-decision-v1.json',dict(status=r['verdict'],source_report_sha256=r['report_sha256'],source_receipt_sha256=sha(RUN/'source-contract-receipt-v1.json'),all12_full_types_unchanged=True,existing_bodies_preexist=True,new_proofs=0,new_definitions=0,current_BODY_pending=True,chapter_complete=False,goal_complete=False))
native('stabilized-event-v1-01','lifecycle-event','--session',TASK,'--event','stabilized','--payload-json',json.dumps(dict(run_id=RUN.name,contract_version=1,source_contract_accepted=True,existing_bodies_preexist=True,new_proofs=0,chapter_complete=False,goal_complete=False)))
native('proving-event-v1-01','lifecycle-event','--session',TASK,'--event','proving','--payload-json',json.dumps(dict(run_id=RUN.name,route='Single lower existing-body/public-canary audit; dependencies ready',contract_version=1,new_proofs=0,chapter_complete=False,goal_complete=False)))
write(RUN/'30_lower_worker-v1.md','/root staged single lower reuse audit, not independent reviewer. Existing canonical12 public proof bodies/one loss definition and whole27canary proofs/6defs/one abbrev preexist this current draft and remain byte-frozen. Actual source/context CONTRACT accepted; focused, all47 named/kernel, twelve guards and actual proofVALUE dependency checks follow. No new proof count or mathematical terminal closure. BODY/combined/reader/FINAL/nativeaccepted/PR separate pending.')
fixed();gate('public-canary-focused-v1-01','lake','build','BanditRLProof.OnlineGuessingSubgradient','Tests.OnlineGuessingSubgradientCanary')
print('Source stabilized; twelve existing bodies/current whole-canary focused compilation passed.')
