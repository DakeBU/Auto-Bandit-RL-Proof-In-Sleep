from common_v1 import *
fixed();d=load(RUN/'blind-decoder-receipt-v1.json');assert d['actor']['task']=='/root/osd_blind' and d['input']['sha256_raw_bytes']==sha(RUN/'blind-packet-v1.md') and d['report']['sha256_raw_bytes']==sha(RUN/'blind-decoder-v1.md')
r=load(RUN/'source-contract-receipt-v1.json');assert r['actor']['task']=='/root/source_reviewer' and r['verdict'] in ['accepted','accepted-with-explicit-delta'] and sha(r['report'])==r['report_sha256']
for k in ['required_repairs','required_mathematical_repairs','required_metadata_repairs']:assert not r.get(k,[]),(k,r.get(k))
reviewed={x['path']:x['sha256'] for x in r['reviewed_files']}
for x in load(RUN/'source-contract-inputs-v1.json')['rows']:assert reviewed[x['path']]==x['sha256']==sha(x['path']),x['path']
write(RUN/'stabilized-decision-v1.json',dict(status=r['verdict'],contract_version=1,source_report_sha256=r['report_sha256'],source_receipt_sha256=sha(RUN/'source-contract-receipt-v1.json'),all11_full_actual_types_unchanged=True,existing_bodies_preexist=True,new_proofs=0,new_definitions=0,current_BODY_pending=True,chapter_complete=False,goal_complete=False))
native('stabilized-event-v1','lifecycle-event','--session',TASK,'--event','stabilized','--payload-json',json.dumps(dict(run_id=RUN.name,contract_version=1,source_contract_accepted=True,existing_bodies_preexist=True,new_proofs=0,chapter_complete=False,goal_complete=False)))
native('proving-event-v1','lifecycle-event','--session',TASK,'--event','proving','--payload-json',json.dumps(dict(run_id=RUN.name,contract_version=1,route='One lower dependency-ready existing scalar-body/public-canary audit',new_proofs=0,chapter_complete=False,goal_complete=False)))
write(RUN/'30_lower_worker-v1.md','/root staged single lower worker, not independent source reviewer. Existing11full public bodies/2defs and whole23canary proofs/4defs/1abbr unchanged. Current CONTRACT accepted; focused41names/11fullguards/actualVALUE/canary next. ZERO new math. BODY/combined/reader/FINAL/nativeaccepted/PR and Chapter1/2 gates remain separate pending.')
gate('public-canary-focused-v1','lake','build','BanditRLProof.OnlineOptimalStep','Tests.OnlineOptimalStepCanary');fixed()
print('Actual source stabilized and complete focused public module/canary build passed; current BODY pending.')
