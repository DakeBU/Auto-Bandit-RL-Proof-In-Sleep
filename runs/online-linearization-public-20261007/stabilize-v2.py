from common_v2 import *
fixed();d=load(RUN/'blind-decoder-receipt-v3.json');assert d['actor']['task']=='/root/osd_blind' and d['input']['sha256_raw_bytes']==sha(RUN/'blind-packet-v3.md') and d['report']['sha256_raw_bytes']==sha(RUN/'blind-decoder-v3.md')
r=load(RUN/'source-contract-receipt-v2.json');assert r['actor']['task']=='/root/source_reviewer' and r['verdict'] in ['accepted','accepted-with-explicit-delta'] and sha(r['report'])==r['report_sha256']
for k in ['required_repairs','required_mathematical_repairs','required_metadata_repairs']:assert not r.get(k,[]),(k,r.get(k))
reviewed={x['path']:x['sha256'] for x in r['reviewed_files']}
for x in load(RUN/'source-contract-inputs-v2.json')['rows']:assert reviewed[x['path']]==x['sha256']==sha(x['path']),x['path']
write(RUN/'stabilized-decision-v2.json',dict(status=r['verdict'],contract_version=2,source_report_sha256=r['report_sha256'],source_receipt_sha256=sha(RUN/'source-contract-receipt-v2.json'),all18_full_actual_types_unchanged=True,existing_bodies_preexist=True,new_proofs=0,new_definitions=0,current_BODY_pending=True,chapter_complete=False,goal_complete=False))
native('stabilized-event-v2','lifecycle-event','--session',TASK,'--event','stabilized','--payload-json',json.dumps(dict(run_id=RUN.name,contract_version=2,source_contract_accepted=True,existing_bodies_preexist=True,new_proofs=0,chapter_complete=False,goal_complete=False)))
native('proving-event-v2','lifecycle-event','--session',TASK,'--event','proving','--payload-json',json.dumps(dict(run_id=RUN.name,contract_version=2,route='Single lower dependency-ready existing-body/public canary audit',new_proofs=0,chapter_complete=False,goal_complete=False)))
write(RUN/'30_lower_worker-v2.md','/root staged one lower worker; not independent reviewer. Existing18full public proof bodies/9defs/3abbr and whole25canaryproofs/8defs/2abbr remain unchanged. Current CONTRACT accepted; actual focused/type/kernel/18fullguards/VALUE/canary next; source/public reuse ZERO new math. BODY/combined/reader/FINAL/nativeaccepted/PR and Chapter1/2 remain separate pending.')
gate('public-canary-focused-v2','lake','build','BanditRLProof.OnlineLinearization','Tests.OnlineLinearizationCanary');fixed()
print('Actual source stabilized and existing whole focused module/canary compilation passed; current BODY pending.')
