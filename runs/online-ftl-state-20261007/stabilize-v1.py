from common_v1 import *
fixed(); r=load(RUN/'source-contract-receipt-v1.json')
assert r['actor']['task']=='/root/source_reviewer' and r['verdict'] in ['accepted','accepted-with-explicit-delta']
assert sha(r['report'])==r['report_sha256']
for key in ['required_repairs','required_mathematical_repairs','required_metadata_repairs']:assert not r.get(key,[]),key
reviewed={x['path']:x['sha256'] for x in r['reviewed_files']}
for x in load(RUN/'source-contract-inputs-v1.json')['rows']:assert sha(x['path'])==reviewed[x['path']]==x['sha256'],x['path']
for p,h in reviewed.items():assert sha(p)==h,p
sys.path.insert(0,str(ROOT));from tools.abrl_lifecycle import normalize_statement,lean_declaration_header
all_headers={**load(CONTRACT/'existing-Mean-headers-v1.json'),**load(CONTRACT/'new-public-headers-v1.json')}
write(CONTRACT/'stabilized-native-proof-headers-v1.json',{n:normalize_statement(h) for n,h in all_headers.items()})
for n in load(CONTRACT/'existing-Mean-headers-v1.json'):assert lean_declaration_header(MEAN,n)==normalize_statement(all_headers[n])
write(RUN/'stabilized-contract-v1.json',dict(status=r['verdict'],review_receipt_sha256=sha(RUN/'source-contract-receipt-v1.json'),review_report_sha256=r['report_sha256'],verified_fixed_rows=157,new_proof_headers_sha256=sha(CONTRACT/'new-public-headers-v1.json'),definitions_full_raw_binding_sha256=sha(CONTRACT/'production-definitions-v1.json'),exact_proof_terminal=PRE+'ftlState_eq_predict',first_ready_leaf=PRE+'empiricalMean_succ',native_header_limit='Supported := declarations only. Equation-style recursive ftlState guarded by exact full-definition bytes, compiled neutral-definition rfl identity/types and kernel audit; no native recursive-header fence claim.',required_reader_corrections=r['required_reader_corrections'],production_bodies_not_yet_written=True,source_package_accepted=False,chapter_complete=False,goal_complete=False))
native('stabilized-event-v1','lifecycle-event','--session',TASK,'--event','stabilized','--payload-json',json.dumps(dict(run_id=RUN.name,contract_version=1,stabilized_contract=(RUN/'stabilized-contract-v1.json').as_posix(),source_package_accepted=False,chapter_complete=False,goal_complete=False)))
native('proving-event-v1','lifecycle-event','--session',TASK,'--event','proving','--payload-json',json.dumps(dict(run_id=RUN.name,contract_version=1,dependency_ready_leaf=PRE+'empiricalMean_succ',terminal=PRE+'ftlState_eq_predict',source_package_accepted=False,chapter_complete=False,goal_complete=False)))
write(RUN/'30_lower-ready-leaf-v1.md','/root staged lower worker: CONTRACT independently accepted; first dependency-ready leaf empiricalMean_succ, source-structural allprefix recurrence. Zero t handled explicitly; positive t finite-sum successor, positive casts, field_simp and ring. Terminal/header frozen; edits Mean append only exact one proof; all old4proof1def unchanged. Focused compile plus exactnative fence, retrieval, axioms recorded separately; leaf compilation not package/Chapter acceptance.')
fixed();print('Actual CONTRACT stabilized; first leaf proving authorized within frozen scope.')
