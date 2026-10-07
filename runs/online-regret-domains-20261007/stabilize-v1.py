from common_v1 import *
fixed();r=load(RUN/'source-contract-receipt-v1.json')
assert r['actor']['task']=='/root/source_reviewer' and r['verdict'] in ['accepted','accepted-with-explicit-delta']
assert sha(r['report'])==r['report_sha256']
for key in ['required_repairs','required_mathematical_repairs','required_metadata_repairs']:assert not r.get(key,[]),key
reviewed={x['path']:x['sha256'] for x in r['reviewed_files']}
inputs=load(RUN/'source-contract-inputs-v1.json')
for x in inputs['rows']:assert sha(x['path'])==reviewed[x['path']]==x['sha256'],x['path']
for p,h in reviewed.items():assert sha(p)==h,p
sys.path.insert(0,str(ROOT));from tools.abrl_lifecycle import normalize_statement,lean_declaration_header
for n,h in load(CONTRACT/'existing-public-headers-v1.json').items():assert lean_declaration_header(PUBLIC,n)==normalize_statement(h),n
write(RUN/'stabilized-contract-v1.json',dict(status=r['verdict'],review_receipt_sha256=sha(RUN/'source-contract-receipt-v1.json'),review_report_sha256=r['report_sha256'],verified_fixed_rows=inputs['fixed_input_count'],existing_public_proofs=2,existing_public_definitions=2,new_production_math=0,frozen_validation_proofs=8,exact_mapping_terminal='Typed W-loss and V-comparator reuse of existing shared API; required subobligation C1-REGRET-DIFFERENT-ACTION-COMPARATOR-SETS',first_ready_leaf=TEST+'domain_gap_sum',required_reader_corrections=r['required_reader_corrections'],new_test_bodies_not_yet_written=True,source_package_accepted=False,chapter_complete=False,goal_complete=False))
native('stabilized-event-v1','lifecycle-event','--session',TASK,'--event','stabilized','--payload-json',json.dumps(dict(run_id=RUN.name,contract_version=1,stabilized_contract=(RUN/'stabilized-contract-v1.json').as_posix(),source_package_accepted=False,chapter_complete=False,goal_complete=False)))
native('proving-event-v1','lifecycle-event','--session',TASK,'--event','proving','--payload-json',json.dumps(dict(run_id=RUN.name,contract_version=1,dependency_ready_leaf=TEST+'domain_gap_sum',source_package_accepted=False,chapter_complete=False,goal_complete=False)))
write(RUN/'30_lower-ready-leaf-v1.md','/root staged lower worker: reviewed CONTRACT first; actual typed-domain gap-sum leaf uses public comparatorRegret_eq_sum at X=SubtypeW and embeds comparator fromV. Frozen statements remain exact. Other finite-domain tests then derive concrete nonpositive regret, with public adapter bound0. No generic performance/causality/minimum/limit claim. New tests only; owning public mathematical bytes unchanged.')
fixed();print('Actual CONTRACT stabilized; ready typed leaf proving; no new test theorem body yet.')
