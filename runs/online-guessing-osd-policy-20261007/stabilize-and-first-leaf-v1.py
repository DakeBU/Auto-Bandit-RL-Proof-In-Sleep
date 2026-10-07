from common_v1 import *
fixed();r=load(RUN/'source-contract-receipt-v1.json')
assert r['actor']['task']=='/root/source_reviewer' and r['verdict']=='accepted-with-explicit-delta'
assert not r['required_repairs'] and not r['required_mathematical_repairs'] and not r['required_metadata_repairs']
assert sha(r['report'])==r['report_sha256']
reviewed={row['path']:row['sha256'] for row in r['reviewed_files']}
for row in load(RUN/'source-contract-review-inputs-v1.json')['rows']:assert reviewed[row['path']]==row['sha256']==sha(row['path']),row['path']
write(RUN/'stabilized-contract-v1.json',dict(stage='stabilized',source_contract_verdict=r['verdict'],report_sha256=r['report_sha256'],receipt_sha256=sha(RUN/'source-contract-receipt-v1.json'),raw_input_rows=87,four_full_header_sha256=sha(CONTRACT/'headers-v1.json'),terminal_frozen=True,ready_leaf='selected_bound',future_reader_obligations=r['required_reader_corrections'],source_package_accepted=False,chapter_complete=False,goal_complete=False))
native('stabilized-event-v1-01','lifecycle-event','--session',TASK,'--event','stabilized','--payload-json',json.dumps(dict(run_id=RUN.name,contract_version=1,source_contract_receipt_sha256=sha(RUN/'source-contract-receipt-v1.json'),ready_leaf='selected_bound',chapter_complete=False,goal_complete=False)))
native('proving-event-v1-01','lifecycle-event','--session',TASK,'--event','proving','--payload-json',json.dumps(dict(run_id=RUN.name,contract_version=1,leaf='selected_bound',dependency='Actual public global absolute loss_subgradient_bound compiled',allowed_edit='Frozen selected_bound header, body only; other terminal headers remain frozen',chapter_complete=False,goal_complete=False)))
write(RUN/'worker-first-leaf-v1.md','ROOT staged worker, requested Astra/medium. Leaf selected_bound is dependency-ready: hlegal supplies actual chosen global support membership at t<T; reuse proved absolute-loss global norm producer. No initial feasibility/label bound/positive eta added. Frozen exact header maintained; focused compilation proves ONLY this first leaf, not other targets/source package/chapter.')
text=(CONTRACT/'public-context-v1.txt').read_text(encoding='utf-8')+'\n'+load(CONTRACT/'headers-v1.json')['selected_bound']+''' := by
  exact loss_subgradient_bound (y t) _ _ (hlegal t ht)

end BanditRL.OnlineGuessingSubgradientPolicy
'''
write(PUBLIC,text);write(RUN/'leaves/first-public-leaf-v1.lean.txt',text)
gate('first-public-leaf-focused-v1-01','lake','build','BanditRLProof.OnlineGuessingSubgradientPolicy')
native('first-public-leaf-fence-v1-01','statement-fence','--declaration','BanditRL.OnlineGuessingSubgradientPolicy.selected_bound','--file',PUBLIC,'--source-assumption','Actual played global support membership on the same absolute-loss history run; no assumed norm bound','--output',str(RUN/'native-public-fences/selected_bound-v1.json'))
native('first-public-leaf-safe-v1-01','safe-verify','--fence',str(RUN/'native-public-fences/selected_bound-v1.json'),'--lean-file',PUBLIC)
write(Path('proof-obligations')/(TASK+'-proving-v1.json'),dict(task=TASK,stage='proving',frozen_contract=CONTRACT.as_posix(),first_leaf='selected_bound',first_leaf_status='compiled-focused-public-with-actual-native-fence',first_leaf_receipt=RUN.joinpath('first-public-leaf-focused-v1-01-exit.json').as_posix(),terminal='example_2_32',terminal_status='pending',remaining_new_targets=['step_clamp','example_2_32','example_2_32_average_eventually'],source_body_and_public_canary='pending',package_acceptance=False,chapter_complete=False,goal_complete=False))
fixed();print('First dependency-ready PUBLIC leaf actually compiled/fenced; full Example2.32 terminal remains pending.')
