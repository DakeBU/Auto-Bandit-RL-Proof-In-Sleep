from common_v1 import *
fixed()
for name in ['source-contract-receipt-v1.json','source-repair-receipt-v1.json']:
 r=load(RUN/name);assert r['actor']['task']=='/root/source_reviewer' and r['verdict']=='accepted-with-explicit-delta'
 assert not r['required_repairs'] and not r.get('required_mathematical_repairs',[]) and not r.get('required_metadata_repairs',[])
 assert sha(r['report'])==r['report_sha256']
 reviewed={x['path']:x['sha256'] for x in r['reviewed_files']}
 for row in load(RUN/'source-contract-inputs-v1.json')['rows']:assert sha(row['path'])==row['sha256']==reviewed[row['path']],row['path']
assert load(RUN/'source-contract-receipt-v1.json')['required_reader_corrections']==load(RUN/'source-repair-receipt-v1.json')['required_reader_corrections']
targets=load(CONTRACT/'targets-v1.json')
write(RUN/'stabilized-contract-v1.json',dict(state='stabilized',version=1,source_sha256=PDF_SHA,targets_sha256=sha(CONTRACT/'targets-v1.json'),context_sha256=sha(CONTRACT/'public-context-v1.lean'),source_fingerprint_sha256=sha(RUN/'source-statement-fingerprint-v1.json'),source_review_receipt_sha256=sha(RUN/'source-contract-receipt-v1.json'),separate_source_repair_receipt_sha256=sha(RUN/'source-repair-receipt-v1.json'),original_reader_requirements=load(RUN/'source-contract-receipt-v1.json')['required_reader_corrections'],terminal_headers=targets['targets'],proofs_accepted=False,source_package_accepted=False,chapter_complete=False,goal_complete=False))
resolutions=[]
for folder in ['tasks','conversion-windows','proof-obligations','proof-blueprints','research-wiki/retrieval-index']:
 p=Path(folder)/(TASK+'.md');snap=RUN/'snapshots'/('CONTRACT-review-'+p.as_posix().replace('/','--')+'.raw');write(snap,p.read_bytes());resolutions.append(dict(original=p.resolve().as_posix(),original_sha256=sha(p),snapshot=snap.as_posix(),snapshot_sha256=sha(snap),reason='This task-owned mutable metadata may receive versioned state/proof updates; original reviewer bound bytes retained. No source/type/public/other-task waiver.'))
 p.write_bytes(p.read_bytes()+b'\n\n## Stabilized contract and proving state\n\nDistinct CONTRACT and separate reconciliation reviews accepted-with-explicit-delta. All exact R1-R8 remain required reader obligations. Nine frozen statements unchanged. First ready leaf: existing-limit sign bridge; actual proof body/build follows. No target proofs or package accepted at stabilization.\n')
write(RUN/'contract-review-baseline-resolutions-v1.json',resolutions)
native('stabilized-event-v1','lifecycle-event','--session',TASK,'--event','stabilized','--payload-json',json.dumps(dict(contract_version=1,frozen_contract=(RUN/'stabilized-contract-v1.json').as_posix(),source_and_reconciliation_separately_reviewed=True)))
native('proving-event-v1','lifecycle-event','--session',TASK,'--event','proving','--payload-json',json.dumps(dict(leaf=targets['targets'][0]['name'],reason='Real order/topology prerequisites actually imported/type checked',edit_scope=PUBLIC.as_posix(),frozen_terminal_sha256=targets['targets'][0]['header_sha256'])))
native('first-worker-running-v1','trial-log','--task',TASK,'--role','lower','--kind','attempt','--status','running','--run-id',RUN.name,'--lean',PUBLIC,'--attempt-id','NO-REGRET-V1','--harness','hierarchical','--target-fingerprint',sha(CONTRACT/'targets-v1.json'),'--notes','Reviewed first leaf: an already existing real limit under the shared upper property is nonpositive. Use actual le_of_tendsto and epsilon=a/2; no convergence existence assumption added to NoRegret.')
context=(CONTRACT/'public-context-v1.lean').read_text(encoding='utf8');prefix,rest=context.split('namespace NoRegretCounterexample',1)
header=targets['targets'][0]['header']
body=''' := by
  by_contra h
  have hpos : 0 < a := lt_of_not_ge h
  have hbound : a ≤ a / 2 :=
    le_of_tendsto hl (hNR u hu (a / 2) (by linarith))
  linarith

'''
write(PUBLIC,prefix+header+body+'namespace NoRegretCounterexample'+rest)
assert header+' := by' in PUBLIC.read_text(encoding='utf8')
gate('first-leaf-focused-build-v1','lake','build','BanditRLProof.OnlineNoRegretSemantics')
native('first-leaf-fence-v1','statement-fence','--declaration',targets['targets'][0]['name'],'--file',PUBLIC,'--output',RUN/'first-leaf-fence-v1.json')
native('first-leaf-safe-verify-v1','safe-verify','--fence',RUN/'first-leaf-fence-v1.json','--lean-file',PUBLIC)
native('first-worker-compiled-v1','trial-log','--task',TASK,'--role','lower','--kind','proof','--status','compiled','--run-id',RUN.name,'--lean',PUBLIC,'--attempt-id','NO-REGRET-V1','--harness','hierarchical','--target-fingerprint',sha(CONTRACT/'targets-v1.json'),'--new-declaration',targets['targets'][0]['name'],'--verifier-evidence',RUN/'first-leaf-focused-build-v1-exit.json','--progress-class','compiled-leaf','--obligations-before','9','--obligations-after','8','--notes','Actual first theorem body focused-builds. Remaining eight contract targets and all public/canary/kernel/root/Tests/harness/sourcebody/reader/site/PR gates remain. No chapter/program acceptance.')
write(RUN/'leaf-progress-v1.json',dict(contract_target_count=9,closed_public_targets=[targets['targets'][0]['name']],remaining_targets=[x['name'] for x in targets['targets'][1:]],public_sha256=sha(PUBLIC),safe_verify_is_header_scan_not_Lean_compiler=True,focus_build_is_actual_Lean_verifier=True,source_package_accepted=False,chapter_complete=False,goal_complete=False))
fixed();print('First actual frozen leaf compiled; nine-target frontier now eight pending, not package accepted')
