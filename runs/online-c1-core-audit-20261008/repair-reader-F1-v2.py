from common_integrated_v1 import *

fixed_integrated()
receipt=load(RUN/'final-reader-receipt-v1.json')
assert sha(RUN/'final-reader-receipt-v1.json')=='ad18f615d607e7f1c3937f307f1502a33119e90a0c300ab6096a7b32a038d0cd'
assert receipt['verdict']=='rejected' and len(receipt['required_blocking_repairs'])==1
assert receipt['required_blocking_repairs'][0]['id']=='F1' and not receipt['required_mathematical_repairs']
paths=[Path('website/content/highlights.json'),Path('runs/trials.jsonl'),Path('runs/lifecycle_sessions.jsonl')]
snapshots=[]
for i,p in enumerate(paths):
    q=RUN/'snapshots'/('FINAL-v1-F1-mutable-'+str(i)+'.raw')
    write(q,p.read_bytes());snapshots.append(dict(live_path=p.resolve().as_posix(),snapshot=q.resolve().as_posix(),sha256=sha(q)))
write(RUN/'FINAL-v1-mutable-reader-repair-bindings-v2.json',snapshots)
proposal=load(RUN/'reader-proposal-v2.json')
note=next(x for x in proposal['notes'] if x['full_name']==PRE+'meanPredict_independent')
before=note['math'];assert before.count('Y_i,')==1
after=before.replace('Y_i,','Y_i\\ (t>0),')
note['math']=after
write(RUN/'reader-proposal-v3.json',proposal)
write(CONTRACT/'reader-repair-v3.json',dict(mathematical_contract_version=2,presentation_version=3,
    rejected_FINAL_receipt_sha256=sha(RUN/'final-reader-receipt-v1.json'),rejected_report_sha256=sha(RUN/'final-reader-review-v1.md'),
    blocker='F1: averaging branch missing t>0 at actual initialhalf t0',path='website/content/highlights.json',
    full_name=note['full_name'],field='math',old=before,new=after,
    exact_reader_only_change=True,independence_all_natural_times_preserved=True,
    five_module_headers_bodies_and_canary_immutable=True,source_audits_remain_pending=5,goal_complete=False))
native('FINAL-rejected-reviewer-trial-v2','trial-log','--task',TASK,'--role','reviewer','--kind','review','--status','rejected',
    '--run-id',RUN.name,'--attempt-id','CORE-AUDIT-FINAL-V1','--verifier-evidence',RUN/'final-reader-receipt-v1.json',
    '--harness','hierarchical','--progress-class','diagnostic','--reviewer-validated',
    '--obligations-before','5','--obligations-after','5','--notes','FINAL419 rejected F1 reader averaging branch lacks t>0; mathematical statements/bodies accepted unchanged. Preserve rejection/raw inputs; exact owned math field repair only, no source-audit acceptance.')
native('FINAL-reader-repair-event-v2','lifecycle-event','--session',TASK,'--event','repair','--payload-json',
    json.dumps(dict(run_id=RUN.name,contract_version=2,presentation_version=3,repair=(CONTRACT/'reader-repair-v3.json').as_posix(),
        blocker='F1',frozen_mathematical_target_unchanged=True,source_audits_pending=5,chapter_complete=False,goal_complete=False)))
reader=Path('website/content/highlights.json');data=load(reader)
target=next(x for x in data['highlights'] if x['full_name']==note['full_name']);assert target['math']==before
target['math']=after;reader.write_bytes((json.dumps(data,ensure_ascii=False,indent=2)+'\n').encode('utf8'))
write(RUN/'reader-repair-integration-bindings-v2.json',dict(reader_proposal_sha256=sha(RUN/'reader-proposal-v3.json'),
    old_highlights_sha256=snapshots[0]['sha256'],current_highlights_sha256=sha(reader),only_one_math_field_changed=True,
    mathematical_headers_bodies_unchanged=True,required_fresh_reader_site_FINAL=True))
# Keep the original guard/scripts and rejected receipt immutable. New guard enforces the exact F1 delta.
s=(RUN/'common_integrated_v1.py').read_text(encoding='utf8')
s=s.replace("RUN/'reader-proposal-v2.json'","RUN/'reader-proposal-v3.json'")
s=s.replace("RUN/'reader-integration-bindings-v1.json'","RUN/'reader-repair-integration-bindings-v2.json'")
write(RUN/'common_reader_repair_v2.py',s)
for source,dest in [('build-clean-site-v1.py','build-clean-site-v2.py'),('verify-registry-v1.py','verify-registry-v2.py'),
    ('capture-reader-v1.py','capture-reader-v2.py'),('capture-reader-v1.cjs','capture-reader-v2.cjs')]:
    s=(RUN/source).read_text(encoding='utf8').replace('common_integrated_v1','common_reader_repair_v2').replace('-v1','-v2')
    # The same original 10935-node registry baseline remains authoritative.
    s=s.replace('registry-base-snapshot-v2.json.gz','registry-base-snapshot-v1.json.gz')
    write(RUN/dest,s)
write(RUN/'reader-F1-repair-result-v2.json',dict(exact_delta=load(CONTRACT/'reader-repair-v3.json'),
    live_highlights_sha256=sha(reader),old_RAW_reader_preserved=True,rejected_FINAL_preserved=True,
    applicable_original_Lean_gate_unchanged=True,source_audits_still_candidate=5,chapter_complete=False,goal_complete=False))
print('Actual F1 repair only; native rejection/repair recorded, fresh contributor/clean site/render/FINAL pending.')
