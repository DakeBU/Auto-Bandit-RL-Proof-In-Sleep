"""Audit actual current/historical raw bindings before package acceptance."""
from pathlib import Path
import hashlib,json
run=Path(__file__).parent
def load(p):return json.loads(Path(p).read_text(encoding='utf-8'))
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
snap={r['path']:r for r in load(run/'historical-raw-supersession-v1.json')['rows']}
rows=[]
for name in ['source-contract-receipt-v1.json','public-body-receipt-v1.json','final-reader-receipt-v1.json']:
    p=run/name;r=load(p);assert r['actor']['task']=='/root/source_reviewer'
    assert r['verdict'] in ['accepted','accepted-with-explicit-delta'] and sha(r['report'])==r['report_sha256']
    for x in r['reviewed_files']:
        current=sha(x['path']);resolved=x['path'];delta='none'
        if current!=x['sha256']:
            s=snap[x['path']];assert sha(s['snapshot'])==x['sha256']==s['raw_sha256']
            resolved=s['snapshot'];delta=s['authorized_delta']
        rows.append(dict(receipt=p.as_posix(),path=x['path'],raw_sha256=x['sha256'],resolved_raw_file=resolved,current_sha256=current,explicit_delta=delta))
review=load(run/'final-reader-receipt-v1.json');assert not review['required_repairs']
inventory=load(run/'final-reader-inputs-v1.json');reviewed={x['path']:x['sha256'] for x in review['reviewed_files']}
for x in inventory['rows']:assert reviewed[x['path']]==x['sha256']==sha(x['path'])
for p in inventory['canonical_surfaces']:assert sha(p)==reviewed[p]
registry=load(run/'registry-final02.json');assert registry['status']=='passed' and len(registry['checks'])==27
assert load(run/'finite-loss-constraint-gap-v1.json')['status']=='mandatory-pending-new-contract'
assert load(run/'review-history-audit-v2.json')['status']=='passed'
gates=load(run/'public-actual-bindings-v1.json')['actual_passed_gates']+['root-v1-01','Tests-v1-01','full-harness-v1-01','contributor-exact-v1-03','site-final02-build','site-final02-check','registry-final02-repair-v1','browser-final02','review-history-v2-01','scoped-diff-v3-01','public-axioms-v2-01','candidate-frontier-refresh-v1','candidate-frontier-shadow-v1']
for label in gates:assert load(run/(label+'-exit.json'))['exit_code']==0,label
diff=load(run/'scoped-diff-v3.json')
result=dict(status='passed',raw_review_rows_verified=len(rows),rows=rows,final_fixed_input_rows=len(inventory['rows']),
    historical_prior_binding_rows_rechecked=load(run/'review-history-audit-v2.json')['raw_rows_verified'],
    final_clean_site_commit=registry['source_commit'],preserved_old_registry_nodes=registry['preserved_base_node_ids_and_urls'],
    actual_passed_gates=gates,whitespace_exception=dict(exception_paths=diff['exception_paths'],reason=diff['reason']),
    new_proofs=0,chapter_complete=False,goal_complete=False,finite_loss_gap_still_mandatory=True)
with (run/'accepted-binding-audit-v1.json').open('w',encoding='utf-8',newline='\n') as f:json.dump(result,f,indent=2);f.write('\n')
print('Current source/body/final raw review bindings passed:',len(rows),'rows; finite-loss gap/whole Goal still open.')
