"""Respect immutable earlier reader obligations, explicitly discharged by actual FINAL."""
from common_v2 import *
assert load(RUN/'record-acceptance-v1-01-exit.json')['exit_code'] != 0
assert not (RUN/'accepted-decision-v1.json').exists()
f=fixed(True)
final=load(RUN/'final-reader-receipt-v1.json')
assert sha(final['report'])==final['report_sha256']
assert final['verdict']=='accepted-with-explicit-delta'
assert not final['required_blocking_reader_repairs']
assert set(final['reader_requirement_verdicts'])=={'R'+str(i) for i in range(1,8)}
assert all(r['verdict']=='satisfied' for r in final['reader_requirement_verdicts'].values())
rows=[]
for name in ['source-contract-receipt-v1.json','public-body-receipt-v1.json']:
 r=load(RUN/name);assert sha(r['report'])==r['report_sha256']
 requirements=r['required_blocking_reader_repairs']
 assert len(requirements)==7
 assert {s.split(':',1)[0] for s in requirements}==set(final['reader_requirement_verdicts'])
 rows.append(dict(receipt=name,sha256=sha(RUN/name),historical_required_reader_repairs=requirements,discharged_by='final-reader-receipt-v1.json',final_receipt_sha256=sha(RUN/'final-reader-receipt-v1.json'),final_verdicts=final['reader_requirement_verdicts']))
write(RUN/'acceptance-reader-discharge-v2.json',dict(status='passed',rows=rows,original_receipts_reports_unchanged=True,mathematical_repairs=[],chapter_complete=False,goal_complete=False))
src=(RUN/'record-acceptance-v1.py').read_text(encoding='utf-8')
old="for key in ['required_repairs','required_mathematical_repairs','mathematical_repairs','required_metadata_repairs','required_blocking_reader_repairs']:assert not r.get(key,[]),(key,r.get(key))"
new="""for key in ['required_repairs','required_mathematical_repairs','mathematical_repairs','required_metadata_repairs']:assert not r.get(key,[]),(key,r.get(key))
 if r.get('required_blocking_reader_repairs',[]):
  discharge=load(RUN/'acceptance-reader-discharge-v2.json');assert discharge['status']=='passed'
  row=next(x for x in discharge['rows'] if x['receipt']==receipt)
  assert sha(RUN/receipt)==row['sha256'] and r['required_blocking_reader_repairs']==row['historical_required_reader_repairs']
  terminal=load(RUN/'final-reader-receipt-v1.json');assert sha(RUN/'final-reader-receipt-v1.json')==row['final_receipt_sha256']
  assert not terminal.get('required_blocking_reader_repairs',[])
  assert terminal['reader_requirement_verdicts']==row['final_verdicts'] and all(x['verdict']=='satisfied' for x in row['final_verdicts'].values())
 else:assert not r.get('required_blocking_reader_repairs',[])"""
assert src.count(old)==1
src=src.replace(old,new)
src=src.replace("nonmathematical_repairs=integrated['failure_repairs']", "nonmathematical_repairs=integrated['failure_repairs']+[load(RUN/'acceptance-adapter-repair-v2.json')]")
write(RUN/'record-acceptance-v2.py',src);compile(src,str(RUN/'record-acceptance-v2.py'),'exec')
generated('acceptance-helper-before-use-v2.json',[RUN/'record-acceptance-v2.py'])
write(RUN/'acceptance-adapter-repair-v2.json',dict(status='repair-prepared-fresh-acceptance-required',actual_failed_attempt='record-acceptance-v1-01',cause='Adapter wrongly required historical CONTRACT/BODY prospective reader requirements to be absent despite FINAL explicitly satisfying R1-R7.',resolution='Keep original receipts byte-fixed; explicitly hash-bind all seven original requirements to actual FINAL satisfied verdicts before acceptance. Current FINAL blocking/math/metadata repair lists must still be empty.',discharge='acceptance-reader-discharge-v2.json',mathematical_repairs=[],source_module_canary_headers_unchanged=True,readonly_diagnostic='Receipt inspection used default GBK stdout and failed UnicodeEncodeError; repeated successfully with Python -X utf8. No source write.',chapter_complete=False,goal_complete=False))
event('repair',dict(failure='acceptance adapter historical reader requirements versus FINAL discharge',resolution='all original R1-R7 explicitly hash-bound to actual FINAL satisfied verdicts; no receipt rewrite',frozen_headers=f['headers'],mathematical_repairs=[],source_package_accepted=False),'acceptance-reader-v2')
print('Versioned acceptance adapter prepared; original receipts and mathematical bytes unchanged.')
