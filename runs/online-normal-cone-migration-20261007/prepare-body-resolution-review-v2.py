from common import *
r=load(RUN/'public-body-receipt-v1.json');assert r['verdict']=='rejected';assert sha(r['report'])==r['report_sha256'];assert not r.get('required_mathematical_repairs',[]) and not r.get('mathematical_repairs',[])
v=load(RUN/'prior-contract-binding-v2.json')
for row in v['rows']:assert sha(row['resolved'])==row['sha256']
write(RUN/'body-resolution-repair-decision-v1.json',dict(stage='repair',rejected_body_receipt='public-body-receipt-v1.json',rejected_report_sha256=r['report_sha256'],failure='v1 resolution index points to mutable globals after native appends; mathematical targets/canaries passed separately',corrected_index='prior-contract-binding-v2.json',corrected_index_sha256=sha(RUN/'prior-contract-binding-v2.json'),verified_exact_original_rows=len(v['rows']),mathematical_repairs=[],source_statement_version_unchanged=True,proof_rework=False,old_rejection_inputs_reports_preserved=True,body_v2_review_required=True,source_package_accepted=False,chapter_complete=False,goal_complete=False))
s=(RUN/'review-packets-v1.py').read_text(encoding='utf-8-sig')
for suffix in ['review','receipt','packet','inputs']:s=s.replace("stem+'-"+suffix+"-v1.","stem+'-"+suffix+"-v2.")
s=s.replace("mode=sys.argv[1];fixed", "mode=sys.argv[1];assert mode=='BODY';fixed")
s=s.replace("BODY recommendation only.", "BODYv2 resolution-only repair review, retaining rejected BODYv1. Independently verify prior-contract-binding-v2.json ALL149 rows and exact original snapshots; original v1 current-global pointers became stale after appends and are not a current verified resolution index. Old reports/receipts/fixed inputs unchanged. No mathematical or frozen statement repair; actual fresh Lean gates remain applicable. Check both prior original input hashes via original snapshots and current fixed inputs. BODY recommendation only.")
write(RUN/'review-packets-v2.py',s);generated('body-repair-packet-helper-before-use-v2.json',[RUN/'review-packets-v2.py'])
