"""Preserve CLI rejection; use actual gate-pending enum in a fresh scoped shadow."""
from common_v2 import *
fixed(True);assert load(RUN/'task-shadow-v1-01-exit.json')['exit_code']!=0 and load(RUN/'candidate-frontier-refresh-v1-exit.json')['exit_code']==2
text=(RUN/'task-shadow-v1.py').read_text(encoding='utf-8').replace("'--leaf-status','compiled'","'--leaf-status','gate-pending'")
for s in ['candidate-scoped-trials-v1','memory-digest-candidate-v1','candidate-frontier-refresh-v1','candidate-frontier-shadow-v1','candidate-frontier-v1']:text=text.replace(s,s.replace('v1','v2'))
write(RUN/'task-shadow-v2.py',text)
text=(RUN/'record-acceptance-v1.py').read_text(encoding='utf-8').replace("passed('task-shadow-v1-01')","passed('task-shadow-v2-01')");write(RUN/'record-acceptance-v2.py',text)
text=(RUN/'prepare-final-evidence-v2.py').read_text(encoding='utf-8').replace("'source-site-gates-v1-01']","'source-site-gates-v1-01','task-shadow-v2-01','candidate-frontier-refresh-v2','candidate-frontier-shadow-v2']")
text=text.replace("'full-context-comparison-v2-01']","'full-context-comparison-v2-01','task-shadow-v1-01','candidate-frontier-refresh-v1']")
text=text.replace("'Prospective TeX repair annotation", "'Task shadow CLI rejected invalid leaf-status compiled before producing a frontier; current actual enum gate-pending used in version2, original exit2/log preserved; no proof/source change.','Prospective TeX repair annotation")
write(RUN/'prepare-final-evidence-v3.py',text)
text=(RUN/'complete-delivery-gates-v2.py').read_text(encoding='utf-8').replace("passed('record-acceptance-v1-01')","passed('record-acceptance-v2-01')");write(RUN/'complete-delivery-gates-v3.py',text)
text=(RUN/'prepare-pr-payload-v2.py').read_text(encoding='utf-8').replace('All R1-R8 discharged', 'Original task-shadow invalid leaf-status compiled CLI exit2 is preserved; actual gate-pending scoped shadow passes without changing proofs or the global frontier. All R1-R8 discharged');write(RUN/'prepare-pr-payload-v3.py',text)
text=(RUN/'complete-delivery-gates-v3.py').read_text(encoding='utf-8').replace("passed('prepare-pr-payload-v2-01')","passed('prepare-pr-payload-v3-01')");write(RUN/'complete-delivery-gates-v4.py',text)
write(RUN/'shadow-adapter-repair-v2.json',dict(actual_failure='frontier-refresh argparse exit2: compiled is not a permitted leaf-status; no frontier created.',actual_schema='pending,ready,running,blocked,gate-pending,accepted',effective_candidate_status='gate-pending',old_failure_and_partial_scoped_inputs_preserved=True,public_canary_headers_combined_gate_unchanged=True,source_FINAL_repair_review_pending=True,new_proofs=0))
event('repair',dict(kind='task-scoped CLI status adapter only',repair=(RUN/'shadow-adapter-repair-v2.json').as_posix(),public_and_canary_unchanged=True),attempt='shadow-v2')
print('Actual CLI status schema repaired in fresh version2; original exit2 preserved, current shadow must execute.')
