"""Repair comment-guard prose and enforce integration prerequisites; never weaken the theorem."""
from common_v2 import *
assert passed('preserve-body-native-v1-01')['exit_code']==0
for label in ['integrate-reader-v2-01','project-gates-v1-01']:assert load(RUN/(label+'-exit.json'))['exit_code']!=0
assert not (RUN/'public-comment-qualification-v1.json').exists() and not (RUN/'reader-integration-v1.json').exists()
f=fixed();assert sha(PUBLIC)==f['original_module_sha256']
assert load(RUN/'body-binding-audit-v1.json')['status']=='passed-at-review-boundary'
text=(RUN/'integrate-reader-v2.py').read_text(encoding='utf-8')
assert '+/-1' in text;text=text.replace('+/-1','+1 and -1')
text=text.replace("r=bind_review('public-body-receipt-v1.json','public-body-inputs-v1.json','body-binding-audit-v1.json')", "r=load(RUN/'public-body-receipt-v1.json');assert sha(r['report'])==r['report_sha256'];assert load(RUN/'body-binding-audit-v1.json')['status']=='passed-at-review-boundary'")
write(RUN/'integrate-reader-v3.py',text)
text=(RUN/'project-gates-v1.py').read_text(encoding='utf-8')
text=text.replace("f=fixed(True);assert", "f=fixed(True);assert load(RUN/'reader-integration-v1.json')['publication']=='research-wiki/contribution-contracts/online-affine-subgradient-migration-20261007.json';assert load(RUN/'integrated-public-guard-audit-v1.json')['status']=='passed';assert load(RUN/'public-comment-qualification-v1.json')['exact_original_raw_suffix'];assert")
for a,b in [('root-v1-01','root-v2-01'),('Tests-v1-01','Tests-v2-01'),('proof-obligations-candidate-v1','proof-obligations-candidate-v2'),('memory-digest-candidate-v1','memory-digest-candidate-v2'),('retrieval-index-candidate-v1','retrieval-index-candidate-v2'),('candidate-scoped-trials-v1','candidate-scoped-trials-v2'),('candidate-frontier-refresh-v1','candidate-frontier-refresh-v2'),('candidate-frontier-shadow-v1','candidate-frontier-shadow-v2'),('candidate-frontier-v1','candidate-frontier-v2'),('full-harness-v1-01','full-harness-v2-01')]:text=text.replace(a,b)
write(RUN/'project-gates-v2.py',text)
text=(RUN/'source-site-gates-v2.py').read_text(encoding='utf-8').replace("passed('project-gates-v1-01')","passed('project-gates-v2-01')")
write(RUN/'source-site-gates-v3.py',text)
helpers=[RUN/n for n in ['integrate-reader-v3.py','project-gates-v2.py','source-site-gates-v3.py']]
for p in helpers:compile(p.read_text(encoding='utf-8'),str(p),'exec')
generated('reader-repair-helpers-before-use-v3.json',helpers)
write(RUN/'reader-repair-v3.json',dict(status='repair-prepared-fresh-gates-required',actual_failed_labels=['integrate-reader-v2-01','project-gates-v1-01'],rootcause='Prose +/-1 contains nested Lean comment opener /-. Guard stopped before module/reader mutation. PowerShell continued subsequent commands; project reached missing manifest and failed. New saved adapters assert integration guard/publication/comment qualification before any project build.',failed_reader_module_unchanged=True,source_statement_unchanged=True,body_canary_unchanged=True,mathematical_repairs=[],failed_preintegration_rootTests=['root-v1-01','Tests-v1-01'],failed_candidate_metadata_not_acceptance='proof-obligations-candidate-v1.json retained as failed-attempt output; new v2 supersedes only after actual gates',new_required_labels=['integrate-reader-v3-01','project-gates-v2-01','root-v2-01','Tests-v2-01','full-harness-v2-01'],source_package_accepted=False,chapter_complete=False,goal_complete=False))
event('repair',dict(failure='reader prose comment lexical guard and continued preintegration project failed',mathematical_repairs=[],frozen_headers=f['headers'],source_package_accepted=False),'reader-v3')
print('Failed attempts retained; actual theorem unchanged; safer scoped reader/project adapters prepared.')
