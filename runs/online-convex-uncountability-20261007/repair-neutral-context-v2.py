"""Repair an actual standalone neutral-context import defect; immutable math targets."""
from common_v1 import *
fixed();assert load(RUN/'neutral-context-v1-01-exit.json')['exit_code']==1
old=RUN/'leaves/neutral-context-v1.lean';text=old.read_text(encoding='utf-8')
new=text.replace('import Mathlib.Analysis.Real.Cardinality','import Mathlib.Analysis.Real.Cardinality\nimport Mathlib.Analysis.Calculus.Deriv.Abs')
write(RUN/'leaves/neutral-context-v2.lean',new)
packet=(RUN/'blind-packet-v1.md').read_text(encoding='utf-8').replace('import Mathlib.Analysis.Real.Cardinality','import Mathlib.Analysis.Real.Cardinality\nimport Mathlib.Analysis.Calculus.Deriv.Abs').replace('blind-reconstruction-v1.md','blind-reconstruction-v2.md').replace('blind-receipt-v1.json','blind-receipt-v2.json')
packet+='\nContext revision2: an actual standalone type probe with the original two listed imports failed to resolve DifferentiableAt. The third listed import supplies that existing symbol. Same Q/P1/P2, objects and quantifiers; no source identity or theorem bodies. Original packet/reconstruction/probe/log preserved. Reconstruct these exact targets afresh and record current raw hashes.\n'
write(RUN/'blind-packet-v2.md',packet)
write(RUN/'neutral-context-repair-v2.json',dict(status='actual-context-failure-repair-awaits-compile-and-separate-review',failure='neutral-context-v1-01',error_signature='Unknown identifier DifferentiableAt in standalone neutral imports',repair='Add pinned Mathlib.Analysis.Calculus.Deriv.Abs to listed neutral context imports; source-qualified target type probes already valid.',old_neutral_packet_sha256=sha(RUN/'blind-packet-v1.md'),new_neutral_packet_sha256=sha(RUN/'blind-packet-v2.md'),frozen_headers=load(RUN/'draft-freeze-v1.json')['headers'],definition_and_mathematical_targets_unchanged=True,original_source_contract_review_retained=True,original_review_scope='Accepted source-target mathematics before this independent standalone-context audit; not used to waive the subsequently discovered defect.',diagnostic_unresolved_sorry_is_not_production_closure=True,source_package_accepted=False,chapter_complete=False,goal_complete=False))
gate('neutral-context-v2-01','lake','env','lean',RUN/'leaves/neutral-context-v2.lean')
event('repair',dict(kind='neutral-context-import',repair=(RUN/'neutral-context-repair-v2.json').as_posix(),terminal_unchanged=True,distinct_decoder_and_separate_source_repair_review_pending=True),attempt='context-v2')
fixed();print('Actual neutral context v2 elaborates both unchanged targets; new blind/repair review pending.')
