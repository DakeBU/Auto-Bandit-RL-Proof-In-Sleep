from lower_common_v1 import *
d=reviewed()
assert PRODUCTION.is_file()
initial_body_sha=sha(PRODUCTION)
write(CONTRACT/'nonsmooth-stabilized-v1.json',dict(
 phase='stabilized finite exact three-terminal source contract; not proved or Chapter2 accepted',
 operative_source_inventory=(CONTRACT/'complete-source-reconciliation-draft-v3.json').relative_to(ROOT).as_posix(),
 operative_source_inventory_sha256=sha(CONTRACT/'complete-source-reconciliation-draft-v3.json'),
 superseded_inventory_v2='Retained only as historical bootstrap/task/conversion pointer; version3 is the operative accepted source enumeration.',
 exact_target_contract_sha256=sha(CONTRACT/'nonsmooth-targets-draft-v1.json'),target_hashes=[dict(declaration=t['declaration'],statement_hash=t['statement_hash']) for t in d['targets']],
 review_receipt_sha256=REVIEW_SHA,source_repair_separately_accepted=True,
 allowed_scope='Three exact terminal bodies in NEW OnlineNonsmoothExamples; staged NEW canary; OWN metadata. All old production/Test/pins/source/root remain immutable at this proof stage.',
 leaf_order=['NS001 shifted absolute: ready Mathlib convex/translation/calculus','NS002 hinge: ready existing affine convexity/full support and differentiability equivalence','NS003 labelled: blocked until NS002 actual kernel completion; real scalar/inner self construction'],
 record_timing='Initial NS001 body was authored after the actual distinct contract/source-repair acceptance and before this native event write. No compile had occurred. This records the real delayed event timing, not runtime enforcement or backdated chronology.',
 initial_absolute_body_sha256=initial_body_sha,
 chapter_complete=False,book_complete=False,whole_Goal_status='ACTIVE'))
event('nonsmooth-stabilized-event-v1','stabilized',dict(operative_inventory=sha(CONTRACT/'complete-source-reconciliation-draft-v3.json'),
 contract=sha(CONTRACT/'nonsmooth-stabilized-v1.json'),review_receipt=REVIEW_SHA,exact_finite_terminals=3,source_families=2,
 proof_leaf_total=None,chapter_complete=False,goal_complete=False))
event('absolute-proving-event-v1','proving',dict(leaf='NS001',terminal_hash=d['targets'][0]['statement_hash'],
 approved_scope=sha(CONTRACT/'nonsmooth-stabilized-v1.json'),owning_module='BanditRLProof/OnlineNonsmoothExamples.lean',
 ready_dependencies='Pinned actual ConvexOn.comp_affineMap/univ_norm, abs derivative off0 and nonderivative0; no supplied mathematical conclusion.',
 initial_body_authored_after_actual_review_before_native_event=True,initial_body_sha256=initial_body_sha,
 chapter_complete=False,goal_complete=False))
write(RUN/'leaf-NS001-attempt-v1.lean',PRODUCTION.read_bytes())
headers(1)
print('Finite source contract stabilized; NS001 permitted and dependency-ready. NS003 awaits actual NS002 completion.')
