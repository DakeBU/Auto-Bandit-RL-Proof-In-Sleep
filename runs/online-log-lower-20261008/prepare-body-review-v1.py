from common_v1 import *
fixed()
b=load(RUN/'body-bindings-v1.json')
assert b['named_kernel_checks']==76 and b['exact_closed_proposition_identities']==64
assert b['public_sha256']==sha(PUBLIC) and b['canary_sha256']==sha(CANARY)
assert b['full_native_proof_fences']==64 and len(b['required_value_pairs'])==30
old=load(RUN/'source-contract-receipt-v1.json')
reviewed={x['path']:x['sha256'] for x in old['reviewed_files']}
for row in load(RUN/'source-contract-inputs-v2.json')['rows']:
    assert sha(row['path'])==reviewed[row['path']]==row['sha256'],row['path']
blind=load(RUN/'full-blind-decoder-receipt-v1.json')
assert blind['actor']['task']=='/root/osd_blind'
for key in ['input','input_manifest','report']:
    row=blind[key];path=RUN/row['path']
    assert sha(path)==row['sha256_raw_bytes'],path
for row in blind['reviewed_files']:
    assert sha(RUN/row['path'])==row['sha256_raw_bytes'],row['path']
assert len(blind['proposition_ids'])==64
write(RUN/'full-blind-binding-audit-v1.json',dict(
    input_sha256=blind['input']['sha256_raw_bytes'],
    input_manifest_sha256=blind['input_manifest']['sha256_raw_bytes'],
    report_sha256=blind['report']['sha256_raw_bytes'],
    receipt_sha256=sha(RUN/'full-blind-decoder-receipt-v1.json'),
    all64_actual_propositions_reconstructed=True,
    actual_closed_prop_equalities='all-exact-types-v3; recursive/nominal bridges actually proved',
    no_source_or_proof_acceptance_in_decoder=True))
status='''

## Compiled candidate: same-process logarithmic lower producer

Version1 CONTRACT accepted-with-explicit-delta. All16 frozen target headers are unchanged and actual theorem bodies compile. Derived policy/seed-independent smoothed binary law, all-horizon normalization, produced count moments/variance, same chronological decoded path and strict-past prediction, actual shared empirical-mean feasibility/minimum and comparator regret. Actual loss successor and expected best loss lead to H(T+1)/6; measurable pointwise interval-bounded seeds yield proved integrability, finite-sum interchange and ONE fixed path chosen outside the seed integral; log(T+2)/6 follows. Source printed4/PDF16 gives only qualitative unavoidability and explicitly no minimax-optimality proof there; coefficient1/6 is derived support, not printed/sharp. T0 law total, positiveT terminals; no HP/AS/uniform-seed/one-infinite-path claim.

Actual public48proofs/10definition-components (8 frozen models+2 same-path loss components),16 named validation proofs/2fixtures,76 kernel axioms standard-only,64 closed proposition equalities/12definition equalities with actual recursive/nominal equality bridges,64 native header/forbidden-token guards and30 prespecified compiled VALUE pairs. Public lookup actual. Full source-neutral64-slot reconstruction independently bound; reused automated roles/history disclosed/requestedAstra/medium/runtime unverified. Failed proof, metadata, neutral-generation and test attempts preserved. Native safe-verify does not compile: focused builds, named kernel checks and type-equality compilation are separate evidence. BODY/rootTests/harness/source-qualified shared Book/FINAL/native acceptance/PR pending.

Only C1-LOG-UNAVOIDABLE can eventually close, not full Chapter1. Original16sourceitems/proof-totalnull/fullRegret/NoRegret/six old main-relative gaps remain required. Chapter2incomplete,3–16unenumerated/necessaryappendicesrequired,totalGoalACTIVE. ExactOPENunmergedPR190stackedbase9425fecb38be60b1acb7a918cb149f72117133ad; no main/live/merge/deploy/retirement. GlobalSGB/oldsourceinventory/scanner/pins/reader/cards/curatedIDs unchanged. One lower route, no optional parallel experiment.
'''
for folder in ['tasks','conversion-windows','proof-obligations','proof-blueprints','research-wiki/retrieval-index']:
    p=Path(folder)/(TASK+'.md');p.write_bytes(p.read_bytes()+status.encode('utf-8'))
    write(RUN/'snapshots'/('BODY-review-'+p.as_posix().replace('/','--')+'.raw'),p.read_bytes())
write(RUN/'proof-obligations-candidate-v1.json',dict(
    source_claim='C1-LOG-UNAVOIDABLE',frozen_targets=16,compiled_frozen_targets=16,
    actual_public_proofs=48,actual_public_definitions=10,
    claimed_progress='Full immutable lower terminal closed locally; not mere additional declarations',
    auxiliary_foundation_growth=32,BODY='pending',
    remaining_required_gates=['BODY source review','public root','Tests','full harness','shadow',
        'shared source-qualified Book mapping','site/pixel/registry','FINAL source review','native acceptance','scoped commit/push/draft PR'],
    chapter1_source_items=16,chapter1_required_proof_total=None,
    other_Chapter1_fullRegret_NoRegret_six_main_gap_obligations='required/open',
    chapter2_complete=False,chapters3_to16='unenumerated',necessary_appendices='required',
    goal_complete=False))
write(RUN/'memory_digest-candidate-v1.md',status.strip())
write(RUN/'body-review-packet-v1.md','''# Mandatory BODY audit: actual guessing lower producer

Reuse distinct /root/source_reviewer, requested GPT-6 Astra/medium/history disclosed/no runtime/human/external attestation. Rehash EVERY fixed row and ALL153 original applicable CONTRACT inputs unchanged. Read COMPLETE48public proof bodies/10definitions (8 frozen +2 same-path loss components), private vector decomposition,16typed canary bodies/2fixtures and instance, actual64closed neutral context/decoder report and proved recursive/nominal bridges. Source printed2–4/PDF14–16 and original v10 pixels/contract remain applicable; recheck all seven slots and anti-anchor against the qualitative source sentence. No source-printed quantitative theorem or sharp coefficient is claimed. Original16headers/rawfingerprints exact, all64actualheaderguards separate from76kernel/64Prop/12definition equality compilation. Native safe-verify is a header/forbidden-token check, not Lean compilation; whole paper pipeline is not single-runtime enforced.

Inspect actual newest-first law, q=(K+1)/(n+2), branch weights including strict positivity and normalized finite vector law using shared distribution/measure. Countmoments/variance/expectation recurrence are produced, not hypothesized. binaryStream reversal/after-end padding/strict-prefix A and exact current last history must generate SAME cumulative loss and empirical-mean best loss. Actual optimum count expression/expected (T-1)/6 plus conditional square≥variance and exact shifted harmonic sum lead to H(T+1)/6 for ANYreal deterministic causal history strategy at positiveT. The randomized terminal retains probabilityseed/per-historymeasurable/pointwise allomega-allhistory[0,1] conditions; actual signed regret bound≤T and measurability yield integrability, finite sum interchange/normalized expectation/fixed-vector witness outside integral. No adversaryseedcoupling/target regret/moment/minimum certificates. Binary labels legal[0,1], real learner outputs; noHP/AS/uniformseed/singleinfinitepath; T0lawtotal but lowerpositiveT. Verify all30actual VALUE reference pairs and complete numeric/causality/deterministic/nontrivial faircoin seeded endpoint canaries.

Full neutral definition f2 is independently recursive, and P is a distinct nominal record. all-exact-types-v1 rfl failed correctly; v2 bridge tactic preparation failed; v3 ACTUALLY proves f2 identity bylistinduction, expectation/measure identities byfunext and same law, and both P fields withpropext. All64 closed Prop equalities and12actual definition equalities then compile. No source/header/neutraldefinition weakening, no asserted aliases/receipt-normalization. All prior failed helper/log/exit versions retained. The original neutral16 contract decoder plus full64decoder are different staged outputs, both history disclosed, only two requisite independent actors used.

BODY acceptance is mathematical candidate review only. Public/Test roots still unchanged; all rootTests/harness/reader/site/FINAL/contribution/native/PR gates pending. After accepted BODY, add exactly public/Test imports and one NEWsource-qualified lower reading card and proof notes/chapter boundary, preserving all original cards/old note math/text/curated IDs/registry old identifiersURLs/scanner/config/pins/globalSGB/sourceinventory/priorPR190 evidence. No generated _site edits. R1–R8 EXACT original CONTRACT reader requirements remain future mandatory. Only C1-LOG-UNAVOIDABLE can eventually close; Chapter1 16sourceitems/prooftotalnull/otherfullRegret/NoRegret/sixunwaived main gaps, Chapter2incomplete/3–16unenumerated/appendicesrequired/GoalACTIVE. ExactOPENunmerged PR190base9425fecb38be60b1acb7a918cb149f72117133ad; no main/live/merge/deploy/retirement.

Write ONLY public-body-review-v1.md and public-body-receipt-v1.json. Receipt actor.task=/root/source_reviewer; verdictaccepted|rejected|accepted-with-explicit-delta; report/report_sha256; reviewed_files EVERYfixedrow+inputmanifest+report; fixed_input_count; required_repairs/required_mathematical_repairs/required_metadata_repairs arrays. Copy original required_reader_corrections R1–R8 EXACT into receipt, still required for FINAL. Review all64 seven-slot source/derived-helper/test mappings and all full proof bodies, and state source delta precisely. No integrated/reader/package/Chapter/Goal acceptance. Return actual raw hashes.
''')
paths=[x['path'] for x in load(RUN/'source-contract-inputs-v2.json')['rows']]
paths += [p.as_posix() for p in sorted(CONTRACT.rglob('*')) if p.is_file()]
paths += [p.as_posix() for p in sorted(RUN.rglob('*')) if p.is_file()]
paths += [PUBLIC.as_posix(),CANARY.as_posix()]
paths=list(dict.fromkeys(paths))
rows=[dict(path=p,sha256=sha(p)) for p in paths]
write(RUN/'body-review-inputs-v1.json',dict(stage='BODY',rows=rows,fixed_input_count=len(rows),
    all153_CONTRACT_inputs_raw_unchanged=True,actual_frozen_target_count=16,
    actual_public_proofs=48,actual_public_definitions=10,named_canary_proofs=16,
    mutable_status_docs_bound_by_immutable_snapshots=True,
    root_Tests_reader_pending=True,source_package_accepted=False,chapter_complete=False,goal_complete=False))
for row in rows:assert sha(row['path'])==row['sha256'],row['path']
fixed()
print('BODY fixed inputs',len(rows),'all direct raw bindings match; mandatory distinct review pending.')
