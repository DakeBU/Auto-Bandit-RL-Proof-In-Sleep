from common_v1 import *

baseline_fixed(mutable=['MANIFEST.md','runs/trials.jsonl','runs/lifecycle_sessions.jsonl'])
assert not PUBLIC.exists() and not CANARY.exists()
blind=load(RUN/'blind-receipt-v1.json')
assert blind['inputs_unchanged']
scope=dict(phase='After favorable CONTRACT only: bounded proving',
    allowed_production_files=[PUBLIC.relative_to(ROOT).as_posix()],
    allowed_test_files=[CANARY.relative_to(ROOT).as_posix()],
    exact_headers=(CONTRACT/'targets-v1.json').as_posix(),
    own_stage_metadata_only='Versioned own RUN/CONTRACT director/architect/worker, exact task suffixes and own native task/session entries; global SGB/readers/root/pins/old module bytes immutable until favorable BODY',
    no_root_reader_or_registry_integration_before_BODY=True,
    terminal='Core actual augmented-field real version producer plus all three original process causal adapters',
    header_mutation_requires_new_contract_version_and_review=True,
    separate_BODY_FINAL_native_delivery_required=True,chapter_complete=False,goal_complete=False)
write(RUN/'contract-future-proof-scope-v1.json',scope)
rows={}
def add(p):
    p=Path(p).resolve();assert p.is_file();rows[p.as_posix()]=dict(path=p.as_posix(),sha256=sha(p))
for folder in [RUN,CONTRACT]:
    for p in folder.rglob('*'):
        if p.is_file() and '__pycache__' not in p.parts:add(p)
for r in load(RUN/'draft-baseline-v1.json')['rows']:add(ROOT/r['path'])
for d in ['tasks','proof-obligations','proof-blueprints','conversion-windows']:add(ROOT/d/(TASK+'.md'))
for p in (ROOT/'research-wiki/retrieval-index').glob('*.json'):add(p)
add(PDF)
for rel in ['Mathlib/MeasureTheory/MeasurableSpace/EventuallyMeasurable.lean',
    'Mathlib/MeasureTheory/MeasurableSpace/CountablyGenerated.lean',
    'Mathlib/MeasureTheory/MeasurableSpace/Embedding.lean',
    'Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean',
    'Mathlib/MeasureTheory/Constructions/Polish/Basic.lean']:add(ROOT/'.lake/packages/mathlib'/rel)
prior=ROOT/'runs/online-ae-causal-20261008'
for name in ['accepted-decision-v2.json','final-reader-review-v2.md','final-reader-receipt-v2.json',
    'post-native-review-v2.md','post-native-receipt-v2.json','delivery-review-v3.md','delivery-receipt-v3.json',
    'actual-kernel-value-audit-v2.json','body-bindings-v1.json']:add(prior/name)
write(RUN/'source-contract-review-inputs-v1.json',dict(phase='draft to stabilized source/statement review; zero new bodies',
    rows=sorted(rows.values(),key=lambda r:r['path']),fixed_input_count=len(rows),
    exact_reader_requirements=load(CONTRACT/'reader-requirements-v1.json'),permitted_future_proof_scope=scope,
    prior_base=BASE,priorPR=198,chapter_complete=False,goal_complete=False))
write(RUN/'source-contract-review-packet-v1.md',
    'Distinct staged anti-anchored source reviewer: independently RAW-hash every index row before/after. Personally read pinned Orabona v10 PDF13/15 and inspect copied actual original PNGs (unchanged cached renders), four exact full Lean headers/neutral decoder/semantic signature/DAG/source intent and actual type/API logs. This CONTRACT has zero new theorem bodies; source acceptance cannot be inferred from type syntax or prior AE proof.\n\n'
    'Search for mismatch: eventuallyMeasurableSpace F (ae ambient_mu) versus completion of mu.trimF; real output/countable coding and measurable inverse regularity versus unsupported arbitrary codomain; no F<=ambient/probability needed in actual core existence. Inspect mixed measurable-space binder semantics of full target. Three actual adapter consumers must obtain an AE version from completed-field measurability, not assume version/current independence. Preserve originalP, whole-stream private seed, jointly independent targets, exact min expected FIXEDloss outside expectation, original AEunit feasibility, single all-time event and T0/no convergence.\n\n'
    'Classify four derived targets explicitly as infrastructure/specializations, not four printed theorems. Precise ambient-null augmentation gap may close after proofs, but general kernels/other completion constructions/source16null/allremainingchapters remain required. Source does not print completed-filtration terminology; record that delta rather than equating labels. Check existing API and source canary plan genuinely completed-measurable but not ordinary pointwise predictable. Whole Goal active, PR198OPENdraftunmerged exact8dcdf base, shared one Lean library, no main/live.\n\n'
    'Return ONLY source-contract-review-v1.md / source-contract-receipt-v1.json, accepted|rejected|accepted-with-explicit-delta, seven slots per target, exact reader requirements and required corrections, actual fixedcount/RAW before-after/reportSHA, blockers and permitted_future_proof_scope copied exactly if favorable. No proof/body/native/publication edits or independent external/human/runtime attestation. Reused distinct automated staged actor/history disclosed; requested Astra/medium.\n')
print('Actual source CONTRACT fixed RAW inputs:',len(rows),'four bodies unproved.',flush=True)
