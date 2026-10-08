from common_reviewed_v1 import *

headers_fixed(6)
b = load(RUN / 'body-bindings-v1.json')
assert b['public_sha256'] == sha(PUBLIC) and b['canary_sha256'] == sha(CANARY)
assert b['named_kernel_checks'] == 38 and len(b['required_value_pairs']) == 16
blind = load(RUN / 'blind-receipt-v1.json')
for key in ['input', 'input_manifest', 'context', 'report']:
    assert sha(blind[key]['path']) == blind[key]['sha256_raw_bytes']
status = '''

## Six actual compiled square-minimum terminals; BODY candidate

M001 produces actual mean feasibility/minimization on the same finite interval-target prefix; T0 is only an explicit empty-prefix extension without uniqueness. M002 constructs IsLeast, including actual membership and lower bounds, then imports mathlib IsLeast.csInf_eq. The comparator-loss image is generally infinite, not asserted finite; its actual least element is produced, not supplied as a certificate. M003/M004 retain signed same-trace regret and any supplied real prediction without claiming generic causality/feasibility. M005/M006 use the actual first1/2 strict-past meanPredict and existing theorem1.3/refined proofs; source rounds1..T and tail2..T map to rangeT and range(T-1) denominator real t+2. Six are derived producers/representations/adapters, not six printed results or new rate mathematics.

Actual focused six-body/public20canary builds,38 named standard-axiom kernel checks,6 neutral-to-draft and6 draft-to-actual public closed-Prop identities,20 actual canary type identities,6 whole scoped/fixture identities,26 native header guards and16 actual compiler VALUE pairs pass separately. Safe-verify scans headers/tokens and does not compile. Actual canaries produce T0 minimum/regret0 without uniqueness; varying0/1 data has T2 mean1/2/minimum1/2 and positive-horizon unique mean; actual strategy gives first1/2,next0,then1/2 and regrets1/4,3/4. Fixed time-only alternating prediction and matching fixed targets produce signed regret -1/2 atT2, independently of losses/comparator. Nonbinary1/4,3/4 data gives T2 mean1/2/minimum1/8. Actual endpoint calls preserve log and sharp quarter/tail. These are validation instances, not universal theorem substitutes.

Distinct source/type CONTRACT review accepted-with-explicit-delta and decoder only reconstructed. Source BODY, combined root/Tests/full harness, scoped shadow, contributor, shared source-qualified registry/readers/site/pixels, FINAL, native acceptance and draft PR remain pending. Exact original R1-R8 stay future requirements. No min/expectation exchange: printed1-2 minimum of expected fixed loss and causal cumulative IID variance benchmark remain REQUIRED next. Five older main-relative module audits unwaived; original16C1items/proof-totalnull/fullC1open/C2incomplete/C3-16unenumerated/necessaryappendicesrequired/totalGoalACTIVE. Exact OPENdraft/unmerged PR192base2aa08b9e1f5da4d0c7d7dcbe9ddeadd1fbfc34e3 is a stack, not main/live. Requested Astra/medium and prior staged role history disclosed, no absolute-blind/human/external/runtime attestation. No single runtime enforces the whole workflow.
'''
for folder in ['tasks', 'conversion-windows', 'proof-obligations', 'proof-blueprints', 'research-wiki/retrieval-index']:
    p = Path(folder) / (TASK + '.md')
    p.write_bytes(p.read_bytes() + status.encode('utf8'))
    write(RUN / 'snapshots' / ('BODY-review-' + p.as_posix().replace('/', '--') + '.raw'), p.read_bytes())
write(RUN / 'memory_digest-candidate-v1.md', status.strip())
write(RUN / 'proof-obligations-candidate-v1.json', dict(frozen_contract_targets=6, compiled_contract_targets=6,
    progress='Produced the actual attainable square minimum and same-process bound terminals, not just new interfaces.',
    BODY='pending', required_gates=['source BODY', 'combined root', 'Tests', 'full harness', 'own shadow', 'contributor',
        'shared Book registry/readers', 'clean applicable Lean-verified site/pixels', 'FINAL', 'native acceptance', 'draft PR'],
    chapter1_source_items=16, chapter1_required_proof_total=None,
    IID_expected_fixed_benchmark_and_causal_variance='REQUIRED next, distinct from pathwise minimum',
    five_main_relative_modules='REQUIRED unwaived', chapter1_complete=False, chapter2_complete=False,
    chapters3_to16='unenumerated', necessary_appendices='required', goal_complete=False))
write(RUN / 'BODY-review-packet-v1.md', '''# Required anti-anchored BODY audit

Reuse distinct /root/source_reviewer with requested Astra/medium and disclosed prior staged history; not human/external/absolute-blind/runtime attestation. Rehash every BODY input before/after. Preserve original132 CONTRACT raw rows, with only five task-owned mutable stage files resolved to exact snapshots in contract-review-baseline-resolutions-v1.json. No source/type/definition/public/other-task waiver. Read actual six public theorem bodies/one definition and actual shared Mean/FTL/Foundations/Regret dependencies, twenty actual named canaries/two full time-only fixtures, source PDF14–17/printed2–5, actual decoder reconstructions and compiled type/kernel/VALUE/header audits. Search for mismatch rather than confirm.

M001 must PRODUCE feasibility and minimum from actual mean proofs, including explicit T0 extension/no uniqueness. M002 must produce IsLeast membership and lower bounds before csInf_eq, no empty-inf convention/assumed minimizer/replaced benchmark; the image is generally infinite. M003/M004 are signed arbitrary-supplied-trace representation/order generalizations, not causal learners. Both actual performance terminals use source first1/2 strict-past meanPredict and old theorem1.3/refined bodies for the SAME losses and prefix. Preserve positiveT and exact real denominators/ranges. Six derived producers/adapters are not six printed theorems or new rate math.

Audit actual canaries rather than prospective plans: T0zero/no uniqueness, actual varying0/1/nonbinary prefixes/produced minimum, positive old uniqueness, actual first-half past predictor, regrets1/4 and3/4, same time-only fixed prediction/independently fixed matched data negative -1/2 atT2, fixed comparator0/1 order, actual log/refined calls. The signed example is finite pathwise and does not prove expected IID excess-risk negativity or generic learner behavior. Printed1–2 min of EXPECTED FIXED loss and causal cumulative IID variance remain REQUIRED next; never interchange min and expectation. No upper convergence or new general argmin theorem.

Actual38kernel checks,6 neutral->draft+6 draft->actual Prop identities,20 actual canary identities,6 whole definitions,26 native header guards and16 actual VALUE occurrences are independent evidence. Native safe-verify is not Lean compilation. Prior CONTRACT accepts types/source only; BODY accepts actual candidate mathematics only. Original R1-R8 must be copied EXACT as future reader requirements, not discharged; combined root/Tests/full harness/ownshadow/contributor/sharedregistry/readers/site/pixels/FINAL/native/PR pending. Original16C1items/proof-totalnull, five main-relative source modules, fullC1open/C2incomplete/3–16unenumerated/necessaryappendices and totalGoalACTIVE. Exact OPENdraft unmergedPR192 base2aa08b9e1f5da4d0c7d7dcbe9ddeadd1fbfc34e3; no main/live/merge/deploy/retirement.

Write ONLY public-body-review-v1.md and public-body-receipt-v1.json in RUN. Receipt actor.task=/root/source_reviewer, verdict accepted|accepted-with-explicit-delta|rejected, report/report_sha256, all fixed input rows plus manifest+report, fixed_input_count, required_repairs/required_mathematical_repairs/required_metadata_repairs arrays, exact original required_reader_corrections. Return raw report and receipt hashes. Do not modify other files.
''')
resolutions = {x['original']: x for x in load(RUN / 'contract-review-baseline-resolutions-v1.json')}
paths = []
for row in load(RUN / 'source-contract-inputs-v1.json')['rows']:
    p, expected = row['path'], row['sha256']
    if sha(p) != expected:
        resolution = resolutions[p]
        assert sha(resolution['snapshot']) == expected
        p = resolution['snapshot']
    paths.append(Path(p).resolve().as_posix())
paths += [p.resolve().as_posix() for root in [CONTRACT, RUN] for p in sorted(root.rglob('*'))
    if p.is_file() and '__pycache__' not in p.parts]
paths += [p.resolve().as_posix() for p in [PUBLIC, CANARY]]
paths = list(dict.fromkeys(paths))
rows = [dict(path=p, sha256=sha(p)) for p in paths]
write(RUN / 'BODY-review-inputs-v1.json', dict(stage='BODY', rows=rows, fixed_input_count=len(rows),
    original_CONTRACT_bindings_preserved=132, exact_task_metadata_snapshots=5,
    package_accepted=False, chapter_complete=False, goal_complete=False))
for row in rows: assert sha(row['path']) == row['sha256'], row['path']
headers_fixed(6)
print('BODY input rows', len(rows), '; actual candidate math frozen; mandatory review pending.')
