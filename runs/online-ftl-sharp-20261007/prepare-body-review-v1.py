from common_v1 import *
fixed(proving=True)
b=load(RUN/'body-bindings-v1.json');assert b['new_public_math']==2 and b['named_kernel_checks']==15 and b['exact_proposition_identities']==13
source=load(RUN/'source-contract-repair-receipt-v1.json');original=load(RUN/'source-contract-receipt-v1.json')
assert source['verdict'] in ['accepted','accepted-with-explicit-delta'] and original['verdict']=='rejected'
assert source['required_reader_corrections']==original['required_reader_corrections']
seen={x['path']:x['sha256'] for x in source['reviewed_files']};prior=load(RUN/'source-contract-inputs-v3.json')['rows']
for x in prior:assert seen[x['path']]==x['sha256']==sha(x['path']),x['path']
resolution=load(RUN/'CONTRACT-reviewed-snapshot-resolution-v3.json')['rows']
for x in load(RUN/'source-contract-inputs-v2.json')['rows']:
 mapping={a['original_live_path']:a['immutable_snapshot'] for a in resolution}
 assert sha(mapping.get(x['path'],x['path']))==x['sha256']
mutable=['Tests.lean','tasks/'+TASK+'.md','conversion-windows/'+TASK+'.md','proof-obligations/'+TASK+'.md','research-wiki/retrieval-index/'+TASK+'.md','proof-blueprints/'+TASK+'.md']
mapping=[]
for p in mutable:
 dest=RUN/'snapshots'/('BODY-reviewed-'+p.replace('/','--')+'.raw');write(dest,Path(p).read_bytes())
 mapping.append(dict(original_live_path=p,reviewed_sha256=sha(p),immutable_snapshot=dest.as_posix(),intended_future_edit='Exactly one new Tests import' if p=='Tests.lean' else 'Own lifecycle/obligations/retrieval metadata'))
write(RUN/'BODY-reviewed-snapshot-resolution-v1.json',dict(rows=mapping,actual_public_bodies_frozen_live=True,current_Tests_root_before_owned_import=True))
write(RUN/'body-review-packet-v1.md','''# Distinct anti-anchored BODY review: FTL exact proof tail

Requested GPT-6 Astra / medium. Reuse required /root/source_reviewer, disclose staged prior history; not human/external/runtime attestation. Read all current body-review-inputs-v1.json rows and rehash EACH. Original rejected CONTRACT stays rejected, distinct repaired CONTRACT accepted M1/E1/E2/M2. Its243 fixed rows remain exact immutable; original229 rows remain exact via CONTRACT snapshot mapping (not falsely unchanged live whole PUBLIC). Read source PDF actual cached pages16/17/18 and source pixel/text evidence; accepted ledger16 required source items plus required general initialization/streaming/W-V/logunavoidable subobligations, proof totals null.

Inspect COMPLETE actual five retained proofs/one definition and BOTH real new source proofs, six named validation proof bodies/one test sequence. Exact N01–N13 proposition identities and actual context a/b/c identities compiled;15 names/axioms (standard propext/Classical.choice/Quot.sound or none),13 full native fences. ACTUAL compiled selected15 nodes=13proofs+2defs, nine PRESPECIFIED proof VALUE pairs from contract, not type annotations/teaching links. All original five theorem bodies and predictor bytes are exact original prefix. New frozen mathematical headers unchanged. Initial proof uses ONLY y0 interval, true predictor1/2 and one-target mean; no future condition. Refined uses actual produced feasible prefix empiricalMean_mem and global empiricalMean_minimizes to instantiate Be-the-Leader on[0,1]; auxiliary hindsight includes current target, causal prediction strict past. Subtract actual loss sums, split stability sum with sum_range_succ' shifted tail PLUS first, new quarter first, unchanged old4/(t+1) later. Exact range(T-1) realdenominators t+2, positive T, no zero-horizon claim or desired regret/stability/argmin certificate input. Source best fixed min over interval represented by produced feasible globally minimizing SAME final mean. Two unnumbered performance proof statements printed5/PDF17, not renumbered Theorem1.3 or general-init bound. Existing theorem_1_3 unchanged.

Actual named canaries: endpoints both quarter and public initial calls; midpointzero strictquarter; outside2 yields9/4>quarter (not source-admissible/theorem call); horizon1 actualquarter and public refined emptytail; y0=0,y1=1 actual regret3/4 with public refined RHS9/4; strict-prefix perturbation output unchanged while current targets differ via actual old prefix theorem. Six tests/one testdef VALIDATION only. Source proof bodies compiled without any proof repair; actual pre-proof metadata/ledger/path/binding failures and TWO actual initial gate invocation failures (--contract unsupported, role lean-worker unsupported) preserved, corrected documented capture/output/hash/safe-verify and lower/build schema; no mathematical edit/waiver.

N01–N13 each seven slots against actual source and neutral decoder. Keep EXACT original R1–R8 reader requirements from original source-contract-receipt-v1.json in receipt; pending current reader/FINAL. Reader untouched, Tests root before newimport; own Tests/task/status reviewed snapshots make allowed future exact import/statusupdates explicit. Actual public/canary proof bodies now frozen live and must not change during integration. Future bounded old FTL card/public note plus2new sourcecards/notes, preserve all otherBookmath/IDs/oldcards/notes/moduleglobs. No combined root/Tests/fullharness/site/pixels/FINAL/native/PR done yet. Exact stack PR1870fc48... unmerged, not main. Main-relative nine Chapter1 contribution gaps remain unwaived until actual check (ownFTL may resolve, eight others remain); Foundation prior unchanged proof does not resolve its gap. Chapter1 open required subobligations, Chapter2null,3–16unenumerated/requiredappendices/ACTIVEGoal. BODY is bounded recommendation only.

Write ONLY public-body-review-v1.md and public-body-receipt-v1.json in this RUN. Receipt actor.task=/root/source_reviewer, verdict accepted|rejected|accepted-with-explicit-delta, report/report_sha256; reviewed_files EACH fixed row+actual report, fixed_input_count; required_repairs/required_mathematical_repairs/required_metadata_repairs arrays; required_reader_corrections EXACT original8 objects unchanged; N01–N13 seven-slot and real proof/15nodes9VALUE evidence. Return real hashes. No chapter/Goal/main/live/latergate acceptance.
''')
resolve={x['original_live_path']:x['immutable_snapshot'] for x in mapping}
paths=[x['path'] for x in prior]+[p.as_posix() for p in sorted(RUN.rglob('*')) if p.is_file()]+[p.as_posix() for p in sorted(CONTRACT.rglob('*')) if p.is_file()]+[PUBLIC.as_posix(),CANARY.as_posix()]
paths=list(dict.fromkeys(resolve.get(p,p) for p in paths))
write(RUN/'body-review-inputs-v1.json',dict(stage='BODY',rows=[dict(path=p,sha256=sha(p)) for p in paths],fixed_input_count=len(paths),repaired_CONTRACT243_rows_unchanged=True,original_rejected_CONTRACT229_rows_match_via_immutable_snapshot_resolution=True,actual_public_and_named_test_bodies_bound=True,source_package_accepted=False,chapter_complete=False,goal_complete=False))
print('Actual BODY fixed rows',len(paths),'15names13exacttypes9VALUE; distinct BODY pending.')
