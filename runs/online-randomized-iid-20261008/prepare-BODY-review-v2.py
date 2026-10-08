from common_reviewed_v2 import *

headers_fixed(7)
b=load(RUN/'body-bindings-v2.json')
assert b['public_sha256']==sha(PUBLIC) and b['canary_sha256']==sha(CANARY)
assert b['named_kernel_checks']==55 and b['named_canary_proofs']==29
assert load(RUN/'actual-canary-types-fixtures-v3-exit.json')['exit_code']==0
assert load(RUN/'actual-public-types-kernel-v2-exit.json')['exit_code']==0
status='''

## Seven frozen actual causal private-seed terminals: BODY candidate

Actual R001 regrouping produces (seed,past)/current independence from independent WHOLE blocks; actual R002 extracts finite tuples from the whole jointly IID process using iIndepFun.indepFun_finset. R003 proves monotone generated comap. R004 inherits independence for measurable predictions in subordinate pre-reveal information. R005 is an actual jointly measurable seed+strict-history policy. R006 derives ambient measurability/L2/current independence and cumulative expected-fixed excess. R007 instantiates R006 with the actual joint policy trajectory, producing legal histories from countable a.s. support. The same stream and prefix are used. No supplied current independence/stability certificate. Arbitrary measurable private tape may be used at t0, with an empty past.

Keep probability, measurable targets, same-law/joint independence/a.s.unit support. Policy feasibility only on legal unit histories for EVERY seed; general predictions only a.s.feasible. Benchmark is min of expected FIXED loss OUTSIDE integration, reusing actual PR194 minimum. R006 accepts a supplied prediction trace measurable in the subordinate information; R007 supplies the explicit real policy representation. No universal stochastic-kernel representation, completed/augmented-field or AE-factorization theorem. Finite lower producer only, not an unknown-law learning rate, high-probability or asymptotic guarantee. Source rounds1..T=Lean0..T-1; T0 is a disclosed empty extension.

Actual seven public proofs/one definition compile with the exact v2 context/headers. Twenty-nine named canary proofs/nine whole fixtures/two probability proofs/two actual anonymous measurable instances compile: a fair private bit times an INFINITE joint IID target law, same laws/a.s.support/mean1/2/variance1/4, actual legal policy first-private-bit then latest past. Two-round expected-fixed excess1/2, separate subordinate-information/R006 wiring, zero horizon, and a proof current Y0 cannot be measured in private-only information. A four-atom XOR law has X,Y,seed each pair independent but (seed,X) not independent of Y; the whole-seed premise cannot be replaced by pairwise independence. The same off-cube-unbounded policy is covered on legal histories. These are actual endpoint instantiations and falsifying boundaries, not substitutes for general declarations.

Actual 55 selected kernel checks: compiler kinds42theorem/13definition, including probability/measurable class proof values. Standard axioms only, no sorryAx. Seven arbitrary-universe public proof VALUE instantiations, seven draft/neutral Prop identities, three complete benchmark/information definition identities;29 closed canary Prop identities/nine whole fixture identities/two probability types/two actual class identities. Thirty-six native header fences/safe scans and26 actual compiled direct VALUE pairs separately pass. All original failures and exact proof-only repairs retained; audit generator duplicate-definition repair changes no source, public or canary. Safe-verify is not compilation. Seven are derived producer/interface results, not seven printed results or a new rate.

Distinct CONTRACT review accepted-with-explicit-delta; BODY, combined root/Tests/full harness, own shadow, nonvacuous contributor, shared registry/source-qualified readers/site/pixels/FINAL/native/draft PR still separate gates. Original R1-R7 remain future FINAL reader requirements. Universal-kernel/completed-field source coverage and source asymptotic-success equivalence remain unproved/required for full coverage audit. Original16 C1 source items/proof-totalnull/five older main-relative source-module audits unwaived/C1C2open/3-16unenumerated/necessaryappendicesrequired/totalGoalACTIVE. OPENdraft unmerged PR194 exact b08 stack, canonical cleanmain6847; no main/live/merge/deploy/retirement. Distinct staged reused automated actors, requested Astra/medium; no absolute-blind/human/external/runtime setting attestation or single-runtime-enforces-all-workflow claim.
'''
for p in APPEND_METADATA:
    p.write_bytes(p.read_bytes()+status.encode('utf8'))
    write(RUN/'snapshots'/('BODY-current--'+p.as_posix().replace('/','--')+'.raw'),p.read_bytes())
retrieval=Path('research-wiki/retrieval-index')/(TASK+'.md')
write(retrieval,status.strip())
write(RUN/'memory_digest-candidate-v2.md',status.strip())
write(RUN/'30_worker-complete-v2.md',status.strip())
write(RUN/'proof-obligations-candidate-v2.json',dict(contract_version=2,frozen_targets=7,compiled_targets=7,
    remaining_mathematical_terminals=0,source_items_chapter1=16,required_chapter1_proof_total=None,
    BODY='pending',required_gates=['BODY source','combined root','Tests','full harness','own shadow',
        'committed contributor','shared registry/readers','applicable clean site/pixels','FINAL','native acceptance','draft PR'],
    remaining_universal_kernel_completed_information_coverage='unproved; REQUIRED full-source scope audit',
    remaining_source_asymptotic_success='REQUIRED',five_old_main_relative_source_audits='REQUIRED unwaived',
    chapter1_complete=False,chapter2_complete=False,chapters3_to16='unenumerated',necessary_appendices='required',goal_complete=False))
native('candidate-event-v2','lifecycle-event','--session',TASK,'--event','candidate','--payload-json',json.dumps(dict(
    run_id=RUN.name,contract_version=2,body_bindings=(RUN/'body-bindings-v2.json').as_posix(),
    package_accepted=False,chapter_complete=False,goal_complete=False)))
native('canary-failed-trial-v2','trial-log','--task',TASK,'--role','lower','--kind','build','--status','failed',
    '--run-id',RUN.name,'--lean',CANARY,'--attempt-id','PRIVATE-CANARY-V2','--harness','hierarchical',
    '--verifier-evidence',RUN/'canary-XOR-focused-build-v2-exit.json','--progress-class','diagnostic',
    '--error-signature','ENNReal quarter arithmetic residual',
    '--notes','Retrospective actual failed canary attempt; no frozen mathematical statement changes, raw source/log retained.')
native('canary-compiled-trial-v3','trial-log','--task',TASK,'--role','lower','--kind','build','--status','compiled',
    '--run-id',RUN.name,'--lean',CANARY,'--attempt-id','PRIVATE-CANARY-V3','--harness','hierarchical',
    '--verifier-evidence',RUN/'canary-XOR-focused-build-v3-exit.json','--progress-class','compiled-leaf',
    '--notes','Actual nondegenerate infinite-IID/private-seed and pairwise-but-not-joint XOR canaries compiled; exact type/kernel/VALUE audits also pass. BODY/package/chapter pending.')

mutable=[p.as_posix() for p in APPEND_METADATA]+['BanditRLProof.lean','Tests.lean',
    'website/content/readings.json','website/content/highlights.json','website/content/chapters.json',
    'research-wiki/contribution-contracts/online-randomized-iid-20261008.json',
    'research-wiki/retrieval-index/local_lean_declarations.json']
resolutions=[]
paths=[]
for row in load(RUN/'source-review-inputs-v2.json')['rows']:
    p=Path(row['path'])
    if p.as_posix() in mutable:
        snapshot=RUN/'snapshots'/('CONTRACT-reviewed--'+p.as_posix().replace('/','--')+'.raw')
        if not snapshot.exists():
            assert sha(p)==row['sha256'],p
            write(snapshot,p.read_bytes())
        assert sha(snapshot)==row['sha256']
        paths.append(snapshot)
        resolutions.append(dict(live_path=p.as_posix(),snapshot=snapshot.relative_to(ROOT).as_posix(),sha256=row['sha256']))
    else:
        assert sha(p)==row['sha256'],p
        paths.append(p)
write(RUN/'CONTRACT-original-input-resolutions-v2.json',resolutions)
write(RUN/'BODY-review-packet-v2.md','''# Anti-anchored actual BODY audit, private-seed/information IID lower producer

Reuse distinct /root/source_reviewer, requested GPT-6 Astra/medium. Prior staged review history disclosed; no human/external/absolute blindness/runtime setting attestation. Search for mismatch. Rehash every indexed original/fixed/current input before/after, read actual seven frozen v2 public bodies and all29 canary proofs, complete fixtures/probability/class values, actual type/kernel/direct-VALUE evidence and preserved failed-proof/audit repairs. Read exact operative source-statement-fingerprint-v2.json, reader-requirements-v2.json, reviewed-DAG-v2.json, prior CONTRACT report/receipt and source-blind reconstruction. View pinned source printed1-2/PDF13-14 pixels and consult freshly extracted text/cached PDF, exact SHA preserved.

Must derive joint (seed,strict-past)/current independence from seed independent WHOLE stream and jointly IID targets, not pairwise shortcuts or given prediction/current certificate. R001 actual joint-law product associativity; R002 actual finite group IID extraction; R003 actual comap monotonicity; R004 subordinate information; R005 real measurable policy; R006 actual measurability/L2/moment benchmark producer; R007 must instantiate the general information endpoint. Explicit arbitrary-universe full public proof VALUE checks; frozen context/header hashes unchanged. a.s.unit targets and legal-input-only every-seed feasibility, min expectedFIXED outsideE, same prefix, t0 empty-past seed allowed. Distinguish general supplied restricted trace/R006 from explicit policy/R007. No all stochastic kernels, completion/augmentation, AE-factorization, arbitrary future-correlated side information or asymptotic-success/rate claim. Determine precisely what full-source coverage remains REQUIRED; do not rubber-stamp all algorithms.

Actual fair private bit x infinite real-coordinate joint IID target space, variance1/4, first seedBit then strict latest-past policy, off-cube unbounded boundary; two-round expectedfixed excess1/2, independent actual R006/R007 wiring, T0 and currentY0 NOTprivate-information canary. XOR four-atom probability gives all three pairwise independences but seed+past/current fails; all actual compiler checks and class values included.55kernelchecks/42theoremkind13definitionkind,29canaryProps/nineWHOLEfixtures/two probability types/two actual class identities,26compiled VALUEpairs/36native headerguards are separate evidence; native safe scans do not compile. Seven derived results/one definition not seven source statements/new rates.

BODY acceptance is for bounded candidate mathematics ONLY. Original seven R1-R7 remain FUTURE FINAL reader requirements and must be copied unchanged to receipt.required_reader_corrections. Original16/null/oldfive/C1C2open/3-16unenumerated/appendices/GoalACTIVE; source asymptotic-success and unresolved universal-kernel/completed-field coverage audit REQUIRED. Exact OPENdraft unmergedPR194 b08 stacked base, canonicalmain6847; no main/live/merge/deploy/retirement. Combined root/Tests/harness/shadow/contributor/registry/site/pixels/FINAL/native/PR pending; no single runtime enforces every convention.

Original CONTRACT inputs remain immutable via exact raw snapshots where metadata/status may evolve. If accepting BODY, explicitly permit the FOLLOWING later integration ONLY, with versioned raw original snapshots and separate FINAL review: roots each append exactly ONE own import; append own four native status files/new own retrieval card; refresh shared retrieval preserving ALL prior rows; source-qualified ONE new private-seed/information card at online-foundations preserving ALL old cards and fields, exactly seven own proof notes preserving old notes, append own module glob and change only that chapter's completion_blockers/open_gaps to current truthful remaining obligations. Supersede own draft contribution manifest using schema2 with precise assumptions/boundaries, actual evidence, identical source-qualified declarations and pending FINAL gates, preserving draft raw snapshot. These are proposed narrowly scoped metadata permissions, not permission to change frozen statements/definitions, old source modules, old contracts, source16/null inventory or globalSGB. Actual original/final changed bytes must later be checked separately; do not mark reader requirements discharged now.

Write ONLY public-body-review-v2.md and public-body-receipt-v2.json in this RUN. Receipt actor.task=/root/source_reviewer, verdict accepted|accepted-with-explicit-delta|rejected, report path/rawSHA, actual fixed_input_count and reviewed_files ALL indexed rawrows+manifest+report, before_after_raw_hashes_match, required_repairs/required_mathematical_repairs/required_metadata_repairs arrays, required_reader_corrections EXACT originalR1-R7, permitted_future_integration reflecting the precise proposal or blocking objections, explicit remaining source scope. No other edits/state promotions. Return raw hashes.
''')
paths += [p for root in [CONTRACT,RUN] for p in sorted(root.rglob('*')) if p.is_file() and '__pycache__' not in p.parts]
paths += [PUBLIC,CANARY,retrieval]
paths=sorted({p.resolve().as_posix() for p in paths})
rows=[dict(path=p,sha256=sha(p)) for p in paths]
write(RUN/'BODY-review-inputs-v2.json',dict(schema='abrl.review-inputs.v1',phase='BODY',contract_version=2,
    rows=rows,fixed_input_count=len(rows),original_CONTRACT_bindings=1143,
    original_input_resolutions='CONTRACT-original-input-resolutions-v2.json',
    package_accepted=False,chapter_complete=False,goal_complete=False))
headers_fixed(7)
print('BODY immutable inputs:',len(rows),'Mandatory distinct review pending; no combined/reader/FINAL/package acceptance.')
