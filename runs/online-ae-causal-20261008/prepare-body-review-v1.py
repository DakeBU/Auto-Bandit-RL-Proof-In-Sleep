from common_proving_v1 import *

s=proving_fixed()
a=load(RUN/'actual-kernel-value-audit-v2.json')
canary=ROOT/'Tests/OnlineGuessingAECausalCanary.lean'
assert a['public_source_sha256']==sha(PUBLIC) and a['canary_sha256']==sha(canary)
assert a['three_whole_public_type_VALUE_checks'] and not a['sorryAx']
witnesses=[]
for label,snapshot,module in [
    ('leaf-L1-focused-v1','leaf-L1-attempt-v1.lean.raw','BanditRLProof.OnlineGuessingAECausal'),
    ('leaf-L2-focused-v2','leaf-L2-attempt-v2.lean.raw','BanditRLProof.OnlineGuessingAECausal'),
    ('leaf-L3-focused-v1','leaf-L3-attempt-v1.lean.raw','BanditRLProof.OnlineGuessingAECausal'),
    ('canary-focused-v2','canary-attempt-v2.lean.raw','Tests.OnlineGuessingAECausalCanary')]:
    r=load(RUN/(label+'-exit.json'))
    log=(RUN/(label+'.log')).read_text(encoding='utf8')
    assert r['actual_exit']==0 and r['log_sha256']==sha(RUN/(label+'.log'))
    built=[line for line in log.splitlines() if 'Built '+module in line]
    assert built, label
    witnesses.append(dict(receipt=label+'-exit.json',actual_Built_lines=built,
        snapshot=snapshot,snapshot_sha256=sha(RUN/snapshot)))
artifacts=[]
for module in ['BanditRLProof/OnlineGuessingAECausal','Tests/OnlineGuessingAECausalCanary']:
    p=ROOT/'.lake/build/lib/lean'/(module+'.olean')
    assert p.is_file() and p.stat().st_size>0
    artifacts.append(dict(path=p.as_posix(),bytes=p.stat().st_size,sha256=sha(p)))
write(RUN/'actual-focused-build-witnesses-v1.json',dict(
    actual_Built_witnesses=witnesses,current_nonempty_oleans=artifacts,
    current_public_source_sha256=sha(PUBLIC),current_canary_source_sha256=sha(canary),
    latest_complete_public_source_snapshot='leaf-L3-attempt-v1.lean.raw',
    whole_type_VALUE_check_receipt='whole-public-types-axioms-v1-exit.json',
    not_an_exit_zero_only_compilation_claim=True,semantic_or_combined_acceptance=False))

native('canary-failed-trial-v1','trial-log','--task',TASK,'--role','lower','--kind','build',
    '--status','failed','--run-id',RUN.name,'--lean',canary.relative_to(ROOT).as_posix(),
    '--attempt-id','AE-CANARY-V1','--progress-class','diagnostic',
    '--verifier-evidence',RUN/'canary-focused-v1-exit.json',
    '--error-signature','Prod.ext rfl unified the whole seed/history pair prematurely',
    '--notes','Actual failed test proof retained; one proof-local constructor application repair, unchanged public headers and test conclusion.')
native('canary-compiled-trial-v2','trial-log','--task',TASK,'--role','lower','--kind','build',
    '--status','compiled','--run-id',RUN.name,'--lean',canary.relative_to(ROOT).as_posix(),
    '--attempt-id','AE-CANARY-V2','--progress-class','compiled-leaf',
    '--obligations-before','3','--obligations-after','3',
    '--verifier-evidence',RUN/'actual-kernel-value-audit-v2.json',
    '--target-fingerprint',s['targets_sha256'],
    '--notes','Fourteen actual named AE-only test proofs, one test definition; original process not pointwise predictable or everywhere unit yet AE equal to a seed-only causal predictor. Positive variance and original-process two-round excess1/2. BODY/combined/readers/FINAL/native pending.')

write(RUN/'body-bindings-v1.json',dict(
    public_sha256=sha(PUBLIC),canary_sha256=sha(canary),
    targets_sha256=s['targets_sha256'],headers_sha256=s['headers_sha256'],
    CONTRACT_receipt_sha256=s['receipt_sha256'],CONTRACT_report_sha256=s['report_sha256'],
    actual_audit_sha256=sha(RUN/'actual-kernel-value-audit-v2.json'),
    actual_new_public_proofs=3,actual_new_test_proofs=14,test_definitions=1,
    remaining_local_source_obligations=3,BODY_accepted=False,chapter_complete=False,goal_complete=False))
status=('Three frozen derived AE causal bodies compiled with actual Built-module witnesses, full public-type proofVALUE instantiations, 42 named standard-axiom outputs and 39 actual compiled graph nodes/2136 TYPE_VALUE occurrences/12 required direct VALUE pairs. '
    'One selected law-relative policy family is globally unit-valued and agrees with the same original process on one all-time AE event. L2 derives original current independence from the actual whole-stream independent private seed and strict past, without bounds or same-law assumptions. '
    'L3 uses original predictions on both sides for every natural horizon, including T0, against minimum of expected fixed unit-comparator loss outside expectation. Population mean is analysis-only. '
    'Actual AE-only canary is not pointwise strict-past measurable and not everywhere unit; off-law current2 branch is nonempty but null. Same independently random private seed/infinite IID targets have positive variance1/4 and two-round original-process expected excess1/2. '
    'L2 first focused proof failed and was repaired only by explicit ambient measurable instance. Canary first focused proof failed and Prod.ext application was repaired locally. Native safe-verify first failed because helper supplied prose as a literal header assumption; current v2 uses actual unchanged header premises. All failures retained. '
    'Three locally compiled bodies do not yet close three accepted source obligations: BODY, combined root/Tests/full harness, exact reader/registry/site pixels, FINAL/native and scoped draft delivery remain. '
    'These are three derived targets, not three source-printed results. Original16 source objects and unknown null proof total remain. General completed-information augmentation, full stochastic-kernel causal representation, remaining C1/C2/C3-16/required appendices remain required. No whole chapter/Goal, convergence, executable unknown-law algorithm, off-null original equality or main/live claim. PR197 stacked exactbase OPEN/unmerged; Goal active.')
write(RUN/'33_lower-body-candidate-v1.md',status)
write(RUN/'memory-digest-candidate-v1.md',status)
write(RUN/'proof-obligations-candidate-v1.json',dict(
    contract_version=1,new_public_proofs=3,new_test_proofs=14,test_definitions=1,
    accepted_local_obligations=0,remaining_local_obligations=3,
    focused_kernel_VALUE_fences='actual passed',BODY='pending',
    remaining_gates=['BODY','combinedroot/Tests/fullharness','stacked AND main contributor',
        'ownshadow/globalSGBunchanged','sharedregistry/readers/site/pixels','FINAL','native acceptance','scoped draft PR'],
    original_source_objects=16,required_C1_proof_total=None,chapter_complete=False,goal_complete=False))
native('candidate-event-v1','lifecycle-event','--session',TASK,'--event','candidate',
    '--payload-json',json.dumps(dict(contract_version=1,run_id=RUN.name,
        body_bindings=(RUN/'body-bindings-v1.json').as_posix(),actual_new_proofs=3,
        source_obligations_pending=3,chapter_complete=False,goal_complete=False)))
write(RUN/'body-future-integration-scope-v1.json',dict(
    immutable_math=[PUBLIC.relative_to(ROOT).as_posix(),canary.relative_to(ROOT).as_posix()],
    allowed_future_changes=dict(
        public_root='append exactly import BanditRLProof.OnlineGuessingAECausal; preserve baseline bytes',
        Tests='append exactly import Tests.OnlineGuessingAECausalCanary; preserve baseline bytes',
        readers='one source-qualified own card and three exact new declaration notes; own precise remaining-boundary text. Preserve every old card/note/ID/link/status and original16/null/fullcompletion/kernel requirements.',
        manifest='own schema2 with exact changed public/root/Test/readers scope and actual reviewed three targets; no unrelated blanket coverage',
        registry='add actual three public declarations to same shared registry, preserve all old declaration IDs/URLs/headers',
        native='own task metadata/frontier/trial/memory rows only; append-only global journals and original active SGB frontier unchanged',
        own_RUN_contract='new scoped evidence/status files only, preserve all frozen source/target/receipt/raw inputs'),
    receipt_bound_mutation_resolution='stabilized-contract-v1.json binds exact immutable snapshots for append-only mutable original reviewed journals; current BODY index hashes current live values separately',
    R1_R6=load(RUN/'source-contract-receipt-v1.json')['required_reader_corrections'],
    chapter_complete=False,goal_complete=False))
write(RUN/'body-review-packet-v1.md',
    'Distinct anti-anchored BODY audit of three exact frozen AE causal statements and ACTUAL public proofs, 14 own named test proofs and one definition. Read current whole public/canary bodies, all successful and failed raw attempts/compile outputs, actual full-type proofVALUE checks/axioms/compiled TYPE_VALUE graph, 12 direct required VALUE pairs and native exact-premise fences. '
    'All original118 CONTRACT rows are separately receipt-bound; only own append-only journals differ and immutable prefix snapshots are bound by stabilized-contract-v1. Current BODY inputs carry current RAW hashes; do not assert current live hashes equal historical receipt hashes. '
    'Reinspect original source PDF13/15 pixels, same exact cached PDF digest and scope-qualified source intent plus distinct decoder and CONTRACT receipt. These are THREE DERIVED targets, not three printed results. '
    'Check actual one-family/one-all-time-AE-event factorization/clipping and no ambient measurable/standard-Borel Seed premise in L1; ambient-instance L2 repair preserves all original assumptions; joint target plus whole-stream seed independence genuinely produces original current independence. L3 original-process finite cumulative exact identity and nonnegativity uses attained minimum of expected fixed unit loss outside expectation, population mean only analysis, every naturalT/T0. '
    'Inspect actual AE-only fixture: nonempty null current2 branch makes original predictor not pointwise predictable nor everywhere unit, yet AE equals same random private seed predictor; independently random seed/infiniteIID positivevariance1/4 and exact two-round excess1/2. Do not substitute ordinary predictable inputs or an assumed loss/independence consumer. '
    'Review all preserved L2/canary/helper failures and repairs; no public header mutation. Assess body-future-integration-scope-v1 exact permitted root/Test/reader/manifest/registry/native changes after favorable BODY; frozen public/canary bytes immutable thereafter. Copy original R1-R6 verbatim into receipt and keep future obligations pending. '
    'BODY cannot accept unrun combined/site/FINAL/native/delivery gates or whole chapter/Goal. Completion/kernel/C1/C2/C3-16/appendices remain required, original16/null total unchanged. '
    'Write ONLY public-body-review-v1.md and public-body-receipt-v1.json here. Independently hash every indexed input before/after, list exact count and reviewed hashes, reportSHA, seven slots and actual-body/canary/API findings, verdict accepted|accepted-with-explicit-delta|rejected, required_blocking_repairs, reader requirements and approved_future_exact_scope. Do not edit reviewed inputs. '
    'Reuse disclosed distinct staged automated reviewer, GPT6Astra/medium requested, no runtime attestation/absolute blindness/externalhuman claim. User approved scoped draft delivery, no merge/deploy.')

paths=[Path(r['path']) for r in load(RUN/'source-contract-review-inputs-v1.json')['rows']]
paths += [PUBLIC,canary,ROOT/'Tests/OnlineGuessingRandomizedIIDCanary.lean',ROOT/'Tests/OnlineGuessingIIDSuccessCanary.lean']
paths += [p for p in RUN.rglob('*') if p.is_file() and '__pycache__' not in p.parts]
paths += list(CONTRACT.rglob('*'))
paths=list(dict.fromkeys(p.resolve() for p in paths if p.is_file()))
write(RUN/'body-review-inputs-v1.json',dict(schema='abrl.review-inputs.v1',phase='BODY-v1',
    rows=[dict(path=p.as_posix(),sha256=sha(p)) for p in paths],fixed_input_count=len(paths),
    allowed_writes=['public-body-review-v1.md','public-body-receipt-v1.json'],
    source_obligations_pending=3,new_public_proofs=3,chapter_complete=False,goal_complete=False))
proving_fixed()
print('Prepared actual BODY review fixed RAW inputs:',len(paths),flush=True)
