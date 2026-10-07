from common_reviewed_v1 import *
reviewed_fixed()
b=load(RUN/'body-bindings-v1.json')
assert b['public_sha256']==sha(PUBLIC) and b['canary_sha256']==sha(CANARY)
assert b['named_kernel_checks']==34 and len(b['required_value_pairs'])==19
assert load(RUN/'body-audit-driver-v3-exit.json')['exit_code']==0
blind=load(RUN/'blind-receipt-v1.json');assert blind['actor']['task']=='/root/osd_blind'
for key in ['input','input_manifest','report']:
 row=blind[key];assert sha(RUN/row['path'])==row['sha256_raw_bytes'],key
write(RUN/'actual-blind-bindings-v1.json',dict(neutral_packet_sha256=blind['input']['sha256_raw_bytes'],neutral_inputs_sha256=blind['input_manifest']['sha256_raw_bytes'],decoder_report_sha256=blind['report']['sha256_raw_bytes'],decoder_receipt_sha256=sha(RUN/'blind-receipt-v1.json'),actual_public_closed_proposition_identities=12,whole_scoped_definition_identities=6,canary_type_identities=15,test_fixture_identity=1,decoder_is_reconstruction_not_proof_or_source_acceptance=True,prior_staged_history_disclosed=True,runtime_attested=False))
status='''

## Actual compiled reconciliation candidate

Nine frozen target headers and all scoped definitions remain exact. Actual proofs establish a nonpositive existing limit, ordinary-limit-to-upper implication, iff only with per-comparator finite real convergence, and strict separation for ONE fixed affine stream on [0,1] and constant feasible causal zero learner. Actual prefix sums telescope to -F(T)u; positive cofinal even/odd horizons give -1/0 at comparator1, ruling out an ordinary real limit. Signed coefficients are unbounded in time; this is not squared/bounded losses or meanPredict nonconvergence. Nine source-derived supports are not nine printed theorems. The source ordinary lim display and original shared upper property remain distinct.

Actual focused public and15named canaries passed. Thirty-four named kernel checks use only standard axioms; twelve source-neutral closed Prop identities, fifteen actual canary type identities, six whole scoped context identities and one test fixture identity compile. Twenty-four native header guards and nineteen specified actual compiled VALUE pairs pass; native safe-verify itself does NOT compile Lean. Original blind reconstruction and separate CONTRACT/source-repair reviews retain their distinct authority and R1–R8 obligations. Failed native metadata, retrieval API, universe checks, proof tactics, canary index/tactic and audit-generator attempts remain versioned; no source/type weakening. Requested Astra/medium and reused actor history disclosed, no runtime/human/external attestations.

BODY source review, root/Tests/full harness, own scoped shadow, exact-base contributor, shared source-qualified reader/registry, clean Lean-verified site/pixels, FINAL, native acceptance and draft PR delivery remain pending. Only C1-NOREGRET may close after acceptance. Existing meanPredict_noRegret revalidated as an upper producer only; no unconditional ordinary-limit claim. Full C1 regret/best-minimum and five other main-relative module gaps remain required; C1 source inventory16/proof-total unknown, C2 incomplete, C3–16 unenumerated and necessary appendices required. Total GoalACTIVE; exact OPENdraft/unmerged PR191base1737391d9867a420a9e4b9529d4d90e1bf79c93c; main/live/merge/deploy/retirement unchanged.
'''
for folder in ['tasks','conversion-windows','proof-obligations','proof-blueprints','research-wiki/retrieval-index']:
 p=Path(folder)/(TASK+'.md');p.write_bytes(p.read_bytes()+status.encode('utf8'))
 write(RUN/'snapshots'/('BODY-review-'+p.as_posix().replace('/','--')+'.raw'),p.read_bytes())
write(RUN/'memory_digest-candidate-v1.md',status.strip())
write(RUN/'proof-obligations-candidate-v1.json',dict(source_claim='C1-NOREGRET',frozen_contract_targets=9,compiled_contract_targets=9,claimed_progress='Exact nine reconciliation terminals closed; actual causal constant learner/loss telescoping/separation, not assumed regret certificates or declaration count.',BODY='pending',required_remaining_gates=['BODY source review','shared root','Tests','full harness','own scoped shadow','source-qualified Book/reader registry','exact-base contributor','clean site and pixels','FINAL source review','native acceptance','scoped commit/push/draft PR'],chapter1_source_items=16,chapter1_required_proof_total=None,remaining_Chapter1='Full source regret/best minimum and five other main-relative modules required, not waived',chapter2_complete=False,chapters3_to16='unenumerated',necessary_appendices='required',goal_complete=False))
write(RUN/'body-review-packet-v1.md','''# Mandatory BODY audit: upper no-regret and ordinary limits

Reuse distinct /root/source_reviewer with requested GPT-6 Astra / medium. Prior staged history disclosed; no runtime, human or external attestation. Rehash EVERY fixed input row before and after. Original CONTRACT's73 bindings are preserved, with only five current task metadata originals resolved through exact raw snapshots in contract-review-baseline-resolutions-v1.json. No source/terminal/API/public definition/other-task waiver. Read complete actual public9 proofs/3definitions, existing three proofs and three context definitions,15named canaries/one test fixture, all12 neutral reconstruction/actual compiled Prop and six whole context definition equalities. Original ordinary lim display printed2/PDF14 and pinned PDF/image/text remain separate from proposed reconciliation.

Search for mismatches in all seven semantic slots and inspect the bodies, not only theorem headers. Existing NoRegret is per fixed feasible comparator/perpositiveepsilon eventual signed upper control, no ordinary limit/nonnegative regret/uniform comparator/rate assumption. LimitNoRegret separately requires a finite real limit <=0 for every feasible comparator. Actual sign bridge assumes a supplied limit and contradicts positivity with epsilon a/2. Implication uses real order topology; iff keeps the exact convergence premise with limit values dependent on comparator and permitted below zero. Arbitrary carrier generic bridges consume a supplied trace and are library generalizations, not causal generic algorithm/minimizer existence. Existing meanPredict_noRegret comes from the actual strict-past mean strategy/Theorem1.3, revalidated only for the upper property.

Counterexample is ONE fixed exogenous affine loss stream ell_t(x)=(F(t+1)-F(t))*x, F(T)=T for evenT and0 oddT, V=[0,1], feasible structurally causal learner zero chosen independently of losses/comparator. Actual finite range induction telescopes same losses; R_T(u)=-F(T)u<=0. At comparator1 the positive evenT=2(n+1) normalized values are -1 and positive oddT=2n+1 values0. Actual maps are cofinal and real uniqueness gives nonexistence of ordinary limit; strict separation uses comparator1 feasibility. T0 total real division is harmless to atTop, not the obstruction. Source rounds1..T map to Lean0..T-1. Signed real affine losses have coefficients unbounded in time; this is NOT squared-loss/bounded-loss/meanPredict nonconvergence and does NOT establish a textbook blanket error. First four actual losses at x1 are0,+2,-2,+4; original off-by-one planned canary is retained with explicit repair. Actual linear stream permits limit -u, comparator1 -1. Actual causal mean canary y=0 has normalized regret -7/8 atT2 without ordinary-limit claims.

Nine are derived source-reconciliation lemmas, not printed numbered results. All target raw fingerprints and native normalized hashes independently guarded; all34kernel declarations standard axioms only, actual12neutral closed Prop/15canary type/7whole definition identity compilation,24native header guards and19compiled VALUE pairs. Native safe-verify is not Lean compilation; full workflow is not one runtime-enforced gate. Review all preserved compiler/API/generator/native/canary failures; latest actual focused builds and actual type/kernel compilation control claims. Root/Test imports and reader JSON remain unchanged pending this BODY review.

Keep original exact R1–R8 from stabilized-contract-v1.json in the receipt, still future reader requirements. BODY is mathematical candidate review only; rootTests/fullharness/ownshadow/contributor/sharedreader/site/pixels/FINAL/native/PR pending. Only C1-NOREGRET can close later; C1 inventory16/proof-totalnull/fullbestminimum/five other main gaps/C2incomplete/C3–16unenumerated/appendicesrequired/GoalACTIVE. OPENdraft unmerged PR191 exactbase1737391d9867a420a9e4b9529d4d90e1bf79c93c, no main/live/merge/deploy/retirement.

Write ONLY public-body-review-v1.md and public-body-receipt-v1.json under this RUN. Receipt actor.task=/root/source_reviewer, requested Astra/medium/history/no runtime or human-external attestations; verdict accepted|rejected|accepted-with-explicit-delta; absolute report/report_sha256; reviewed_files EVERYfixedrow plus inputmanifest and report, fixed_input_count; required_repairs/required_mathematical_repairs/required_metadata_repairs arrays. Copy original required_reader_corrections EXACT. Return actual report and receipt raw SHA. Do not edit any other file.
''')
resolutions={x['original']:x for x in load(RUN/'contract-review-baseline-resolutions-v1.json')}
paths=[]
for row in load(RUN/'source-contract-inputs-v1.json')['rows']:
 p=row['path'];h=row['sha256']
 if sha(p)!=h:
  old=resolutions[p];assert sha(old['snapshot'])==h;p=old['snapshot']
 paths.append(Path(p).resolve().as_posix())
paths += [p.resolve().as_posix() for p in sorted(CONTRACT.rglob('*')) if p.is_file()]
paths += [p.resolve().as_posix() for p in sorted(RUN.rglob('*')) if p.is_file()]
paths += [p.resolve().as_posix() for p in [PUBLIC,CANARY,Path('BanditRLProof/OnlineLearningAsymptotic.lean'),Path('BanditRLProof/OnlineLearningRegret.lean'),Path('BanditRLProof/OnlineLearningFTL.lean')]]
paths=list(dict.fromkeys(paths));rows=[dict(path=p,sha256=sha(p)) for p in paths]
write(RUN/'body-review-inputs-v1.json',dict(stage='BODY',rows=rows,fixed_input_count=len(rows),original73_bindings_preserved_with_five_metadata_snapshots=True,frozen_targets=9,source_package_accepted=False,root_Tests_reader_pending=True,chapter_complete=False,goal_complete=False))
for row in rows:assert sha(row['path'])==row['sha256'],row['path']
reviewed_fixed();print('BODY fixed rows',len(rows),'exact raw bindings; mandatory source reviewer pending.')
