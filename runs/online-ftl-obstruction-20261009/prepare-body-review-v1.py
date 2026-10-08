from common_canary_v1 import *
s=canary_contract_fixed();a=load(RUN/'compiled-audit-v1.json')
assert sha(PUBLIC)==a['public_sha256'] and sha(CANARY)==a['canary_sha256']
previous=ROOT/'docs/contracts/online-ftl-limit-v1/chapter-one-source-ledger-accepted-v1.json'
ledger=load(previous);assert len(ledger['original16_source_objects'])==16 and ledger['required_proof_leaf_total'] is None
ledger['current_bounded_FTL_obstruction_overlay']=dict(task=TASK,phase='candidate',derived_obligations=4,
    compiled_public_proofs=4,compiled_dyadic_canaries=11,accepted_obligations=0,pending_acceptance=4,
    bounded_same_FTL_obstruction_body_compiled=True,exact_all_comparator_converse_body_compiled=True,
    whole_Chapter1_reconciliation_gate_required=True,chapter_complete=False,goal_complete=False,merged=False,live=False)
write(CONTRACT/'chapter-one-source-ledger-candidate-v1.json',ledger)
write(RUN/'body-bindings-v1.json',dict(public_sha256=sha(PUBLIC),canary_sha256=sha(CANARY),
    frozen_statement_hashes=[t['statement_hash'] for t in s['targets']],
    frozen_canary_statement_hashes=[t['statement_hash'] for t in load(CONTRACT/'canary-targets-v1.json')['targets']],
    source_contract_receipt_sha256=sha(RUN/'source-contract-receipt-v1.json'),
    canary_contract_receipt_sha256=sha(RUN/'canary-contract-receipt-v1.json'),
    reader_proposal_sha256=sha(RUN/'reader-proposal-v1.json'),scope_sha256=sha(RUN/'body-future-integration-scope-v1.json'),
    new_guard_sha256=sha(RUN/'common_body_v2.py'),prior_accepted_ledger_sha256=sha(previous),current_accepted=0,whole_goal_active=True))
gate('integration-guard-syntax-v1',sys.executable,'-B','-X','utf8','-c',
    "from pathlib import Path;p=Path('runs/online-ftl-obstruction-20261009/common_body_v2.py');compile(p.read_text(encoding='utf8'),str(p),'exec');print('Syntax only; no guards/gates executed or integration edits.')")
write(RUN/'body-review-packet-v1.md','Separate anti-anchored BODY review: verify all exact RAWinputs before/after. '
    'Inspect complete actual production four proofs and eleven independently frozen canary bodies, original source p2/p4/p6, distinct decoder reconstruction, proposed correction, and exact reader proposal. '
    'D1 uses actual ordinary limits at feasible0/1, prior fixed-limit iff and algebra to reconstruct ONE empirical-mean limit; eventual prefix feasibility gives feasible limit; reverse conditional producer. No mean-convergence premise in necessity. '
    'D2 well-founded explicit dyadic recursion produces binary support by strong induction. D3 produces children pair sum, high and low EXACT prefix sums, normalized identities, positive actual horizons and both atTop divergence maps; inverse horizon tends0. No assumed count/limit. '
    'D4 SAME stream/actual initial-half strict-history learner gets upper NoRegret and feasible-best/T0 from prior actual producer. Any fixed-zero real ordinary limit forces squaremean limit; compose with both produced diverging horizons and D3, uniqueness gives4/9=1/9 contradiction. Thus no finite-real fixed0 limit and notliteralLimitNoRegret; this does not contradict source4log upper. '
    'Canary actualprefix0,1,1,0/predictionshalf,0,half,two-thirds, bestR0/1/2/3=0,quarter,threequarters,five-sixths and signed fixed0 R3/3=negativeone-sixth. All four public endpoints WHOLE instantiated, C5 iff-derived no feasible mean limit and C8-C11 metric components. '
    'Four WHOLE public Prop VALUE witnesses and28 standard-only axiom outputs;24selected nodes19 directVALUE pairs, coalesced directTYPE_VALUE edges; notfull transitive dependency or sourcecoverage claim. Fifteen native fences/safechecks pass. '
    'Preserved D4v1 actual exit1 implicit-zero elaboration failure, v2 adds explicit realzero constant only; all terminals/context and earlierproofbytes unchanged. No proof weakness repair. '
    'CONTRACT189 andCANARY42 allcurrentRAW preserved; originalbaseline-v2 artifacts immutable. Review new common_body_v2.py exact prospective guard conversion: only oldRAWroot plus approved ONE import addition per root permitted; allotheroriginalguardrows unchanged; exact readerJSON append-only delta against separately frozenRAWbaseline. This is separate explicit authorization, not silent skip/rewrite/claim oldroots remain byte-identical after integration. '
    'Current root/Test/readers/globalindexes unchanged. Favorable BODY authorizes only boundfuture scope/proposal/newguard, notacceptance. Full root/Tests/harness, nonempty committed-HEAD contributor covering newPUBLIC at bothbases, ownshadow/currentcleansite/registry/pixels/FINAL/native/delivery allpending. '
    'Keep pinned ordinary-lim, upperpredicate and correction PROPOSAL distinct; separately review thatactual fourproved derived endpoints support bounded-source reconciliation with exactiff boundary, notsource-wide theoremrewrite. '
    'Original16/null and allprior acceptedledger overlays retained, onlyfourderivedcandidateoverlay added; C1whole reconciliation/otherC1C2/C3-16/appendices required, wholeGoalACTIVE, stackedPR201openunmerged/mainliveunchanged. '
    'Outputs ONLY ownRUN public-body-review-v1.md and public-body-receipt-v1.json: verdict, fixed_input_count, inputs_unchanged/allraw_input_checks(path/before_sha256/after_sha256/unchanged), report_sha256, required_blocking_repairs, pertarget7slots/canaryassessment, '
    'required_reader_corrections EXACT reader-requirements-v1.json, approved_future_exact_scope EXACT body-future-integration-scope-v1.json if favorable, explicit prospective_guard_conversion_review and separate_source_correction_verdict. '
    'Original source pixels freshly inspect or explicitly reuse own personal priorviews withsamecurrentSHA; nohuman/external/absolute-blind/runtimeattestation, distinctreusedactor requestedAstra/medium. No proof/header/root/reader/git/native mutations.')
paths=[]
for folder in [RUN,CONTRACT]:paths += [p for p in folder.rglob('*') if p.is_file() and '__pycache__' not in p.parts]
paths += [PUBLIC,CANARY,PDF,previous,ROOT/'BanditRLProof.lean',ROOT/'Tests.lean']
paths += [ROOT/r['path'] for r in load(RUN/'baseline-v2.json')['rows']]
paths += [ROOT/r['path'] for r in load(RUN/'integration-baseline-v1.json')['rows']]
paths += [ROOT/d/(TASK+'.md') for d in ['tasks','proof-obligations','conversion-windows']]
write(RUN/'body-review-inputs-v1.json',dict(rows=rows(paths),fixed_input_count=len(set(paths)),
    required_reader_corrections=load(CONTRACT/'reader-requirements-v1.json'),approved_future_exact_scope=load(RUN/'body-future-integration-scope-v1.json'),
    package_accepted=False,chapter_complete=False,goal_complete=False))
print('Frozen actual BODY inputs:',len(set(paths)),'four production proofs/11 canaries; integration unchanged.',flush=True)
