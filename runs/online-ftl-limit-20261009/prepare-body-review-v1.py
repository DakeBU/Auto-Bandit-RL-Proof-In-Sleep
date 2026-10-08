from common_canary_v1 import *
s=canary_contract_fixed()
a=load(RUN/'compiled-audit-v1.json')
assert sha(PUBLIC)==a['public_sha256'] and sha(CANARY)==a['canary_sha256']
ledger=load(ROOT/'docs/contracts/online-kernel-causal-v1/chapter-one-source-ledger-accepted-v1.json')
assert len(ledger['original16_source_objects'])==16 and ledger['required_proof_leaf_total'] is None
ledger['current_FTL_limit_hinge_overlay']=dict(task=TASK,phase='candidate',derived_obligations=5,
    compiled_public_proofs=5,compiled_binary_canaries=12,accepted_obligations=0,pending_acceptance=5,
    bounded_oscillating_same_FTL_obstruction_required=True,exact_all_comparator_converse_required=True,
    chapter_complete=False,goal_complete=False,merged=False,live=False)
write(CONTRACT/'chapter-one-source-ledger-candidate-v1.json',ledger)
write(RUN/'body-bindings-v1.json',dict(public_sha256=sha(PUBLIC),canary_sha256=sha(CANARY),
    frozen_statement_hashes=[t['statement_hash'] for t in s['targets']],
    frozen_canary_statement_hashes=[t['statement_hash'] for t in load(CONTRACT/'canary-targets-v1.json')['targets']],
    source_contract_receipt_sha256=sha(RUN/'source-contract-receipt-v1.json'),
    canary_contract_receipt_sha256=sha(RUN/'canary-contract-receipt-v1.json'),
    reader_proposal_sha256=sha(RUN/'reader-proposal-v1.json'),scope_sha256=sha(RUN/'body-future-integration-scope-v1.json'),
    current_accepted=0,whole_goal_active=True))
write(RUN/'body-review-packet-v1.md','Separate anti-anchored staged BODY review. Audit all fixed RAWinputs in body-review-inputs-v1.json before/after; inspect actual complete production5 bodies and12 public binary canary bodies. '
    'Original48 source-contract fields remain unchanged except allowed OWN taskappendices (currently unchanged), snapshot/strict guards recorded; original24 canarycontract allRAW stillunchanged. '
    'Compare source v10 printed2/PDF14 ordinary-limit display, p4/PDF16 actualFTL Theorem1.3 4log upper, p6/PDF18 sublinear conclusion; source and both neutralreconstructions, seven slots each. '
    'F1 nonnegative actualFTL loss gap is produced via oldleader prefixminimum induction, no boundoracle; arbitraryreal stream/T0 allowed but no gamefeasibility claim outsideunit. '
    'F2 exactminusT*square comparator identity allrealu/y/T. F3 true intervalminimum identification with sourceactualupper and F1lower -> best/T ordinary0. '
    'F4 derives eventualpositiveT cancellation and both-direction ordinarylimit criterion fromsameactualFTL; no unconditional existence. F5 explicit empiricalMean convergence implies allrealcomparator negative-square limits and literalLimitNoRegret forunitcomps, notsourceunconditionalclaim. '
    'Canary actualbinary0/1counts floorT/2 produce mean→half, actualpredictions half/0/half/third, actualbestR0=0,R1=quarter,R2=threequarters. All5public endpoints instantiated; fixedu0 ordinarynegativequarter and uhalf0 fromsameprocess; no suppliedregret or meanoracle. '
    'Five whole public proposition VALUE witnesses,29 unique #printaxioms onlystandard,24 selectedcompiled nodes2676coalesceddirect TYPE_VALUEedges16requireddirectVALUEpairs,17nativefences/safeverify. Notfulltransitivegraph/coverage or independent sourcevalidation. '
    'F1 focusedcompile0 but first fence safeverify1 because explanatoryprose absentliteral sourcefile; originalinvocation/fence/log retained, correctedfencev2 exactquantifierstrings0, body/header/sourceassumptions unchanged. '
    'Originalpypdfium2 importfailure retained; Popplerexistingfallback actually renderedsource3pages, no environment/toolchain install. Review these as evidence-configuration repairs, not silent theorem weakening. '
    'Review bound reader-proposal and exact future integration scope: onecard/fivenotes/currentrootTestimports/moduleownership, oldrecords/status/URLs preserved; newownschema2manifest/review records only. '
    'No currentroot/site edits yet; favorable BODY onlyauthorizes this exactintegration, fullroot/Tests/harness/site/FINAL/native/delivery stillpending. Globalretrieval sixindexes currentlyunchanged, owned retrieval only. '
    'Original16/null unknownproof total and previousacceptedoverlays preserved; bounded oscillating actualFTL sourceobstruction/exactall-comparatorconverse remain REQUIRED; otherC1/C2/C3-16/appendices required, wholeGoalACTIVE. '
    'Do notclosepackage/chapter/Goal orclaimmain/live. VieworiginalsourcePNG14/16/18 (or explicitlysamecurrentSHA previouslyviewed) andreviewnegativequartercanary sign. '
    'Outputs ONLY public-body-review-v1.md and public-body-receipt-v1.json inthisRUN: verdict accepted|rejected|accepted-with-explicit-delta, fixed_input_count/inputs_unchanged/allraw_input_checks/report_sha256, required_blocking_repairs, '
    'per-target7slots/canary assessment, required_reader_corrections EXACT reader-requirements-v1.json, approved_future_exact_scope EXACT body-future-integration-scope-v1.json ifapproved. '
    'Distinct reused actor, requested GPT-6 Astra/medium notruntimeattested; no human/external/absolute-blind claims. No input/proof/root/site/git mutations or broadgate work.')
paths=[]
for folder in [RUN,CONTRACT]:
    paths += [p for p in folder.rglob('*') if p.is_file() and '__pycache__' not in p.parts]
paths += [PUBLIC,CANARY]
paths += [ROOT/r['path'] for r in load(RUN/'baseline-v1.json')['rows'] if 'OnlineLearning' in r['path'] or 'OnlineSquareMinimum' in r['path'] or 'OnlineNoRegretSemantics' in r['path']]
paths += [ROOT/d/(TASK+'.md') for d in ['tasks','proof-obligations','conversion-windows']]
write(RUN/'body-review-inputs-v1.json',dict(rows=rows(paths),fixed_input_count=len(set(paths)),
    required_reader_corrections=load(CONTRACT/'reader-requirements-v1.json'),
    approved_future_exact_scope=load(RUN/'body-future-integration-scope-v1.json'),package_accepted=False,chapter_complete=False,goal_complete=False))
print('Frozen BODY inputs',len(set(paths)),'5 actualproofs12canaries; root/site untouched.',flush=True)
